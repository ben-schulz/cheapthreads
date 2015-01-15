module CT.Compiler.Codegen where
--module CT.Compiler.Codegen (codegen) where

import CT.Syntax
import CT.Compiler.ThreeAddressCode
import CT.Compiler.CM
import Data.List
import Data.Maybe
import Data.Either
import Control.Monad
import System.IO.Unsafe

------------------------
------------------------
-- Top-level function --
------------------------
------------------------

codegen :: CtsProg -> TacProg
codegen prog = runCM phi initSrcPos initFunEnv initMonadEnv initMonadStateEnv initBindEnv initDTEnv initLabelCount initKappa
          where initSrcPos        = CtsSrcPos "<undefined>" 0 0
                initFunEnv        = []
                initMonadEnv      = []
                initMonadStateEnv = []
                initBindEnv       = []
                initDTEnv         = []
                initLabelCount    = 0
                initKappa         = Nothing
                
                phi = liftM TacProg $ trProg prog

--------------
--------------
-- Programs --
--------------
--------------

mkLayerNPMs :: CtsIdent -> CtsMonadLayer -> [MonadNPM]
mkLayerNPMs n (CtsResumptionLayer b) = [MonadStep { monadStepBaseMonad = b, monadStepResultMonad = n }]
mkLayerNPMs n (CtsStateLayer (TyADT "Heap") sn) = [MonadReadHeap { monadReadHeapMonad = n, monadReadHeapName = sn },
                                                   MonadStoreHeap { monadStoreHeapMonad = n, monadStoreHeapName = sn }]
mkLayerNPMs n (CtsStateLayer ty sn)  = [MonadGet { monadGetMonad = n, monadGetStateName = sn, monadGetStateType = ty },
                                        MonadPut { monadPutMonad = n, monadPutStateName = sn, monadPutStateType = ty }]
mkLayerNPMs n (CtsReactiveLayer req rsp b) = [MonadStep { monadStepBaseMonad = b, monadStepResultMonad = n },
                                              MonadGetreq { monadGetreqMonad = n, monadGetreqResultMonad = b, monadGetreqReqType = TyADT req },
                                              MonadPutrsp { monadPutrspMonad = n, monadPutrspResultMonad = b, monadPutrspRspType = TyADT rsp },
                                              MonadIsDone { monadIsDoneMonad = n, monadIsDoneResultMonad = b },
                                              MonadSignal { monadSignalMonad = n, monadSignalReqType = TyADT req, monadSignalRspType = TyADT rsp }]

mkMonadNPMs :: CtsDecl -> [MonadNPM]
mkMonadNPMs (CtsMonadDecl _ n ls) = concatMap (mkLayerNPMs n) ls

npmName :: MonadNPM -> CtsIdent
npmName (MonadStep { monadStepBaseMonad = b, monadStepResultMonad = n }) = "step" ++ n
npmName (MonadGet { monadGetMonad = m, monadGetStateName = n })          = "get" ++ n ++ m
npmName (MonadPut { monadPutMonad = m, monadPutStateName = n })          = "put" ++ n ++ m
npmName (MonadReadHeap { monadReadHeapMonad = m, monadReadHeapName = n }) = "read" ++ n ++ m
npmName (MonadStoreHeap { monadStoreHeapMonad = m, monadStoreHeapName = n }) = "store" ++ n ++ m
npmName (MonadGetreq { monadGetreqMonad = m })                           = "getreq" ++ m
npmName (MonadPutrsp { monadPutrspMonad = m })                           = "putrsp" ++ m
npmName (MonadIsDone { monadIsDoneMonad = m })                           = "isDone" ++ m
npmName (MonadSignal { monadSignalMonad = m })                           = "signal" ++ m

monadStateLayerRegs :: CtsDecl -> CM MonadStateEnv
monadStateLayerRegs (CtsMonadDecl _ n ls) = do
                                               maybeRegs <- mapM (stateLayerReg n) ls
                                               let regs  =  catMaybes maybeRegs
                                               return regs

stateLayerReg :: CtsIdent -> CtsMonadLayer -> CM (Maybe ((CtsIdent,CtsIdent),Register))
stateLayerReg m (CtsStateLayer _ sn) = do
                                          reg <- freshReg
                                          return (Just ((m,sn),reg))
stateLayerReg _ _                    = return Nothing

trProg :: CtsProg -> CM [TacCommand]
trProg (CtsProg decls) = do
                            let monadDecls = filter isMonadDecl decls
                                dataDecls  = filter isDataDecl decls
                                tySigs     = filter isTySig decls
                                funDecls   = concatMap extractFunDecls decls
                                
                                isMonadDecl (CtsMonadDecl _ _ _)       = True
                                isMonadDecl _                          = False
                                isDataDecl (CtsDataDecl _ _ _)         = True
                                isDataDecl _                           = False
                                isTySig (CtsFunTySig _ _ _ _)          = True
                                isTySig _                              = False
                                extractFunDecls e@(CtsFunDecl _ _ _ _) = [e]
                                extractFunDecls (CtsRecDecl ds)        = concatMap extractFunDecls ds
                                extractFunDecls _                      = []
                                
                                monadEnv = concatMap mkMonadNPMs monadDecls
                                dtEnv    = map mkDTSpec dataDecls
                                funEnv   = map (mkFunSpec funDecls) tySigs
                                
                            monadStateEnv <- (liftM concat) $ mapM monadStateLayerRegs monadDecls
                                
                            inFunTabCM funEnv $ inMonadEnvCM monadEnv $ inMonadStateEnvCM monadStateEnv $ inDTTabCM dtEnv $ liftM concat $ mapM trDecl decls

-- FIXME: This is weird. Go through each type decl and look up the associated
--        function definition, then fill in the FunSpec from that
mkFunSpec :: [CtsDecl] -> CtsDecl -> FunSpec
mkFunSpec funDecls (CtsFunTySig _ f tys retty) = let
                                                    funDecl = find (\(CtsFunDecl _ f' _ _) -> f == f') funDecls
                                                 in
                                                    case funDecl of
                                                       Nothing                      -> error $ "Function " ++ f ++ " has type signature but no definition"
                                                       (Just (CtsFunDecl _ _ xs e)) -> FunSpec {
                                                                                          funSpecName     = f,
                                                                                          funSpecArgNames = xs,
                                                                                          funSpecArgTys   = tys,
                                                                                          funSpecRetTy    = retty,
                                                                                          funSpecBody     = e
                                                                                       }

trDecl :: CtsDecl -> CM [TacCommand]
trDecl (CtsFunDecl pos f xs e) =
       inSrcPosCM pos $
         do
            funSpec      <- getFunSpec f
            regsXs       <- replicateM (length xs) freshReg
            
            let argTys   =  funSpecArgTys funSpec
                bindings =  zipWith3 Binding xs argTys regsXs
            
            (pi,_)       <- inBindEnvCM bindings (trExpr e)
            
            return $ [Labeled $ Label $ "__" ++ f] ++
                     [Comment "FIXME: Junk to set up arg registers"] ++
                     pi ++
                     [Comment "FIXME: Junk to squish the stack frame and return"]
trDecl _ = return []

------------------
------------------
-- Declarations --
------------------
------------------

mkDTSpec :: CtsDecl -> DTSpec
mkDTSpec (CtsDataDecl _ ident ctors) = DTSpec {
                                          dtSpecName = ident,
                                          dtSpecConSpecs = ctorspecs
                                       }
                                       where
                                          ctorspecs = map mkCtorSpec ctors
                                          mkCtorSpec (CtsConDecl ident types) = ConSpec {
                                                                                   conSpecName = ident,
                                                                                   conSpecTys  = types
                                                                                }
                                                                 
monadicBase :: CtsType -> CtsType
monadicBase (TyMonadic _ t) = t
monadicBase _               = cantHappen "Attempt to take base of non-monadic type"

mkMove :: Register -> CtsType -> Register -> CM [TacCommand]
mkMove rDest ty rSrc = if goesOnStack ty
                         then return [Move rDest rSrc]
                         else do
                            (piSize,rSize) <- sizeOf ty rSrc
                            return $ piSize ++
                                     [MoveMem rDest rSrc rSize]


-----------
-----------
-- Types --
-----------
-----------

wordSize :: Int
wordSize = 4

skipPast :: CtsType -> Register -> CM [TacCommand]
skipPast TyInt r           = freshReg >>= \ rSkip -> return [Constant rSkip wordSize,Binary r r Plus rSkip]
skipPast TyBool r          = freshReg >>= \ rSkip -> return [Constant rSkip wordSize,Binary r r Plus rSkip]
skipPast TyUnit _          = return []
skipPast (TyADT _) _       = return [Comment "FIXME: size of ADT"]
skipPast (TyTuple ts) r    = (liftM concat) $ mapM (\t -> skipPast t r) ts
skipPast (TyList t) r      = freshReg >>= \ rSkip -> return [Unary rSkip Deref r,Binary r r Plus rSkip]
skipPast (TyMonadic _ _) r = freshReg >>= \ rSkip -> return [Constant rSkip wordSize,Binary r r Plus rSkip]                                      

sizeOf :: CtsType -> Register -> CM ([TacCommand],Register)
sizeOf t rStart = if goesOnStack t
                   then do
                     rEnd   <- freshReg
                     rSize  <- freshReg
                     piSkip <- skipPast t rEnd
                     return ([Comment $ "begin sizeOf " ++ showType t] ++
                             [Move rEnd rStart] ++
                             piSkip ++
                             [Binary rSize rEnd Minus rStart] ++
                             [Comment "end sizeOf"]
                            ,
                            rSize
                            )
                   else do
                     rRes <- freshReg
                     let size = case t of
                                   TyUnit -> 0
                                   _      -> 4
                     return ([Comment $ "begin sizeOf " ++ showType t] ++
                             [Constant rRes wordSize] ++
                             [Comment "end sizeOf"]
                             ,
                             rRes)

-----------------
-----------------
-- Expressions --
-----------------
-----------------

compileError :: String -> CM a
compileError s = do
                    srcPos <- rdSrcPosCM
                    error $ "At " ++ show srcPos ++ ": compilation error: " ++ s

--                                    --
-- Compilation of special expressions --
--                                    --
isSpecial :: CtsExpr -> CM Bool
isSpecial e = do
                 monadEnv     <- rdMonadEnvCM
                 let specials =  map npmName monadEnv
                 case e of
                    (CtsVar "lkup" _) -> return True
                    (CtsVar "xEnv" _) -> return True
                    (CtsVar "emptyEnv" _) -> return True
                    (CtsVar "head" _) -> return True
                    (CtsVar n _)   -> return (n `elem` specials)
                    (CtsApp "lkup" _ _) -> return True
                    (CtsApp "xEnv" _ _) -> return True
                    (CtsApp "emptyEnv" _ _) -> return True
                    (CtsApp "head" _ _) -> return True
                    (CtsApp n _ _) -> return (n `elem` specials)
                    _              -> return False

trSpecial :: CtsExpr -> CM ([TacCommand],Register)
trSpecial (CtsVar n t)      = do
                                  monadEnv <- rdMonadEnvCM
                                  let mNpm =  lookupBy npmName n monadEnv
                                  -- Other cases should not arise if well-typed
                                  case mNpm of
                                     (Just (MonadGet { monadGetMonad = m, monadGetStateName = sn })) ->
                                        do
                                           regDest       <- freshReg
                                           monadStateEnv <- rdMonadStateEnvCM
                                           let regSrc    =  fromJust $ lookup (m,sn) monadStateEnv
                                           return ([Comment $ "Get: " ++ m ++ "." ++ sn ++ " is in " ++ show regSrc,
                                                    Move regDest regSrc],regDest)
                                     Nothing ->
                                        case n of
                                           "emptyEnv" -> return ([Comment "FIXME: emptyEnv"],VR 1492)
trSpecial (CtsApp n args t) = do
                                 monadEnv <- rdMonadEnvCM
                                 let mNpm  =  lookupBy npmName n monadEnv
                                     punt :: CM ([TacCommand],Register)
                                     punt = do
                                               resArgs     <- mapM trExpr args
                                               let pisArgs =  map fst resArgs
                                               return (concat pisArgs ++ [Comment $ "FIXME: punting on " ++ n],VR 14920000)


                                 case mNpm of
                                    (Just (MonadStep {})) -> trExpr (head args)
                                    (Just (MonadGet {}))  -> trSpecial (CtsVar n t)
                                    (Just (MonadPut { monadPutMonad = m, monadPutStateName = sn })) ->
                                       do
                                          let arg       =  head args
                                          (pi,regSrc)   <- trExpr arg
                                          monadStateEnv <- rdMonadStateEnvCM
                                          let regDest   =  fromJust $ lookup (m,sn) monadStateEnv
                                          return (pi ++ [Comment $ "Put: " ++ m ++ "." ++ sn ++ " is in " ++ show regDest,
                                                         Move regDest regSrc],
                                                  cantHappen "Attempt to use register associated with unit value"
                                                 )
                                    (Just (MonadReadHeap { })) -> punt
                                    (Just (MonadStoreHeap { })) -> punt
                                    (Just (MonadGetreq { })) -> punt
                                    (Just (MonadPutrsp { })) -> punt
                                    (Just (MonadIsDone { })) -> punt
                                    (Just (MonadSignal { })) -> punt
                                    Nothing ->
                                       case n of
                                          "lkup" -> punt
                                          "xEnv" -> punt
                                          "head" -> do
                                             let [argL]         =  args
                                             (piArgL,rArgL)     <- trExpr argL
                                             rWordSize          <- freshReg
                                             rFirstElem         <- freshReg
                                             rResult            <- freshReg
                                             (piSizeOf,rSizeOf) <- sizeOf (typeOf argL) rFirstElem
                                             
                                             return (piArgL ++
                                                     [Constant rWordSize wordSize,
                                                      Binary rFirstElem rArgL Plus rWordSize
                                                     ] ++
                                                     piSizeOf ++
                                                     [Move rResult SP,
                                                      PushMem rFirstElem rSizeOf
                                                     ],
                                                     rResult
                                                    )
                                                     
                                                      
                                                     

goesOnStack :: CtsType -> Bool
goesOnStack TyInt           = False
goesOnStack TyBool          = False
goesOnStack TyUnit          = False
goesOnStack (TyMonadic _ _) = False
goesOnStack _               = True

--                                    --
-- Compilation of general expressions --
--                                    --
trExpr :: CtsExpr -> CM ([TacCommand],Register)
trExpr e@(CtsVar ident t)               = do
                                             special <- isSpecial e
                                             if special
                                               then trSpecial e
                                               else do
                                                 bindenv <- rdBindEnvCM
                                        
                                                 if ident `elem` (map bindingName bindenv)
                                                   then do
                                                     let b   = fromJust $ lookupBy bindingName ident bindenv
                                                         reg = bindingReg b
                                                     return ([],reg)
                                                   else do
                                                     funTab <- rdFunTabCM
                                                     if ident `elem` (map funSpecName funTab)
                                                        then trExpr (CtsApp ident [] t)
                                                        else do
                                                          kappa <- rdKappaCM
                                                          case kappa of
                                                            (Just k) | kappaName k == ident ->
                                                              trExpr (CtsApp ident [] t)
                                                            _ ->
                                                              compileError $ "Unbound variable: " ++ ident
                                                              
trExpr e@(CtsApp ident args _)               = do
                                                  special <- isSpecial e
                                                  if special
                                                    then trSpecial e
                                                    else do
                                                      funtab       <- rdFunTabCM
                                                      kappa        <- rdKappaCM
    
                                                      if ident `elem` map funSpecName funtab then do
                                                          let funSpec =  fromJust (lookupBy funSpecName ident funtab)
                                                          piArgs      <- liftM concat $ mapM trExprPush args
                                                          rResult     <- freshReg
                                                          return ([Comment $ "CALL: " ++ ident,
                                                                   Comment "FIXME: Push fpsave, spsave, args"] ++
                                                                  piArgs ++
                                                                  [Jump $ Label $ "__" ++ ident,
                                                                   Comment $ "FIXME: Set the result register (pop if fits in reg)"],
                                                                 rResult)
                                                        else do
                                                          kappa <- rdKappaCM
                                                          case kappa of 
                                                            (Just k) | kappaName k == ident -> do
                                                              let label   =  kappaLabel k
                                                                  regs    =  kappaRegs k
                                                              argResults  <- mapM trExpr args
                                                              let piArgs  =  concatMap fst argResults
                                                                  argRegs =  map snd argResults
    
                                                              -- FIXME: This is weird, but it is what we want.  :)
                                                              piMoves     <- liftM concat $ mapM ((uncurry . uncurry) mkMove) (zip (zip regs (map typeOf args)) argRegs)
                                                              
                                                              return (piArgs ++
                                                                      piMoves ++
                                                                      [Move SP (kappaSpSave k),
                                                                       Jump (kappaLabel k)],
                                                                     undefined)
                                                            _ ->
                                                              compileError $ "Unbound function name: " ++ ident
                                                              
trExpr (CtsFixApp ns e es t)       = do
                                        let argTys   =  map typeOf es
                                        argResults   <- mapM trExpr es
                                        let piArgs   =  concatMap fst argResults
                                            regs     =  map snd argResults
                                        bindenv      <- rdBindEnvCM
                                        l            <- freshLabel
                                        rSpSave      <- freshReg
                                        let bindenv' =  zipWith3 Binding (tail ns) argTys regs ++ bindenv
                                            kappa'   =  Just $ Kappa { kappaName = (head ns), kappaSpSave = rSpSave, kappaLabel = l, kappaRegs = regs }
                                        (piBody,rD)  <- inKappaCM kappa' $ inBindEnvCM bindenv' $ trExpr e
                                        return $ (piArgs ++
                                                  [Move rSpSave SP,
                                                   Labeled l] ++
                                                  piBody,
                                                 rD)
 
trExpr (CtsConstrApp ident args t) = do
                                        tag         <- getCtorTag ident
                                        
                                        piArgs      <- liftM concat (mapM trExprPush args)
                                        
                                        regDest     <- freshReg
                                        regTag      <- freshReg
                                        
                                        let pi      =  [Move regDest SP,
                                                        Constant regTag tag,
                                                        PushReg regTag] ++
                                                       piArgs

                                        return (pi,regDest)

trExpr (CtsTuple es _)             = do
                                        piEs    <- liftM concat (mapM trExprPush es)
                                        regDest <- freshReg
                                        let pi  =  [Move regDest SP] ++
                                                   piEs
                                        return (pi,regDest)

trExpr (CtsCase e alts t)          = do
                                        (piE,rE)  <- trExpr e
                                        doneLabel <- freshLabel
                                        regDest   <- freshReg
                                        piAlts    <- mapM (trAlt doneLabel regDest (typeOf e) rE) alts

                                        return (piE ++ concat piAlts ++ [Labeled doneLabel], regDest)
                                        
-- Unit has no associated storage, so we use an error value in place of the
-- register.
trExpr (CtsUnit _)                 = return ([],cantHappen "Attempt to use register associated with unit value")

trExpr (CtsEmptyList _)            = do
                                        rZero <- freshReg
                                        rRes  <- freshReg
                                        return ([Move rRes SP,
                                                 Constant rZero 0,
                                                 PushReg rZero],
                                                rRes)

trExpr (CtsLet letBindings e ty)   = do
                                        let vars        =  map fst letBindings
                                            es          =  map snd letBindings
                                            tys         =  map typeOf es
                                        resEs           <- mapM trExpr es
                                        let pis         =  map fst resEs
                                            regs        =  map snd resEs
                                        rho             <- rdBindEnvCM
                                        let newBindings =  zipWith3 Binding vars tys regs
                                        (piE,rE)        <- inBindEnvCM (newBindings++rho) (trExpr e)    
                                        return (concat pis ++
                                                piE,
                                                rE)
                                                

trExpr (CtsInfixApp e1 "+" e2 _)   = do
                                        (pi1,reg1) <- trExpr e1
                                        (pi2,reg2) <- trExpr e2
                                        regDest    <- freshReg
                                        let pi     =  pi1 ++
                                                      pi2 ++
                                                      [Binary regDest reg1 Plus reg2]
                                        return (pi,regDest)

trExpr (CtsInfixApp e1 "-" e2 _)   = do
                                        (pi1,reg1) <- trExpr e1
                                        (pi2,reg2) <- trExpr e2
                                        regDest    <- freshReg
                                        let pi     =  pi1 ++
                                                      pi2 ++
                                                      [Binary regDest reg1 Minus reg2]
                                        return (pi,regDest)
trExpr (CtsInfixApp e1 ">" e2 _)   = do
                                        (pi1,reg1) <- trExpr e1
                                        (pi2,reg2) <- trExpr e2
                                        regDest    <- freshReg
                                        let pi     = pi1 ++
                                                     pi2 ++
                                                     [Binary regDest reg1 GrtrThan reg2]
                                        return (pi,regDest)

trExpr (CtsInfixApp e1 "<" e2 _)   = do
                                        (pi1,reg1) <- trExpr e1
                                        (pi2,reg2) <- trExpr e2
                                        regDest    <- freshReg
                                        let pi     = pi1 ++
                                                     pi2 ++
                                                     [Binary regDest reg1 LessThan reg2]
                                        return (pi,regDest)

trExpr (CtsInfixApp e1 "==" e2 _)  = do
                                        (pi1,reg1) <- trExpr e1
                                        (pi2,reg2) <- trExpr e2
                                        regDest    <- freshReg
                                        let pi     =  pi1 ++
                                                      pi2 ++
                                                      [Binary regDest reg1 IsEqual reg2]
                                        return (pi,regDest)
                                        
                                        
trExpr (CtsInfixApp e1 ":" e2 _)    = do
                                         (pi1,reg1)         <- trExpr e1
                                         (pi2,reg2)         <- trExpr e2
                                         regDest            <- freshReg
                                         (piSizeE1,rSizeE1) <- sizeOf (typeOf e1) reg1
                                         (piSizeE2,rSizeE2) <- sizeOf (typeOf e2) reg2
                                         rSizeRes           <- freshReg
                                         rTail              <- freshReg
                                         rTailSize          <- freshReg
                                         rWordSize          <- freshReg
                                         return (pi1 ++
                                                 pi2 ++
                                                 piSizeE1 ++
                                                 piSizeE2 ++
                                                 [Move regDest SP,
                                                  Binary rSizeRes rSizeE1 Plus rSizeE2,
                                                  PushReg rSizeRes,
                                                  (if goesOnStack (typeOf e1)
                                                      then PushMem reg1 rSizeE1
                                                      else PushReg reg1),
                                                  Constant rWordSize wordSize,
                                                  Binary rTail reg2 Plus rWordSize,
                                                  Binary rTailSize rSizeE2 Minus rWordSize,
                                                  PushMem rTail rTailSize
                                                 ]
                                                 ,
                                                 regDest
                                                )

trExpr (CtsLitExpr (CtsLitInt i) _) = do
                                         regDest <- freshReg
                                         let pi  =  [Constant regDest i]
                                         return (pi,regDest)

trExpr (CtsLitExpr (CtsLitBool b) _) = do
                                          regDest <- freshReg
                                          let pi  =  [Constant regDest (if b then 1 else 0)]
                                          return (pi,regDest)

trExpr (CtsLitExpr (CtsLitString s) _) = do
                                            regDest <- freshReg
                                            let pi = [Comment $ "FIXME: OH NO A STRING " ++ s ++ " (" ++ showReg regDest ++")"]
                                            return (pi,regDest)

trExpr (CtsNeg e _)                  = do
                                          (piE,regE) <- trExpr e
                                          regDest    <- freshReg
                                          let pi     = piE ++
                                                       [Unary regDest Neg regE]
                                          return (pi,regDest)

trExpr (CtsIfThenElse e t f _)       = do
                                          (piTest,regTest)   <- trExpr e
                                          (piTrue,regTrue)   <- trExpr t
                                          (piFalse,regFalse) <- trExpr f
                                     
                                          labFalse           <- freshLabel
                                          labEnd             <- freshLabel
                                          regDest            <- freshReg

                                          let pi             =  piTest ++
                                                                [BZero regTest labFalse] ++
                                                                piTrue ++
                                                                [Move regDest regTrue,
                                                                 Jump labEnd,
                                                                 Labeled labFalse] ++
                                                                piFalse ++
                                                                [Move regDest regFalse,
                                                                 Labeled labEnd]
                                                                 
                                          return (pi,regDest)

trExpr (CtsBind e1 n e2 _)         = do
                                        let t1            =  monadicBase (typeOf e1)
                                        (pi1,reg1)        <- trExpr e1
                                        bindenv           <- rdBindEnvCM
                                        let newbinding    =  Binding {
                                                                bindingName = n,
                                                                bindingTy   = t1,
                                                                bindingReg  = reg1
                                                             }
                                            bindenv'      =  newbinding:bindenv
                                        (pi2,reg2)        <- inBindEnvCM bindenv' $ trExpr e2
                                        return (pi1++pi2,reg2)

trExpr (CtsBindNull e1 e2 _)       = do
                                        (pi1,reg1) <- trExpr e1
                                        (pi2,reg2) <- trExpr e2
                                        return (pi1++pi2,reg2)

trExpr (CtsReturn e _)             = trExpr e

trExpr e                           = compileError $ "Can't generate code for this: " ++ (show e)

trAlt :: Label -> Register -> CtsType -> Register -> CtsAlt -> CM [TacCommand]
trAlt doneLabel rDest tyS rS alt = case alt of
                                      (CtsAlt (CtsPTuple xs) e) ->
                                        case tyS of
                                           (TyTuple tysXs) -> do
                                              rsXs            <- replicateM (length xs) freshReg
                                              bindEnv         <- rdBindEnvCM
                                              let newBindings =  zipWith3 Binding xs tysXs rsXs
                                              (piE,rE)        <- inBindEnvCM (newBindings ++ bindEnv) $ trExpr e
                                              return $ [Comment "FIXME: Init regs for case-bound vars in tuple"] ++
                                                       piE ++
                                                       [Move rDest rE]
                                      (CtsAlt (CtsPConstr ctor xs) e) ->
                                        case tyS of
                                           (TyADT dtName) -> do
                                              dtSpec       <- getDTSpec dtName
                                              let conSpecs =  dtSpecConSpecs dtSpec
                                                  conSpec  =  fromJust $ lookupBy conSpecName ctor conSpecs
                                                  tysXs    =  conSpecTys conSpec
                                              rsXs            <- replicateM (length xs) freshReg
                                              bindEnv         <- rdBindEnvCM
                                              let newBindings =  zipWith3 Binding xs tysXs rsXs
                                              (piE,rE)        <- inBindEnvCM (newBindings ++ bindEnv) $ trExpr e
                                              return $ [Comment "FIXME: Check tag in ADT",
                                                        Comment "FIXME: Init regs for case-bound vars in ADT"] ++
                                                       piE ++
                                                       [Move rDest rE,
                                                        Jump doneLabel]
                                                                            

trExprPush :: CtsExpr -> CM [TacCommand]
trExprPush e = do
                  let ty   =  typeOf e
                  (pi,reg) <- trExpr e
                  if goesOnStack ty
                     then return pi
                     else return (pi ++ [PushReg reg])


freshLabel :: CM Label
freshLabel = do
                n <- freshNumCM
                return (Label $ "l" ++ show n)

freshReg :: CM Register
freshReg = do
              n <- freshNumCM
              return (VR n)

cantHappen :: String -> a
cantHappen = error . ("Internal compiler error: " ++)
