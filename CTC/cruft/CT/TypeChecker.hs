module CT.TypeChecker (tc, tc_ann) where

import CT.Syntax
import CT.TypeCheckerMonad
import Data.Maybe
import Data.List
import Control.Monad
import System.IO.Unsafe

tc_triv :: CtsProg -> Either String CtsProg
tc_triv prog = Right prog

--
-- a trivial type-annotator;
--
-- just fill in the types for declared ports in the state layer, and
-- leave everything else alone.
--
-- this is a work-around to deal with the new additions for 'signal'
-- without having to fix much more extensive problems with the type checker
--
-- really, we are only interested in having an 'InPort' or an 'Outport'
-- annotation appear next to the first argument of 'signal'
--
-- 2009.12.14 Schulz
--

tc_ann :: CtsProg -> Either String CtsProg
tc_ann (CtsProg ds) =
  let ps = getPorts ds
  in
    Right $ CtsProg $ map (annotate ps) ds

getPorts :: [CtsDecl] -> [(CtsIdent, CtsType)]
getPorts ((CtsMonadDecl _ _ ms):ds) =
  let f = \m -> \xs -> case m of
                         (CtsStateLayer t x) -> (x, t):xs
                         _                   -> xs
  in
    (foldr f [] ms) ++ (getPorts ds)
getPorts (_:ds) = getPorts ds
getPorts [ ]    = [ ]

--
-- these annotations DO NOT respect lexical scope;
-- port names declared at the state monad layer will
-- override any local identifier names that happen to coincide
--
-- 2009.12.14 Schulz
--
annotate :: [(CtsIdent, CtsType)] -> CtsDecl -> CtsDecl
annotate ps (CtsFunDecl l f xs b) =
  let b' = annotateExpr ps b
  in
    CtsFunDecl l f xs b'
annotate _ d = d

annotateExpr :: [(CtsIdent, CtsType)] -> CtsExpr -> CtsExpr
annotateExpr ps e@(CtsApp f args t) =
  case f of
    "signal" -> case args of
                  [p, q] -> (CtsApp f [annotateExpr ps p, q] t)
                  _      -> e  -- this shouldn't happen,
                               -- but will be caught downstream (2009.12.14)
    _        -> e

annotateExpr ps (CtsFixApp xs e args t) =
  let e'    = annotateExpr ps e
      args' = map (annotateExpr ps) args
  in
    CtsFixApp xs e' args' t

annotateExpr ps (CtsSemiFixApp g xs e args t) =
  let e'    = annotateExpr ps e
      g'    = annotateExpr ps g
      args' = map (annotateExpr ps) args
  in
    CtsSemiFixApp g' xs e' args' t

annotateExpr ps (CtsInfixApp e1 f e2 t) =
  let e1' = annotateExpr ps e1
      e2' = annotateExpr ps e2
  in
    CtsInfixApp e1' f e2' t

annotateExpr ps (CtsConstrApp f args t) =
  let args' = map (annotateExpr ps) args
  in
    case (lookup f ps) of
      (Just t') -> CtsConstrApp f args' t'
      Nothing   -> CtsConstrApp f args' t  -- this shouldnt' happen either

annotateExpr ps l@(CtsLitExpr _ _) = l

annotateExpr ps (CtsVar x t) =
  case (lookup x ps) of
    (Just t') -> (CtsVar x t')
    Nothing   -> (CtsVar x t)

annotateExpr ps (CtsNeg e t) =
  let e' = annotateExpr ps e
  in
    CtsNeg e' t

annotateExpr ps (CtsIfThenElse b e1 e2 t) =
  let b'  = annotateExpr ps b
      e1' = annotateExpr ps e1
      e2' = annotateExpr ps e2
  in
    CtsIfThenElse b' e1' e2' t

annotateExpr ps (CtsCase e as t) =
  let e'  = annotateExpr  ps e
      f   = \(CtsAlt p x) -> CtsAlt p (annotateExpr  ps x)
      as' = map f as
  in
    CtsCase e' as' t

annotateExpr  ps (CtsTuple es t) =
  let es' = map (annotateExpr  ps) es
  in
    CtsTuple es' t

annotateExpr  ps (CtsList es t) =
  let es' = map (annotateExpr  ps) es
  in
    CtsList es' t

annotateExpr _ (CtsUnit t)      = CtsUnit t
annotateExpr _ (CtsEmptyList t) = CtsEmptyList t

annotateExpr  ps (CtsLet xs e t) =
  let e'  = annotateExpr  ps e
      xs' = map (\(y, s) -> (y, annotateExpr  ps s)) xs
  in
    CtsLet xs' e' t

annotateExpr  ps (CtsBind e1 x e2 t) =
  let e1' = annotateExpr  ps e1
      e2' = annotateExpr  ps e2
  in
    CtsBind e1' x e2' t

annotateExpr  ps (CtsBindNull e1 e2 t) =
  let e1' = annotateExpr  ps e1
      e2' = annotateExpr  ps e2
  in
    CtsBindNull e1' e2' t

annotateExpr  ps (CtsReturn e t) =
  let e' = annotateExpr  ps e
  in
    CtsReturn e' t

annotateExpr  ps x = error $ "in CT.Parser.annotate: no case for " ++ (show x)

--
-- back to Adam's code:
--

tc :: CtsProg -> Either String CtsProg
tc prog = runTCM (go prog) (CtsSrcPos "<undefined>" 0 0) [] [] [] [] Nothing
  where go :: CtsProg -> TCM (Either String CtsProg)
        go prog = catchTypeErrorTCM (tcProg prog >>= \p -> return (Right p)) (\e -> return (Left e))

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

unify :: CtsType -> CtsType -> Maybe CtsType
unify (TyMonadic m ty) (TyMonadic m' ty') = do
                                              uniTy <- unify ty ty'
                                              if m == m' || m' == "m"
                                                then return (TyMonadic m ty)
                                                else if m == "m"
                                                  then return (TyMonadic m' ty)
                                                  else mzero
unify TyInt TyInt                         = return TyInt
unify TyBool TyBool                       = return TyBool
unify TyString TyString                   = return TyString
unify TyUnit TyUnit                       = return TyUnit
unify (TyADT n) (TyADT n')                = if n == n' then return (TyADT n) else mzero
unify (TyTuple tys) (TyTuple tys')        = if (length tys /= length tys')
                                              then mzero
                                              else do
                                                uniTys <- sequence (zipWith unify tys tys')
                                                return (TyTuple uniTys)
unify (TyList ty) (TyList ty')            = do
                                               uniTy <- unify ty ty'
                                               return (TyList uniTy)
unify _ _                                 = mzero

unifyOrDie :: CtsIdent -> Int -> CtsType -> CtsType -> TCM CtsType
unifyOrDie f pos ty ty' = do
                             let uniTy = unify ty ty'
                             case uniTy of
                                (Just tu) -> return tu
                                Nothing   -> typeError $ f ++ ": inferred type " ++ show ty ++ " of argument "
                                                           ++ show pos ++ " does not match expected type " ++ show ty'

errWrongNumArgs :: CtsIdent -> Int -> Int -> TCM a
errWrongNumArgs name expected given = typeError $ name ++ " takes " ++ show expected ++ " argument"
                                                       ++ if expected == 1 then "" else "s" ++ ", "
                                                       ++ show given ++ " given"

isSpecial :: CtsExpr -> TCM Bool
isSpecial e = do
                 monadEnv     <- rdMonadEnvTCM
                 let specials =  map npmName monadEnv
                 case e of
                    (CtsVar "lkup" _) -> return True
                    (CtsVar "xEnv" _) -> return True
                    (CtsVar "emptyEnv" _) -> return True
                    (CtsVar "head" _) -> return True
                    (CtsVar n _)      -> return (n `elem` specials)
                    (CtsApp "lkup" _ _) -> return True
                    (CtsApp "xEnv" _ _) -> return True
                    (CtsApp "emptyEnv" _ _) -> return True
                    (CtsApp "head" _ _) -> return True
                    (CtsApp n _ _)    -> return (n `elem` specials)
                    _                 -> return False

inferSpecial :: CtsExpr -> TCM CtsExpr
inferSpecial (CtsVar n _) = do
                               monadEnv <- rdMonadEnvTCM
                               let npm  = lookupBy npmName n monadEnv
                               case npm of
                                  (Just (MonadStep _ _)) -> errWrongNumArgs n 1 0
                                  (Just (MonadGet { monadGetMonad = m, monadGetStateType = ty })) ->
                                       return $ CtsVar n (TyMonadic m ty)
                                  (Just (MonadPut _ _ _)) -> errWrongNumArgs n 1 0
                                  (Just (MonadReadHeap _ _)) -> errWrongNumArgs n 1 0
                                  (Just (MonadStoreHeap _ _)) -> errWrongNumArgs n 1 0
                                  (Just (MonadGetreq _ _ _)) -> errWrongNumArgs n 1 0
                                  (Just (MonadPutrsp _ _ _)) -> errWrongNumArgs n 2 0
                                  (Just (MonadIsDone _ _))   -> errWrongNumArgs n 1 0
--                                  (Just (MonadSignal _ _ _)) -> errWrongNumArgs n 1 0
                                  (Just (MonadSignal _ _ _)) -> errWrongNumArgs n 2 0  -- now taking 2 arguments (2009.12.14) Schulz
                                  Nothing -> case n of
                                                "lkup" -> errWrongNumArgs n 2 0
                                                "xEnv" -> errWrongNumArgs n 3 0
                                                "emptyEnv" -> return $ CtsVar n (TyADT "Env")
                                                "head" -> errWrongNumArgs n 1 0

inferSpecial (CtsApp n args_ _) = do
                                    monadEnv <- rdMonadEnvTCM
                                    let npm  =  lookupBy npmName n monadEnv
                                    case npm of
                                       (Just (MonadStep { monadStepBaseMonad = b, monadStepResultMonad = r })) ->
                                          do
                                             args <- mapM tcExpr args_
                                             if length args /= 1
                                                then typeError $ n ++ " takes one argument, " ++ show (length args) ++ " given"
                                                else do
                                                   let arg = head args
                                                   case (typeOf arg) of
                                                      (TyMonadic am aty) -> if am == b || am == "m"
                                                                              then return (CtsApp n args (TyMonadic r aty))
                                                                              else typeError $ "Type " ++ showType (typeOf arg) ++ " of argument to " ++
                                                                                               n ++ " is not in expected monad " ++ b
                                                      _                  -> typeError $ "Type " ++ showType (typeOf arg) ++ " of argument to " ++
                                                                                        n ++ " is not in expected monad " ++ b

                                       (Just (MonadGet { monadGetMonad = m, monadGetStateType = ty })) ->
                                          do
                                             args <- mapM tcExpr args_
                                             if length args /= 0
                                                then errWrongNumArgs n 0 (length args)
                                                else return $ CtsApp n args (TyMonadic m ty)

                                       (Just (MonadPut { monadPutMonad = m, monadPutStateType = ty })) ->
                                          do
                                             args <- mapM tcExpr args_
                                             if length args /= 1
                                                then errWrongNumArgs n 1 (length args)
                                                else do
                                                   let arg    = head args

                                                   unifyOrDie n 1 (typeOf arg) ty
                                                   return $ CtsApp n args (TyMonadic m TyUnit)
                                       (Just (MonadReadHeap { monadReadHeapMonad = m })) ->
                                          do
                                             args <- mapM tcExpr args_
                                             if length args /= 1
                                                then errWrongNumArgs n 1 (length args)
                                                else do
                                                   let arg = head args
                                                   
                                                   -- FIXME: assuming Loc and V
                                                   unifyOrDie n 1 (typeOf arg) (TyADT "Loc")
                                                   return $ CtsApp n args (TyMonadic m (TyADT "V"))
                                       (Just (MonadStoreHeap { monadStoreHeapMonad = m })) ->
                                          do
                                             args <- mapM tcExpr args_
                                             if length args /= 1
                                                then errWrongNumArgs n 1 (length args)
                                                else do
                                                   let arg = head args
                                                   
                                                   -- FIXME: assuming Loc and V
                                                   unifyOrDie n 1 (typeOf arg) (TyADT "V")
                                                   return $ CtsApp n args (TyMonadic m (TyADT "Loc"))
                                                     
                                       (Just (MonadGetreq { monadGetreqMonad = m, monadGetreqResultMonad = b, monadGetreqReqType = req })) ->
                                          do
                                             args <- mapM tcExpr args_
                                             if length args /= 1
                                               then errWrongNumArgs n 1 (length args)
                                               else do
                                                  let arg = head args
                                                  
                                                  case typeOf arg of
                                                     (TyMonadic m' _) -> if m' /= m && m' /= "m"
                                                                          then typeError $ "Type " ++ showType (typeOf arg) ++ " of argument to " ++
                                                                                           n ++ " is not in expected monad " ++ m
                                                                          else return $ CtsApp n args (TyMonadic b req)
                                                     _               -> typeError $ "Type " ++ showType (typeOf arg) ++ " of argument to " ++
                                                                                            n ++ " is not in expected monad " ++ m
                                                                                            
                                       (Just (MonadPutrsp { monadPutrspMonad = m, monadPutrspResultMonad = b, monadPutrspRspType = rsp })) ->
                                          do
                                             args <- mapM tcExpr args_
                                             if length args /= 2
                                               then errWrongNumArgs n 2 (length args)
                                               else do
                                                 let [argRsp,argPhi] = args
                                                 
                                                 case unify (typeOf argRsp) rsp of
                                                    Nothing       -> typeError $ "Type " ++ showType (typeOf argRsp) ++ " of first argument to " ++
                                                                           n ++ " does not match expected type " ++ showType rsp
                                                    (Just uniRsp) -> case typeOf argPhi of
                                                                        (TyMonadic m' t) -> if m' /= m && m' /= "m"
                                                                                             then typeError $ "Type " ++ showType (typeOf argPhi) ++ " of second argument to " ++
                                                                                                              n ++ " is not in expected monad " ++ m
                                                                                             else return $ CtsApp n args (TyMonadic b (TyMonadic m t))
                                                                        _                -> typeError $ "Type " ++ showType (typeOf argPhi) ++ " of second argument to " ++
                                                                                                              n ++ " is not in expected monad " ++ m

                                       (Just (MonadIsDone { monadIsDoneMonad = m, monadIsDoneResultMonad = mr })) ->
                                          do
                                             args <- mapM tcExpr args_
                                             if length args /= 1
                                               then errWrongNumArgs n 1 (length args)
                                               else do
                                                  let arg = head args
                                                  
                                                  case typeOf arg of
                                                     (TyMonadic m' t) -> if m' /= m && m' /= "m"
                                                                          then typeError $ "Type " ++ showType (typeOf arg) ++ " of argument to " ++
                                                                                           n ++ " is not in expected monad " ++ m
                                                                          else return $ CtsApp n args (TyMonadic mr TyBool)
                                                     _                -> typeError $ "Type " ++ showType (typeOf arg) ++ " of argument to " ++
                                                                                     n ++ " is not in expected monad " ++ m
                                       (Just (MonadSignal { monadSignalMonad = m, monadSignalReqType = tq, monadSignalRspType = tp })) ->
                                          do
                                             args <- mapM tcExpr args_
                                             -- if length args /= 1
                                             if length args /= 2  -- now taking 2 arguments (2009.12.14 Schulz)
                                               then errWrongNumArgs n 2 (length args)
                                               else do
                                                 let arg = head args
                                                 
                                                 unifyOrDie n 1 tq (typeOf arg)
                                                 return $ CtsApp n args (TyMonadic m tp)
                                       Nothing -> case n of
                                                     -- FIXME: Assuming String -> Env -> Loc
                                                     "lkup" -> do
                                                                  args <- mapM tcExpr args_
                                                                  if length args /= 2
                                                                    then errWrongNumArgs n 2 (length args)
                                                                    else do
                                                                      let [argX,argRho] = args
                                                                          tyX           = typeOf argX
                                                                          tyRho         = typeOf argRho
                                                                      
                                                                      unifyOrDie n 1 tyX TyString
                                                                      unifyOrDie n 2 tyRho (TyADT "Env")
                                                                      return (CtsApp n args (TyADT "Loc"))
                                                     "xEnv" -> do
                                                                  args <- mapM tcExpr args_
                                                                  if length args /= 3
                                                                     then errWrongNumArgs n 3 (length args)
                                                                     else do
                                                                       let [argRho,argName,argLoc] = args
                                                                           tyRho                   = typeOf argRho
                                                                           tyName                  = typeOf argName
                                                                           tyLoc                   = typeOf argLoc
                                                                       
                                                                       unifyOrDie n 1 tyRho (TyADT "Env")
                                                                       unifyOrDie n 2 tyName TyString
                                                                       unifyOrDie n 3 tyLoc (TyADT "Loc")
                                                                       return (CtsApp n args (TyADT "Env"))
                                                     "emptyEnv" -> do
                                                                      args <- mapM tcExpr args_
                                                                      if length args /= 0
                                                                         then errWrongNumArgs n 0 (length args)
                                                                         else inferSpecial (CtsVar n TyUnit)
                                                     "head"     -> do
                                                                      args <- mapM tcExpr args_
                                                                      if length args /= 1
                                                                         then errWrongNumArgs n 1 (length args)
                                                                         else do
                                                                           let [argList] = args
                                                                           case typeOf argList of
                                                                              (TyList tb) -> return (CtsApp n args tb)
                                                                              _           -> typeError $ n ++ ": argument type "
                                                                                                           ++ showType (typeOf argList) ++ " is not a list"
typeError :: String -> TCM a
typeError e = do
                 pos <- rdSrcPosTCM
                 throwTypeErrorTCM $ show pos ++ ": Type error: " ++ e

mkBindEnv :: CtsDecl -> FunSpec -> BindEnv
mkBindEnv (CtsFunDecl _ _ argNames _) funSpec    = let
                                                      argTys = funSpecArgTys funSpec
                                                   in
                                                      zipWith Binding argNames argTys

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

--
-- desugar type synonyms,
-- i.e. replace all type synonyms with their declared
-- base types in a list of type signatures
--
-- List in first arg is combined type synonyms, data declarations
--
-- Second arg is list of all function type signitures
--
-- 25.06.09 Schulz
--

desugarTypes :: [CtsDecl] -> [CtsDecl] -> [CtsDecl]
desugarTypes datas decs =
  let desyns = desugarDatas datas datas [ ]

      -- lookup a type synonym, or kick back the argument
      -- if it is (1) not an ADT or (2) an ADT that is not a type synonym
      lkp ty = case ty of
                 (TyADT n) -> let xs = dropWhile
                                       (\d ->
                                         case d of
                                           (CtsDataDecl c n' t') ->  n /= n'
                                           _                     ->  True)
                                       desyns
                              in
                              case xs of
                                ((CtsDataDecl _ _ [(CtsConDecl "" [ty'])]):_) -> ty'
                                ((CtsDataDecl _ _ _):_)                       -> ty
                                _                                             -> error ": in local function lkup in desugarDatas"

                 (TyTuple tys)      -> (TyTuple $ map lkp tys)
                 (TyList ty)        -> (TyList $ lkp ty)
                 (TyMonadic n ty)   -> (TyMonadic n $ lkp ty)
                 _                  -> ty


      -- rewrite a type signiture with reduced types:
      rw (CtsFunTySig c n args ret) ds = 
        let ats  = map (\t -> if isBase t then t else lkp t) args
            nret = lkp ret
        in
          (CtsFunTySig c n ats nret):ds
  in
    foldr rw [ ] decs

--
-- ... first reducing all type/data declarations
-- to declarations that involve no type synonyms
--
-- first argument is a list of all decs, used for lookup
-- second argument is list of unreduced decs
-- third argument is an accumulator
--

desugarDatas :: [CtsDecl] -> [CtsDecl] -> [CtsDecl] -> [CtsDecl]
desugarDatas decs ((CtsDataDecl c n cdecs):datas) red =
  let
      -- lookup a type synonym, or kick back the argument
      -- if it is (1) not an ADT or (2) an ADT that is not a type synonym
      lkp ty = case ty of
                 (TyADT n) -> let xs = dropWhile
                                       (\d ->
                                         case d of
                                           (CtsDataDecl c n' t') ->  n /= n'
                                           _                     ->  True)
                                       decs
                              in
                              case xs of
                                ((CtsDataDecl _ _ [(CtsConDecl "" [ty'])]):_) -> ty'
                                ((CtsDataDecl _ _ _):_)                       -> ty
                                _                                             -> error ": in local function lkup in desugarDatas"

                 (TyTuple tys)      -> (TyTuple $ map lkp tys)
                 (TyList ty)        -> (TyList $ lkp ty)
                 (TyMonadic n ty)   -> (TyMonadic n $ lkp ty)
                 _                  -> ty


      -- reduce the types in a constructor declaration:
      redcon (CtsConDecl n tys) = (CtsConDecl n $ map lkp tys)
  in
    desugarDatas decs datas ((CtsDataDecl c n $ map redcon cdecs):red)

desugarDatas _ [ ] red = red


--
-- base types
--
-- 25.06.09 Schulz
--
isBase :: CtsType -> Bool
isBase TyInt = True
isBase TyBool = True
isBase TyString = True
isBase TyUnit = True
isBase (TyTuple ts) = foldr ((&&) . isBase) True ts
isBase (TyList t) = isBase t
isBase (TyMonadic _ t) = isBase t
isBase _ = False


--
-- Adam's (effective) top-level call to the type-checker:
--
tcProg :: CtsProg -> TCM CtsProg
tcProg (CtsProg decls) = do
                            let monadDecls = filter isMonadDecl decls
                                dataDecls  = filter isDataDecl decls
                                --tySigs     = filter isTySig decls
                                -- tySigs     = desugarTypes tySyns $ filter isTySig decls  -- 25.06.09 Schulz
                                tySigs    = desugarTypes dataDecls $ filter isTySig decls  -- 29.06.09 Schulz
                                
                                isMonadDecl (CtsMonadDecl _ _ _) = True
                                isMonadDecl _                    = False
                                isDataDecl (CtsDataDecl _ _ _)   = True
                                isDataDecl _                     = False
                                isTySig (CtsFunTySig _ _ _ _)    = True
                                isTySig _                        = False
                                
                                mkDataSpec (CtsDataDecl p n cs)          = DTSpec { dtSpecName = n, dtSpecCtors = cs }
                                mkFunSpec (CtsFunTySig _ f argTys retTy) = FunSpec { funSpecName = f, funSpecArgTys = argTys, funSpecRetTy = retTy }
                                
                                monadEnv = concatMap mkMonadNPMs monadDecls
                                dtEnv    = map mkDataSpec dataDecls
                                funEnv   = map mkFunSpec tySigs
                                
                            decls' <- inMonadEnvTCM monadEnv $ inDTEnvTCM dtEnv $ inFunEnvTCM funEnv $ tcDecls decls
                            return $ CtsProg decls'
  where
    tcDecls :: [CtsDecl] -> TCM [CtsDecl]
    tcDecls (d@(CtsFunDecl p f a body):decls)    = inSrcPosTCM p $
                                                    do
                                                      funEnv      <- rdFunEnvTCM
                                                      
                                                      let mFunSpec = lookupBy funSpecName f funEnv
                                                      
                                                      if isNothing mFunSpec
                                                        then typeError $ "No type signature given for function " ++ f
                                                        else do
                                                          let funSpec =  fromJust $ lookupBy funSpecName f funEnv
                                                              bindEnv =  mkBindEnv d funSpec
                                                          body'       <- inBindEnvTCM bindEnv (tcExpr body)
                                                          case unify (typeOf body') (funSpecRetTy funSpec) of
                                                             Nothing   -> typeError $ "Inferred return type " ++
                                                                                      showType (typeOf body') ++
                                                                                      " does not match declared return type " ++
                                                                                      showType (funSpecRetTy funSpec)
                                                             (Just ty) -> do
                                                                rest  <- tcDecls decls
                                                                return ((CtsFunDecl p f a body'):rest)
    tcDecls (d@(CtsRecDecl ds):decls)            = do
                                                     ds'  <- tcDecls ds
                                                     rest <- tcDecls decls
                                                     return ((CtsRecDecl ds'):rest)
    tcDecls (d:decls)                            = do
                                                     rest <- tcDecls decls
                                                     return (d:rest)
    tcDecls []                                   = return []

mkKappa :: CtsIdent -> [CtsType] -> Kappa
mkKappa k argTys = Kappa { kappaName = k, kappaArgTys = argTys }

isArithOp :: CtsIdent -> Bool
isArithOp "+" = True
isArithOp "-" = True
isArithOp "^" = True
isArithOp _   = False

isCompareOp :: CtsIdent -> Bool
isCompareOp "<"  = True
isCompareOp ">"  = True
isCompareOp "==" = True
isCompareOp "/=" = True
isCompareOp "<=" = True
isCompareOp ">=" = True
isCompareOp _    = False

tcExpr :: CtsExpr -> TCM CtsExpr
tcExpr (CtsInfixApp e1_ op e2_ _) | isArithOp op = do
                                        e1 <- tcExpr e1_
                                        e2 <- tcExpr e2_
                                             
                                        let te1 = typeOf e1
                                            te2 = typeOf e2
                                              
                                        case (te1,te2) of
                                           (TyInt,TyInt) -> return (CtsInfixApp e1 op e2 TyInt)
                                           _             -> typeError $ "(" ++ op ++ "): Inferred operand types " ++ showType te1 ++
                                                                        " and " ++ showType te2 ++ " do not match expected" ++
                                                                        " types Int and Int"
                                  | isCompareOp op = do
                                        e1 <- tcExpr e1_
                                        e2 <- tcExpr e2_
                                             
                                        let te1 = typeOf e1
                                            te2 = typeOf e2
                                              
                                        case (te1,te2) of
                                           (TyInt,TyInt) -> return (CtsInfixApp e1 op e2 TyBool)
                                           _             -> typeError $ "(" ++ op ++ "): Inferred operand types " ++ showType te1 ++
                                                                        " and " ++ showType te2 ++ " do not match expected" ++
                                                                        " types Int and Int"
                                                                        
                                  | op == ":" = do
                                        e1 <- tcExpr e1_
                                        e2 <- tcExpr e2_
                                        
                                        let te1 = typeOf e1
                                            te2 = typeOf e2
                                            
                                        case te2 of
                                           (TyList tBase) -> case unify te1 tBase of
                                                                Nothing   -> typeError $ "(:): Left operand type " ++ showType te1 ++
                                                                                         " does not match expected type " ++ showType tBase
                                                                (Just tU) -> return $ CtsInfixApp e1 op e2 (TyList tU)
                                           _              -> typeError $ "(:): Right operand type " ++ showType te2 ++ " is not a list type"
                                                                        
tcExpr (CtsNeg e_ _)               = do
                                        e <- tcExpr e_
                                        
                                        let te = typeOf e

                                        case te of
                                           TyInt -> return (CtsNeg e TyInt)
                                           _     -> typeError $ "Negation: Inferred operand type " ++
                                                                showType te ++ " does not match" ++
                                                                " expected type Int"

                                                                
tcExpr (CtsTuple es_ _)            = do
                                        es <- mapM tcExpr es_
                                             
                                        return $ CtsTuple es (TyTuple (map typeOf es))
                                        
tcExpr (CtsList es_ _)               = do
                                          es <- mapM tcExpr es_
                                          
                                          if null es
                                            then typeError "Can't assign a type to an empty list (FIXME!!!)"
                                            else case foldM unify (typeOf (head es)) (map typeOf (tail es)) of
                                               (Just t) -> return (CtsList es (TyList t))
                                               Nothing  -> typeError "Types of list elements do not match"

tcExpr (CtsLitExpr (CtsLitInt i) _)  = return (CtsLitExpr (CtsLitInt i) TyInt)

tcExpr (CtsLitExpr (CtsLitBool b) _) = return (CtsLitExpr (CtsLitBool b) TyBool)

tcExpr (CtsLitExpr (CtsLitString s) _) = return (CtsLitExpr (CtsLitString s) TyString)

tcExpr (CtsIfThenElse e_ t_ f_ _)  = do
                                        e <- tcExpr e_
                                        t <- tcExpr t_
                                        f <- tcExpr f_
                                        
                                        let te = typeOf e
                                            tt = typeOf t
                                            tf = typeOf f
                                        
                                        case te of
                                           TyBool -> case (unify tt tf) of
                                                        Nothing   -> typeError $ "if/then/else: Types " ++ showType tt ++
                                                                                 " of 'then' branch and " ++ showType tf ++
                                                                                 " of 'else' branch do not match"
                                                        (Just tu) -> return $ CtsIfThenElse e t f tu
                                           _      -> typeError $ "if/then/else: Type " ++ showType te ++ "of condition " ++
                                                                 " does not match expected type Bool"


tcExpr (CtsUnit _)                 = return (CtsUnit TyUnit)

tcExpr (CtsEmptyList t)   = case t of
                               (TyList _) -> return (CtsEmptyList t)
                               _          -> typeError $ "[]: Explicit type " ++ showType t ++ " is not a list type"

tcExpr e@(CtsVar ident _) = do
                               special <- isSpecial e

                               if special
                                  then inferSpecial e
                                  else do
                                     bindEnv <- rdBindEnvTCM
                                              
                                     if ident `elem` (map bindingName bindEnv)
                                        then do
                                           let binding = fromJust (lookupBy bindingName ident bindEnv)

                                           return $ CtsVar ident (bindingTy binding)
                                           else do
                                             funEnv <- rdFunEnvTCM
                                             kappa  <- rdKappaTCM
                                                        
                                             if ident `elem` (map funSpecName funEnv)
                                                || (isJust kappa && kappaName (fromJust kappa) == ident)
                                                then tcExpr $ CtsApp ident [] noType
                                                else typeError $ "Unbound variable: " ++ ident

tcExpr e@(CtsApp f args_ _) = do
                                 kappa <- rdKappaTCM
                                             
                                 if isJust kappa && kappaName (fromJust kappa) == f
                                    then do
                                       let argTys = kappaArgTys (fromJust kappa)
                                           -- FIXME: This should not be hard-coded but there's a need for type reconstruction if we do things the Right Way.
                                           -- (Should be perfectly feasible, but I'm too lazy at the moment.)
                                           retTy  = (TyMonadic "Re" (TyADT "V"))
                                                 
                                       args <- mapM tcExpr args_
                                                 
                                       if length argTys /= length args || any isNothing (zipWith unify argTys (map typeOf args))
                                          then typeError $ "Applying function " ++ f ++ ": inferred" ++
                                                           " argument types " ++ intercalate "," (map (showType . typeOf) args) ++
                                                           " do not match expected types " ++
                                                           intercalate "," (map showType argTys)
                                          else return (CtsApp f args retTy)
                                    else do
                                       funEnv <- rdFunEnvTCM
                                       if f `elem` map funSpecName funEnv
                                          then do
                                             let funSpec =  fromJust $ lookupBy funSpecName f funEnv
                                                 argTys  =  funSpecArgTys funSpec
                                                 retTy   =  funSpecRetTy  funSpec

                                             args        <- mapM tcExpr args_

                                             if length argTys /= length args || any isNothing (zipWith unify argTys (map typeOf args))
                                                then typeError $ "Applying function " ++ f ++ ": inferred" ++
                                                                 " argument types " ++ intercalate "," (map (showType . typeOf) args) ++
                                                                 " do not match expected types " ++
                                                                 intercalate "," (map showType argTys)
                                                else return (CtsApp f args retTy)
                                          else do
                                             special <- isSpecial e
                                 
                                             if special
                                                then inferSpecial e
                                                else typeError $ "Undeclared function " ++ f

tcExpr (CtsFixApp ns body_ args_ _) = do
                                         args         <- mapM tcExpr args_
                                         bindEnv      <- rdBindEnvTCM

                                         -- FIXME: Check to make sure #args matches #ns - 1
                                         let argTys   =  map typeOf args
                                             kappa    =  mkKappa (head ns) argTys
                                             bindEnv' =  (zipWith Binding (tail ns) argTys) ++ bindEnv
                                         body         <- inBindEnvTCM bindEnv' $ inKappaTCM (Just kappa) (tcExpr body_)

                                         return $ CtsFixApp ns body args (typeOf body)

tcExpr (CtsSemiFixApp cond ns body_ args_ _) = do
                                               args         <- mapM tcExpr args_
                                               bindEnv      <- rdBindEnvTCM

                                               -- FIXME: Check to make sure #args matches #ns - 1
                                               let argTys   =  map typeOf args
                                                   kappa    =  mkKappa (head ns) argTys
                                                   bindEnv' =  (zipWith Binding (tail ns) argTys) ++ bindEnv
                                               body         <- inBindEnvTCM bindEnv' $ inKappaTCM (Just kappa) (tcExpr body_)
 
                                               return $ CtsSemiFixApp cond ns body args (typeOf body)

tcExpr (CtsConstrApp ctor args_ t) = do
                                        dtEnv         <- rdDTEnvTCM
                                        args          <- mapM tcExpr args_

                                        let mConDecl  =  getConDecl ctor dtEnv
                                        
                                        if isNothing mConDecl then

                                          -- this is a temporary work-around; (2009.12.14) Schulz
                                          -- return (unsafePerformIO $ putStrLn $ "WARNING: type of " ++ (show mConDecl) ++ " is being ignored\n") >>
                                               return $ CtsConstrApp ctor args t
 
--                                          then typeError $ "Undeclared data constructor " ++ ctor

                                          else do
                                            let conDecl                   = fromJust mConDecl
                                                (CtsConDecl _ conDeclTys) = conDecl
                                                argTys                    = map typeOf args
                                              
                                            if length conDeclTys /= length args || any isNothing (zipWith unify argTys conDeclTys)
                                               then typeError $ "Applying constructor " ++ ctor ++ ":" ++
                                                                " argument types " ++ intercalate "," (map showType argTys) ++
                                                                " do not match expected types " ++
                                                                intercalate "," (map showType conDeclTys)
                                               else do
                                                 let dtSpec = fromJust $ getDTSpecByCtor ctor dtEnv
                                                 return $ CtsConstrApp ctor args (TyADT $ dtSpecName dtSpec)

tcExpr (CtsCase e_ alts_ _)        = do
                                        e <- tcExpr e_
                                              
                                        let tyIsADT (TyADT _)     = True
                                            tyIsADT _             = False
                                          
                                            tyIsTuple (TyTuple _) = True
                                            tyIsTuple _           = False
                                              
                                        if not (tyIsTuple (typeOf e) || tyIsADT (typeOf e))
                                           then typeError $ "Scrutinee type " ++ showType (typeOf e) ++
                                                                " is not a tuple or a `data' type" 
                                           else do
                                             alts <- mapM (inferAlt (typeOf e)) alts_
                                             let typeOfAlt (CtsAlt _ ae) = typeOf ae
                                                 tAlts                   = map typeOfAlt alts
                                                 mUniTy                  = foldM unify (head tAlts) (tail tAlts)
                                             if not (null tAlts) && isNothing mUniTy
                                                then typeError $ "Case type mismatch (FIXME -- lousy error message)"
                                                else return $ CtsCase e alts (fromJust mUniTy)

--
-- Monad stuff
--

--
-- FIXME: cases for bind and bindnull need to be rewritten
--

tcExpr (CtsBind e1_ n e2_ _)       = do
                                             e1      <- tcExpr e1_
                                             let te1 =  typeOf e1
                                             if not (tyIsMonadic te1)
                                               then typeError $ "Type " ++ showType te1 ++ " of left side of bind is not monadic"
                                               else do
                                                 let (TyMonadic m1 t1) = te1
                                                 bindEnv <- rdBindEnvTCM
                                                 let bindEnv' = Binding { bindingName = n, bindingTy = t1 } : bindEnv
                                                 e2      <- inBindEnvTCM bindEnv' (tcExpr e2_)
                                                 let te2 =  typeOf e2
                                                 if not (tyIsMonadic te2)
                                                   then typeError $ "Type " ++ showType te2 ++ " of right side of bind is not monadic"
                                                   else do
                                                     let (TyMonadic m2 t2) = te2
                                                     if m1 == "m" || m1 == m2
                                                       then return $ (CtsBind e1 n e2 (TyMonadic m2 t2))
                                                       else if m2 == "m"
                                                         then return $ (CtsBind e1 n e2 (TyMonadic m1 t2))
                                                         else typeError $ "(>>=): monadic types " ++ showType te1 ++ " and " ++ showType te2 ++ " do not match"

tcExpr (CtsBindNull e1_ e2_ _)     = do
                                             e1      <- tcExpr e1_
                                             let te1 =  typeOf e1
                                             if not (tyIsMonadic te1)
                                               then typeError $ "Type " ++ showType te1 ++ " of left side of bind is not monadic"
                                               else do
                                                 let (TyMonadic m1 t1) = te1
                                                 e2      <- tcExpr e2_
                                                 let te2 =  typeOf e2
                                                 if not (tyIsMonadic te2)
                                                   then typeError $ "Type " ++ showType te2 ++ " of right side of bind is not monadic"
                                                   else do
                                                     let (TyMonadic m2 t2) = te2
                                                     if m1 == "m" || m1 == m2
                                                       then return $ (CtsBindNull e1 e2 (TyMonadic m2 t2))
                                                       else if m2 == "m"
                                                         then return $ (CtsBindNull e1 e2 (TyMonadic m1 t2))
                                                         else typeError $ "(>>): monadic types " ++ showType te1 ++ " and " ++ showType te2 ++ " do not match"

tcExpr (CtsReturn e_ _)            = do
                                        e <- tcExpr e_
                                        return $ CtsReturn e (TyMonadic "m" (typeOf e))
                                                
tcExpr e                           = typeError $ "Type checker does not know how to handle this: " ++ show e
                                        
inferAlt :: CtsType -> CtsAlt -> TCM CtsAlt
inferAlt ty (CtsAlt (CtsPConstr ctor ns) e_) = do
                                                  case ty of
                                                     (TyADT tn) -> do
                                                        dtEnv      <- rdDTEnvTCM
                                                        -- FIXME: fromJust
                                                        let dtSpec =  fromJust $ lookupBy dtSpecName tn dtEnv
                                                        if not (ctor `elem` (map conDeclName (dtSpecCtors dtSpec)))
                                                           then typeError "ctor mismatch (FIXME)"
                                                           else do
                                                              -- FIXME: Check number of vars
                                                              let conDecl     =  fromJust $ getConDecl ctor dtEnv
                                                                  newBindings =  zipWith Binding ns (conDeclTys conDecl)
                                                              bindEnv         <- rdBindEnvTCM
                                                              e               <- inBindEnvTCM (newBindings++bindEnv) (tcExpr e_)
                                                              return (CtsAlt (CtsPConstr ctor ns) e)
                                                     _          -> typeError "not TyADT (FIXME)"
inferAlt ty (CtsAlt (CtsPTuple ns) e_)       = do
                                                  case ty of
                                                     (TyTuple ts) -> do
                                                        -- FIXME: check number of vars
                                                        let newBindings =  zipWith Binding ns ts
                                                        bindEnv         <- rdBindEnvTCM
                                                        e               <- inBindEnvTCM (newBindings++bindEnv) (tcExpr e_)
                                                        return (CtsAlt (CtsPTuple ns) e)
                                                     _            -> typeError "not TyTuple (FIXME)"

-- Seems weird that there's no prelude function for this
lookupBy :: (Eq b) => (a -> b) -> b -> [a] -> Maybe a
lookupBy f k xs = lookup k [(f x,x) | x <- xs]

tyIsMonadic :: CtsType -> Bool
tyIsMonadic (TyMonadic _ _) = True
tyIsMonadic _               = False

conDeclName :: CtsConDecl -> CtsIdent
conDeclName (CtsConDecl n _) = n

conDeclTys :: CtsConDecl -> [CtsType]
conDeclTys (CtsConDecl _ tys) = tys

getConDecl :: CtsIdent -> DTEnv -> Maybe CtsConDecl
getConDecl n (dt:dts) = lookupBy conDeclName n (dtSpecCtors dt) `mplus` getConDecl n dts
getConDecl _ []       = Nothing

getDTSpecByCtor :: CtsIdent -> DTEnv -> Maybe DTSpec
getDTSpecByCtor n dts = listToMaybe $ filter (isJust . lookupBy conDeclName n . dtSpecCtors) dts
