--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/Compiler/CodeGen.2010.05.20.hs
--
-- The old version of Adam's CT-to-ETIC code generation module,
-- frozen for future generations
--
-- put here 2010.05.20
--
-- Schulz
--
module CT.Compiler.Codegen where

import CT.Syntax as C
import CT.Uncase
import CT.INAST
import CT.MonadicConstructions hiding (rdEnv,inEnv)
import qualified CT.MonadicConstructions
import ETIC.Syntax as E
import qualified ETIC.Print
import qualified Control.Monad.Identity
import Control.Monad

type Label   = String
type Ident   = String
type Reg     = String
type Env     = Ident -> Binding
data Binding = RegBinding Reg | KappaBinding Label [Reg] deriving Show

--------------------
--------------------
-- Compiler monad --
--------------------
--------------------
type M       = StateT Int (EnvT (Env,Bool) Id)

prj :: M a -> a
prj (ST s) = fst $ deId $ (deENV (s initst)) initenv
               where initenv = (\x -> RegBinding (dummyreg ++ "(((FIXME: Reference to unbound variable " ++ x ++ ")))"),False)
                     initst  = 0

rdM :: M (Env,Bool)
rdM = liftSt CT.MonadicConstructions.rdEnv

inM :: (Env,Bool) -> M a -> M a
inM env m = ST (\s -> (CT.MonadicConstructions.inEnv env (deST m s)))

rdEnv :: M Env
rdEnv = rdM >>= return . fst

rdStThread :: M Bool
rdStThread = rdM >>= return . snd

inEnv :: Env -> M a -> M a
inEnv env m = rdStThread >>= \ stThread ->
              inM (env,stThread) m

inStThread :: Bool -> M a -> M a
inStThread stThread m = rdEnv >>= \ env ->
                      inM (env,stThread) m

-------------------------------------
-------------------------------------
-- Miscellaneous Support Functions --
-------------------------------------
-------------------------------------
genLabel :: M String
genLabel = get      >>= \ c ->
           upd (+1) >>
             return ("l" ++ show c)

genReg :: M String
genReg = get      >>= \ c ->
         upd (+1) >>
           return ("r" ++ show c)

tweek :: Env -> Ident -> Binding -> Env
tweek env r b = \ r' -> if r' == r then b else env r'

xEnv :: Env -> [Ident] -> [Binding] -> Env
xEnv env (i:is) (b:bs) = tweek (xEnv env is bs) i b
xEnv env []     []     = env

--
-- a 'unit' register having a constant value;
-- assignments can be made to this, but they
-- should have no effect, e.g. this works
-- like 'r0' in Microblaze
--
-- (2010.05.19) Schulz
--
r_unit :: Reg
r_unit = "UNIT_R"

-----------------------------------------------------
-----------------------------------------------------
-- Miscellaneous rollings/unrollings we have to do --
-----------------------------------------------------
-----------------------------------------------------
uncurryLam :: INAST -> ([Ident],INAST)
uncurryLam (CTLamIN x e _) = let (idents,e') = uncurryLam e in (x:idents,e')
uncurryLam e               = ([],e)

uncurryApp :: INAST -> [INAST]
uncurryApp (CTAppIN f e _)    = uncurryApp f ++ [e]
uncurryApp (CTRecAppIN f e _) = uncurryApp f ++ [e]
uncurryApp e                  = [e]


curryType :: CTTy -> ([CTTy],CTTy)
curryType (CTAbsTy t1 t2) = let
                               (ts,r) = curryType t2
                            in
                               (t1:ts,r)
curryType t               = ([],t)

-----------------------
-----------------------
-- Type Translations --
-----------------------
-----------------------
trTy :: CTTy -> Type
trTy CTIntTy                   = TyInt
trTy CTBoolTy                  = TyBool
trTy CTCharTy                  = TyChar
trTy CTStringTy                = TyUserDef "__UntranslatableString"
trTy CTUnitTy                  = TyUserDef "__UntranslatableUnit"
trTy (CTTyVar v)               = TyUserDef $ "__UntranslatableTyVar" ++ v
trTy (CTAbsTy t1 t2)           = TyUserDef $ "__UntranslatableArrow"
trTy (CTConTy (TyCon ctor) []) = TyUserDef ctor
trTy (CTConTy (TyCon ctor) _)  = error $ "Cannot translate higher-kinded type constructor " ++ ctor

--
-- stubbed, just to see what's going through elsewhere
--
-- (2010.05.19) Schulz
trTy (CTListTy _)              = TyUserDef $ "__UntranslateableList"
--trTy (CTListTy _)              = error "Cannot translate list types"
--

trTy (CTMTy ResTy _)           = TyUserDef "__TCB"
trTy (CTMTy (ReactTy _ _) _)   = TyUserDef "__React"
trTy (CTMTy StateTy _)         = TyUserDef "__State"

-- yet another (2010.05.19) Schulz
trTy (CTMTy (MVar _) _)        = TyUserDef "__Monadic"
--trTy (CTMTy (MVar _) _)        = error "Cannot translate variable functor types"
--
trTy (CTPairTy t1 t2)          = TyPair (trTy t1) (trTy t2)
trTy (CTReqTy _ _)             = TyUserDef "__Req"
trTy (CTRspTy _ _)             = TyUserDef "__Rsp"


----------------------------
----------------------------
-- Main Codegen Functions --
----------------------------
----------------------------

compileThread :: INAST -> M (Reg,[Stmt])
compileThread = inStThread True . compile

compileNoThread :: INAST -> M (Reg,[Stmt])
compileNoThread = inStThread False . compile

compileFunDec :: INFunDec -> M TopDecl
compileFunDec (INFunDec ((name,ty),(argNames,body))) =
    let
       (argTys,resultTy) = curryType ty
    in
       rdEnv    >>= \ env ->
       let env' = xEnv env argNames (map RegBinding argNames)
       in  inEnv env' (compile body) >>= \ (r_body,pi_body) ->
           case resultTy of
             (CTMTy _ t) -> return (FunDecl (Just (trTy t)) name (zip (map trTy argTys) argNames) [] (pi_body++[Return (FunCall "__run" [Var r_body])]))
             t           -> return (FunDecl (Just (trTy t)) name (zip (map trTy argTys) argNames) [] (pi_body++[Return (Var r_body)]))

compileProg :: INProg -> M Prog
compileProg (INProg ((mainDec,otherFunDecs),(dataDecs,monadDecs))) =
    mapM compileFunDec (mainDec:otherFunDecs) >>= \ fundecls ->
    mapM compileDataDec dataDecs              >>= \ uniondecls ->
    mapM compileMonadDec monadDecs            >>= \ statevardeclss ->
    return (Prog (uniondecls++concat statevardeclss++fundecls))

compileCtorDec :: (TyCon,[CTTy]) -> (String,[Type])
compileCtorDec (TyCon n,tys) = (n,map trTy tys)

compileDataDec :: DataDec -> M TopDecl
compileDataDec (DataDec (TyCon dtname) [] ctordecs) =
    return (UnionDecl dtname (map compileCtorDec ctordecs))
compileDataDec (DataDec _ _ _) = error "Can't handle parameterized data declarations"
compileDataDec (SigDec _ _)    = return $ TopVarDecl (VarDecl [] TyInt "FIXMESIGDEC" Nothing) --error "SigDec not implemented yet"



compileStateLayer :: (StateLT, (CTIdent, CTTy)) -> M TopDecl
compileStateLayer (StateL, (n,ty)) = return (TopVarDecl (VarDecl [] (trTy ty) n Nothing))

compileStateLayer (MemL n, (x, t)) = return $
                                       TopVarDecl $ 
                                         VarDecl [] (TyArray n (trTy t)) x
                                           Nothing




compileMonadDec :: MonadDec -> M [TopDecl]
compileMonadDec (CTStateT _ layers) = mapM compileStateLayer layers
compileMonadDec _                   = return []

compile :: INAST -> M (Reg,[Stmt])

---------------
-- Functions --
---------------
compile ap@(CTAppIN _ _ _) = mapM compileThread args >>= \ results ->
                             rdEnv                   >>= \ env ->

                             let regs = map fst results
                                 pis  = map snd results
                             in
                               case f of
                                 lam@(CTLamIN _ _ _) -> let (vars,body) = uncurryLam lam
                                                            rho         = xEnv env vars (map RegBinding regs)
                                                        in  inEnv rho (compileNoThread body) >>= \ (r_body, pi_body) ->
                                                            return (r_body,concat pis ++ pi_body)
                                 (CTVarIN k _) -> case env k of
                                                    (KappaBinding klabel kregs) ->
                                                        return (dummyreg,

                                                                concat pis ++
                                                                zipWith (\ r kr -> Assign (LHSVar kr) (Var r)) regs kregs ++
                                                                [Jump klabel])
--                                                    (RegBinding _)              -> error $ "Can't apply named function " ++ k
                                                    (RegBinding _) -> return (dummyreg,concat pis ++ [Jump "durrr"]) -- FIXME
                             where
                               (f:args) = uncurryApp ap

compile (CTFixAppIN
            (CTFixIN (CTLamIN k lam _) _)
            args ty)                      = mapM compileThread args >>= \ results ->
                                            rdEnv                   >>= \ env ->
                                            genLabel                >>= \ label ->
                                            let regs        = map fst results
                                                pis         = map snd results
                                                (vars,body) = uncurryLam lam
                                                env'        = tweek env k (KappaBinding label regs)
                                                rho         = xEnv env' vars (map RegBinding regs)
                                            in inEnv rho (compileNoThread body) >>= \ (r_body, pi_body) ->
                                               return (r_body,concat pis ++ [Loop label (pi_body++[ExprStmt (FunCall "__FIXMEBREAKLOOP" [])])])


compile (CTRecAppIN f e ty) = compile (CTAppIN f e ty)
-- By "orphaned" I mean it's not handled in the context of an application or a bind.
compile e@(CTLamIN _ _ _) = error $ "Orphaned CTLamIN: " ++ show e

-------------------------
-- Monadic Expressions --
-------------------------
compile (CTBindIN e (CTLamIN x f _) _) = compileNoThread e             >>= \ (r_e,pi_e) ->
                                         rdEnv                         >>= \ env ->
                                         inEnv
                                          (tweek env x (RegBinding r_e))
                                          (compileNoThread f)          >>= \ (r_f,pi_f) ->
                                         rdStThread                    >>= \ stThread ->
                                             if stThread
                                              then
                                               genReg       >>= \ r_result ->
                                               return (r_result,[DeclStmt (VarDecl [] (TyUserDef "__TCB") r_result (Just (MkThread (pi_e++pi_f++[Return (Var r_f)]))))])
                                              else
                                               return (r_f,pi_e++pi_f)
compile (CTNullBindIN e1 e2 _)         = compileNoThread e1 >>= \ (_,pi_e1) ->
                                         compileNoThread e2 >>= \ (r_e2,pi_e2) ->
                                         rdStThread         >>= \ stThread ->
                                             if stThread
                                              then
                                               genReg >>= \ r_result ->
                                               return (r_result,[DeclStmt (VarDecl [] (TyUserDef "__TCB") r_result (Just (MkThread (pi_e1++pi_e2++[Return (Var r_e2)]))))])
                                              else
                                               return (r_e2,pi_e1++pi_e2)
compile (CTReturnIN e _)               = compileThread e >>= \ (r_e,pi_e) ->
                                         rdStThread        >>= \ stThread ->
                                             if stThread
                                              then
                                               genReg                     >>= \ r_result ->
                                               return (r_result,[DeclStmt (VarDecl [] (TyUserDef "__TCB") r_result (Just (MkThread (pi_e++[Return (Var r_e)]))))])
                                              else
                                               return (r_e,pi_e)

------------------------
-- Stateful Operators --
------------------------
compile (CTGetIN n ty)      = genReg >>= \r ->
                              return (r, [Assign (LHSVar r) (Var n)])

compile (CTPutIN n e _)     = compile e >>= \(r_e, p) ->
                              return
                                (r_unit,
                                  p ++ [Assign (LHSVar n) (Var r_e)])

compile (CTReadIN x i ty)   = genReg >>= \r ->
                              compile i >>= \(r_i, p) ->
                              return
                                (r,
                                  p ++
                                    [Assign (LHSVar r) (VarIX x (Var r_i))])

compile (CTWriteIN x i e _) = compile e >>= \(r_e, p) ->
                              compile i >>= \(r_i, p') ->
                              return
                               (r_unit,
                                 p ++ p' ++ 
                                   [Assign (LHSVarIX x (Var r_i)) (Var r_e)])



--------------------------
-- Resumptive Operators --
--------------------------
compile (CTStepIN phi _)  = compileThread phi >>= \ (r_phi,pi_phi) ->
                            rdStThread        >>= \ stThread ->
                            genReg            >>= \ r_result ->
                            if stThread
                             then
                              return (r_result,
                                      pi_phi++[DeclStmt (VarDecl [] (TyUserDef "__TCB") r_result (Just (MkThread [Return (FunCall "__slice" [Var r_phi])])))])
                             else
                              return (r_result,
                                      pi_phi++[DeclStmt (VarDecl [] (TyUserDef "__TCB") r_result (Just (FunCall "__slice" [Var r_phi])))])

-----------------------------------
-- Reactive-Resumption Operators --
-----------------------------------
compile (CTSignalIN e _) = compileThread e >>= \ (r_e,pi_e) ->
                           genReg          >>= \ r_res ->
                           return (r_res,pi_e ++ [Assign (LHSVar ("the_request")) (Var r_e),
                                                  ExprStmt (FunCall "__FIXMEJUMPTOHANDLER" []),
                                                  DeclStmt (VarDecl [] (TyUserDef "__FIXMERSP") r_res (Just (Var "the_result")))])

--------------------------
-- Primitive Operations --
--------------------------
compile (CTPrim1aryIN op e ty)    = compileThread e >>= \ (r_e,pi_e) ->
                                    genReg          >>= \ r_res ->
                                    return (r_res,pi_e ++ [DeclStmt (VarDecl [] (trTy ty) r_res
                                                                     (Just (opDenote op (Var r_e))))])
                                    where opDenote (Un CTNeg) = Neg
                                          opDenote (Un CTNot) = Not
                                          opDenote (Un Fst)   = error $ "Tuples not supported yet"
                                          opDenote (Un Snd)   = error $ "Tuples not supported yet"
                                          opDenote o          = error $ "Unknown unary operator " ++ show o
compile (CTPrim2aryIN op e1 e2 ty) = compileThread e1 >>= \ (r_e1,pi_e1) ->
                                     compileThread e2 >>= \ (r_e2,pi_e2) ->
                                     genReg           >>= \ r_res ->
                                     return (r_res,pi_e1 ++ pi_e2 ++ [DeclStmt (VarDecl [] (trTy ty) r_res
                                                                                (Just (opDenote op (Var r_e1) (Var r_e2))))])
                                     where opDenote (Bin CTPlus)     = Add
                                           opDenote (Bin CTMinus)    = Sub
                                           opDenote (Bin CTMult)     = Mul
                                           opDenote (Bin CTIDiv)     = Div
                                           opDenote (Bin CTAnd)      = AndLogic
                                           opDenote (Bin CTOr)       = OrLogic
                                           opDenote (Bin CTEqTest)   = IsEq
                                           opDenote (Bin CTIneqTest) = NotEq
                                           opDenote (Bin CTLTTest)   = IsLT
                                           opDenote (Bin CTGTTest)   = IsGT
                                           opDenote (Bin CTLTETest)  = IsLTE
                                           opDenote (Bin CTGTETest)  = IsGTE
                                           opDenote (Bin CTCons)     = \ e1 e2 ->
                                                                         FunCall "FIXMECONS" [e1,e2]
                                           opDenote o                = error $ "Unknown binary operator " ++ show o

------------------
-- Control Flow --
------------------
compile (CTBranchIN c t f ty) = compileThread c >>= \ (r_c,pi_c) ->
                                compile t       >>= \ (r_t,pi_t) ->
                                compile f       >>= \ (r_f,pi_f) ->
                                genReg          >>= \ r_res ->
                                return (r_res,pi_c ++
                                              [DeclStmt (VarDecl [] (trTy ty) r_res Nothing),
                                               IfThenElse
                                                (Var r_c)
                                                (pi_t ++ [Assign (LHSVar r_res) (Var r_t)])
                                                (Just (pi_f ++ [Assign (LHSVar r_res) (Var r_f)]))])
compile (CTCaseIN e alts ty) = compileThread e              >>= \ (r_e,pi_e) ->
                               genReg                       >>= \ r_res ->
                               mapM (compileAlt r_res) alts >>= \ etic_alts ->
                               return (r_res, pi_e ++ [DeclStmt (VarDecl [] (trTy ty) r_res Nothing),
                                                       MatchUnion (Var r_e) etic_alts])

----------------------
-- Tuples and Lists --
----------------------
compile e@(CTPairIN e1 e2 ty) = compileThread e1 >>= \ (r_e1,pi_e1) ->
                                compileThread e2 >>= \ (r_e2,pi_e2) ->
                                genReg             >>= \ r_res ->
                                return (r_res,pi_e1 ++ pi_e2 ++
                                              [DeclStmt (VarDecl [] (trTy ty) r_res
                                                         (Just (MkPair (Var r_e1) (Var r_e2))))])


--
-- stubbed, just to see what's going through elsewhere
--
-- (2010.05.19) Schulz
--

compile (CTListIN _ _) = return ("<LIST>", [])

--compile e@(CTListIN _ _)     = error $ "CTListIN not supported yet: " ++ show e

---------------
-- Variables --
---------------
compile e@(CTVarIN x ty)        = rdEnv      >>= \ env ->
                                  rdStThread >>= \ stThread ->
                                  let (RegBinding r) = env x in return (r,[])
compile e@(CTConIN ctor args _) = mapM compileThread args >>= \ results ->
                                  return (map fst results)  >>= \ rs_args ->
                                  return (map snd results)  >>= \ pis_args ->
                                  genReg                    >>= \ r_res ->
                                  return (r_res,concat pis_args ++
                                                [Assign (LHSVar r_res) (CtorApp ctor (map Var rs_args))])

--------------
-- Literals --
--------------
compile (CTLitIN (C.LitInt i) _)      = genReg >>= \ r ->
                                        return (r,[DeclStmt (VarDecl [] TyInt r (Just (E.LitInt (fromIntegral i))))])
compile (CTLitIN (C.LitBool b) _)     = genReg >>= \ r ->
                                        return (r,[DeclStmt (VarDecl [] TyBool r (Just (E.LitBool b)))])
compile (CTLitIN (C.LitChar c) _)     = genReg >>= \ r ->
                                        return (r,[DeclStmt (VarDecl [] TyChar r (Just (E.LitChar c)))])
--compile e@(CTLitIN (C.LitString _) _) = error $ "LitString not supported yet: " ++ show e
compile (CTLitIN (C.LitString s) _)   = return (dummyreg++"STRING",[])
-- Does UnitEl ever actually pop out of the frontend?
compile (CTLitIN C.UnitEl _)          = return ("dummyRegUnit",[])
--compile (CTUnitIN _)                  = return ("dummyRegUnit",[])
compile (CTUnitIN _)                  = return (r_unit,[])

-----------------------
-- Fall-through case --
-----------------------
compile e = error $ "Unhandled case in `compile': " ++ show e

trsubpat :: CTPat -> PatBinder
trsubpat (PVar x _)   = VarBinder x
trsubpat (Wildcard _) = WildcardBinder
trsubpat (PLit _ _)   = ConstBinder 0
trsubpat (PCon _ _ _)   = CtorBinder
trsubpat (PTuple _ _ _) = PairBinder
trsubpat (PNest p _)  = trsubpat p
trsubpat p            = error $ "Improperly nested pattern: " ++ show p

patvars :: CTPat -> [String]
patvars (PVar x _)  = [x]
patvars (PNest p _) = patvars p
patvars _           = []

compileAlt :: Reg -> (CTPat, INAST) -> M (Pat,[Stmt])
compileAlt r_dest (pat,e) = case pat of
                              (PCon ctor subpats _) -> rdEnv >>= \ env ->
                                                       let
                                                          vars     = concatMap patvars subpats
                                                          etic_pat = PatMatch ctor (map trsubpat subpats)
                                                          rho      = xEnv env vars (map RegBinding vars)
                                                       in
                                                          inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                                                             return (etic_pat,pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])
                              (PTuple subpat1 subpat2 _) ->
                                                     rdEnv >>= \ env ->
                                                     let
                                                        vars     = patvars subpat1 ++ patvars subpat2
                                                        etic_pat = PatTuple [trsubpat subpat1,trsubpat subpat2]
                                                        rho      = xEnv env vars (map RegBinding vars)
                                                     in
                                                        inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                                                           return (etic_pat,pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])
                              (PDone subpat _)    -> rdEnv >>= \ env ->
                                                     let
                                                        vars     = concatMap patvars [subpat]
                                                        etic_pat = PatMatch "__Done" [trsubpat subpat]
                                                        rho      = xEnv env vars (map RegBinding vars)
                                                     in
                                                        inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                                                           return (etic_pat,pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])
                                                     --TODO :: Verify this pattern is correct
                              (PDoneRe subpat _)  -> rdEnv >>= \ env ->
                                                     let
                                                        vars     = concatMap patvars [subpat]
                                                        etic_pat = PatMatch "__DoneRe" [trsubpat subpat]
                                                        rho      = xEnv env vars (map RegBinding vars)
                                                     in
                                                        inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                                                           return (etic_pat,pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])
                              (PPause subpat _)   -> rdEnv >>= \ env ->
                                                     let
                                                        vars     = concatMap patvars [subpat]
                                                        etic_pat = PatMatch "__Pause" [trsubpat subpat]
                                                        rho      = xEnv env vars (map RegBinding vars)
                                                     in
                                                        inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                                                           return (etic_pat,pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])
                                                     --TODO :: Verify this pattern is correct
                              (PPauseRe subpat _) -> rdEnv >>= \ env ->
                                                     let
                                                        vars     = concatMap patvars [subpat]
                                                        etic_pat = PatMatch "__PauseRe" [trsubpat subpat]
                                                        rho      = xEnv env vars (map RegBinding vars)
                                                     in
                                                        inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                                                           return (etic_pat,pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])
                              (Wildcard _)        -> compile e >>= \ (r_e,pi_e) ->
                                                     return (PatDefault,pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])
                              (PNest p _)         -> compileAlt r_dest (p,e)
                              (PVar v _)          -> rdEnv >>= \ env ->
                                                     let
                                                        vars = [v]
                                                        etic_pat = PatVar v
                                                        rho      = xEnv env vars (map RegBinding vars)
                                                     in
                                                        inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                                                          return (etic_pat,pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])


                              -- more stubs, to examine output without lists:
                              -- (2010.05.19) Schulz

                              (PCons _ _ _)       -> return (PatDefault, [])
                              (PList _ _)         -> return (PatDefault, [])

                              _                   -> error $ "Unsupported pattern form: " ++ show pat

dummyreg :: Reg
dummyreg = "rDummy"

codegen :: INProg -> Prog
codegen inprog = prj (compileProg inprog)
