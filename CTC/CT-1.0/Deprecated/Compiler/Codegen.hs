--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/CodeGen.hs
--
-- The CT-to-ETIC code generation module
--
-- Put here 2010.04.14 by Adam
--
-- Taken over 2010.05.20 by Ben
--
-- (2010.05.20) Schulz
--
module Deprecated.Compiler.Codegen where

import CT.Syntax as C
import CT.Uncase
import CT.INAST
import CT.MonadicConstructions hiding (rdEnv,inEnv)
import qualified CT.MonadicConstructions
import Deprecated.ETIC.Syntax as E
import qualified Deprecated.ETIC.Print
import qualified Control.Monad.Identity
import Control.Monad

type Label   = String
type Ident   = String
type Reg     = String
type Env     = Ident -> Binding

data Binding = RegBinding Reg
             | ProcBinding Reg [Reg]   -- return and argument registers, resp.
             | KappaBinding Label [Reg]
             | ConstBinding Int        -- symbol bound to an immediate constant
             deriving Show



--                 --
-- TOP-LEVEL CALL: --
--                 --
codegen :: INProg -> Prog
codegen inprog = prj (compileProg inprog)


--------------------
--------------------
-- Compiler monad --
--------------------
--------------------
type M       = StateT Int (EnvT (Env,Bool) Id)

initst :: Int
initst = 0

initenv = \_ -> RegBinding dummyreg

prj :: M a -> a
prj (ST s) =
  fst $ deId $ (deENV (s initst)) (initenv, False)

                      

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
           return ("__r_" ++ show c)

tweek :: Env -> Ident -> Binding -> Env
tweek env r b = \ r' -> if r' == r then b else env r'

xEnv :: Env -> [Ident] -> [Binding] -> Env
xEnv env (i:is) (b:bs) = tweek (xEnv env is bs) i b
xEnv env []     []     = env


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
trTy CTStringTy                = TyString
trTy CTUnitTy                  = TyVoid
trTy (CTTyVar v)               = TyUserDef $ "__UntranslatableTyVar" ++ v
trTy (CTAbsTy t1 t2)           = TyUserDef $ "__UntranslatableArrow"
trTy (CTConTy (TyCon ctor) []) = TyUserDef ctor

trTy (CTConTy (TyCon ctor) _)  = error $ "Cannot translate " ++
                                         "higher-kinded type constructor " ++
                                         ctor

trTy (CTListTy t)              = TyStack (trTy t)

trTy (CTMTy ResTy _)           = TyTCB
trTy (CTMTy (ReactTy _ _) _)   = TyUserDef "__React"
trTy (CTMTy StateTy _)         = TyUserDef "__State"

-- yet another (2010.05.19) Schulz
trTy (CTMTy (MVar _) _)        = TyUserDef "__Monadic"
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

       rdEnv >>= \env ->
       let (argTys, resultTy) = curryType ty
           env'               = xEnv env argNames (map RegBinding argNames)
           args'              = zip (map trTy argTys) argNames
--           ret                = retrof name
           ret                = r_ret
       in
         inEnv env' (compile body) >>= \(r_body, pi_body) ->
         case resultTy of
           (CTMTy _ t) -> return
                            (FunDecl
                              (Just $ trTy t) name args' []
                                (pi_body ++ [Return (Var r_body)]))
--                                  [Return (RunThread (Var r_body))]))

           t           -> return
                            (FunDecl
                              (Just $ trTy t) name args' []
                                (pi_body ++
                                  [
                                    (mkrassign ret r_body),
                                    Return (Var ret)
                                  ]))


compileProg :: INProg -> M Prog
compileProg (INProg ((mainDec, otherFunDecs), (dataDecs, monadDecs))) =

   -- bind virtual registers for each procedure:
   mkfenv (mainDec:otherFunDecs) >>= \rho ->

   -- bind declared constructors to their enumeration constants:
   inEnv rho (mkdconenv dataDecs) >>= \rho' -> 

   inEnv rho' $

   mapM compileFunDec (mainDec:otherFunDecs) >>= \fundecs ->
   mapM compileDataDec dataDecs              >>= \datadecs ->
   mapM compileMonadDec monadDecs            >>= \statevardeclss ->
   return (Prog ((concat datadecs) ++ (concat statevardeclss) ++ fundecs))


--
-- deprecated
--
-- (2010.05.24) Schulz
--
--compileCtorDec :: (TyCon,[CTTy]) -> (String,[Type])
--compileCtorDec (TyCon n,tys) = (n,map trTy tys)


compileCtor :: (TyCon, [CTTy]) -> TopDecl
compileCtor (TyCon c, ts) = StructDec c
                              (attachl structfieldname (map trTy ts))

compileDataDec :: DataDec -> M [TopDecl]
compileDataDec (DataDec (TyCon dtname) [] ctordecs) =

    let cs  = map compileCtor ctordecs
        suf = "__alts"
        fl  = (dconflag, TyInt)

        -- C-like union formed by the constructor alternatives
        un  = UnionDec (dtname ++ suf)
                (attachl altfieldname
                  (map (TyStruct . (\(TyCon c) -> c) . fst) ctordecs))

        unt = (instancefieldname, TyUnion (dtname ++ suf))

        -- make an enumeration corresponding to the constructor values
        -- that can appear in the flag field of the final struct:
        enm = EnumDec (map ((\(TyCon c) -> enumof c) . fst) ctordecs)

        -- first field: flag that signals which union alternative instantiated
        -- second field: the union formed by the constructor-dec alternatives
        dat = StructDec dtname (fl:unt:[])

    in
      return $ (enm:cs) ++ (un:dat:[])


--    return (UnionDecl dtname (map compileCtorDec ctordecs))

compileDataDec (DataDec _ _ _) = error "No parameterized data declarations"

--
-- for the purposes of this compilation path, signal declarations
-- can be treated as data declarations; each is split into a 'rsp'
-- and a 'req' set of structs, and these are compiled
--
compileDataDec s@(SigDec _ _) = let (reqs, rsps) = sigtodata s
                                in
                                  compileDataDec reqs >>= \d ->
                                  compileDataDec rsps >>= \d' ->
                                  return (d ++ d')


compileStateLayer :: (StateLT, (CTIdent, CTTy)) -> M TopDecl
compileStateLayer (StateL, (n,ty)) = return $
                                       TopVarDecl $
                                         VarDecl [] (trTy ty) n
                                           Nothing

compileStateLayer (MemL n, (x, t)) = return $
                                       TopVarDecl $ 
                                         VarDecl [] (TyArray n (trTy t)) x
                                           Nothing

--
-- need to reconcile stack size as declared with
-- low-level usages of stacks here
--
-- (2010.06.04) Schulz
--
compileStateLayer (StackL _, (x, t)) = return $
                                         TopVarDecl $ 
                                           VarDecl [] (TyStack (trTy t)) x
                                             Nothing




compileMonadDec :: MonadDec -> M [TopDecl]
compileMonadDec (CTStateT _ layers) = mapM compileStateLayer layers
compileMonadDec _                   = return []




---------------
-- Functions --
---------------

compile :: INAST -> M (Reg,[Stmt])

--
-- "application" of a resumption bound to an in-scope
-- identifier has a special meaning, and should not
-- be treated like an ordinary procedure call
--
-- this case in particular corresponds to the reactive resumption
-- coming out of a pattern as, e.g.,
--
--   (P (Cont, r)) -> step_R (r Ack)
--
compile ap@(CTAppIN (CTVarIN r _) rsp (CTMTy StateTy (CTMTy (ReactTy _ _) _))) =
  

  compileThread rsp >>= \(r_s, p) ->
  genReg >>= \r_res ->

  let mksig = mkrassign r_signal r_s
      rts   = mkxassign r_ret (RunThread (Var r))
--      rts   = RunThread (Var r)
  in
    return (r_res, p ++ [mksig, rts])


--
-- general function application:
--

compile ap@(CTAppIN _ _ _) =
  let (f:args) = uncurryApp ap
  in
    mapM compileThread args >>= \results ->

    let regs = map fst results
        pi   = concat $ map snd results
    in

    rdEnv >>= \env ->

    case f of
      lam@(CTLamIN _ _ _) -> let (vars, body) = uncurryLam lam
                                 rho          = xEnv env vars
                                                  (map RegBinding regs)

                             in
                               inEnv rho
                                 (compileNoThread body) >>= \(r_body,pi_body) ->
                               return (r_body, pi ++ pi_body)

      (CTVarIN k _) -> case env k of

                         (ProcBinding ret_r arg_rs)  -> genReg >>= \r_res ->

                                                        return
                                                        (r_res,

                                                          pi ++ 
                                                          [mkxassign r_res 
                                                            (FunCall k $
                                                              map Var regs)]
                                                        )


                         (KappaBinding klabel kregs) -> return
                                                        (dummyreg,

                                                         pi ++

                                                         (zipWith
                                                           (\r -> \kr ->
                                                             Assign (LHSVar kr) 
                                                                    (Var r))
                                                          regs kregs) ++

                                                          [Jump klabel])

                         -- Seriously?  No.
                         -- This needs to be a legit procedure call
                         -- (2010.05.20) Schulz
                         --
                         -- Wrote around to hit first case above
                         -- if this case happens,
                         -- it means something is wrong
                         -- (2010.05.26) Schulz
                         --
                         (RegBinding _) -> return
                                             (dummyreg,
                                               pi ++
                                                 [Jump "b0rked procedure call"])




--
-- fixpoint application, i.e. instantiated loop:
--
compile (CTFixAppIN (CTFixIN (CTLamIN k lam _) _) args ty) =
            
  mapM compileThread args >>= \results ->
  rdEnv >>= \env ->
  genLabel >>= \label ->
  let regs        = map fst results
      pi          = concat $ map snd results
      (vars,body) = uncurryLam lam
      inits       = zipWith mkrassign vars regs  -- initial loop var assignments

      env'        = tweek env k (KappaBinding label regs)
      rho         = xEnv env' vars (map RegBinding vars)
  in
    inEnv rho (compileNoThread body) >>= \(r_body, pi_body) ->
    return
      (r_body,
        pi ++ inits ++ [Loop label pi_body])



compile (CTRecAppIN f e ty) = compile (CTAppIN f e ty)

-- By "orphaned" I mean it's not handled in the context of
-- an application or a bind.
--
-- Adam
compile e@(CTLamIN _ _ _) = error $ "Orphaned CTLamIN: " ++ show e

-------------------------
-- Monadic Expressions --
-------------------------
compile (CTBindIN e (CTLamIN x f _) _) = compileNoThread e >>= \(r_e,pi_e) ->
                                         rdEnv >>= \env ->

                                         inEnv (tweek env x (RegBinding r_e))
                                          (compileNoThread f) >>= \(r_f,pi_f) ->

                                         rdStThread >>= \stThread ->
                                         if stThread
                                         then
                                           genReg >>= \r_result ->
                                           return
                                             (r_result,
                                               [DeclStmt $
                                                 VarDecl [] TyTCB 
                                                 r_result
                                                 (Just $
                                                   MkThread $
                                                     pi_e++pi_f++
                                                       [Return (Var r_f)])])
                                         else
                                           return (r_f, pi_e ++ pi_f)


compile (CTNullBindIN e1 e2 _)         = compileNoThread e1 >>= \ (_,pi_e1) ->
                                         compileNoThread e2 >>= \ (r_e2,pi_e2) ->
                                         rdStThread         >>= \ stThread ->
                                             if stThread
                                              then
                                               genReg >>= \ r_result ->
                                               return (r_result,[DeclStmt (VarDecl [] TyTCB r_result (Just (MkThread (pi_e1++pi_e2++[Return (Var r_e2)]))))])
                                              else
                                               return (r_e2,pi_e1++pi_e2)

compile (CTReturnIN e _)               = compileThread e >>= \(r_e,pi_e) ->
                                         rdStThread >>= \stThread ->
                                         if stThread
                                         then
                                           genReg >>= \ r_result ->
                                           return
                                             (r_result,

                                               [DeclStmt $
                                                 VarDecl [] TyTCB
                                                 r_result

                                                 (Just $
                                                   MkThread
                                                     (pi_e++[Return (Var r_e)]))
                                               ]
                                             )
                                         else
                                           return (r_e, pi_e)

------------------------
-- Stateful Operators --
------------------------
compile (CTGetIN n ty)      = genReg >>= \r ->
                              return (r, [Assign (LHSVar r) (Var n)])

compile (CTPutIN n e _)     = compile e >>= \(r_e, p) ->
                              return
                                (r_unit,
                                  p ++ [Assign (LHSVar n) (Var r_e)])

compile (CTPopIN n ty)      = genReg >>= \r ->
                              return
                                (r, [Assign (LHSVar r) (Pop $ Var n)])

compile (CTPushIN n e _)    = compile e >>= \(r_e, p) ->
                              return
                                (r_unit,
                                  p ++ [ExprStmt $ Push  (Var r_e) (Var n)])

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

                            let sl = Slice (Var r_phi)
                            in
                              if stThread
                              then
                                return
                                  (r_result,
                                    pi_phi ++
                                      [DeclStmt $
                                        VarDecl [] TyTCB r_result $
                                          Just (MkThread [Return sl])])
                              else
                               return
                                 (r_result,
                                   pi_phi ++
                                     [DeclStmt $
                                       VarDecl [] TyTCB r_result (Just sl)])


-----------------------------------
-- Reactive-Resumption Operators --
-----------------------------------
compile (CTSignalIN e _) = compileThread e >>= \ (r_e,pi_e) ->
                           genReg >>= \ r_res ->
                           return
                             (r_res,
                               pi_e ++
                                 (SysCall (Var r_e)):
                                 (mkrassign r_res r_signal):
                                 [])


--------------------------
-- Primitive Operations --
--------------------------
compile (CTPrim1aryIN op e ty)    = compileThread e >>= \ (r_e,pi_e) ->
                                    genReg          >>= \ r_res ->
                                    return
                                      (r_res,
                                        pi_e ++
                                          [DeclStmt (VarDecl [] (trTy ty) r_res
                                            (Just (opDenoteUn op (Var r_e))))])

compile (CTPrim2aryIN op e1 e2 ty) = compileThread e1 >>= \ (r_e1,pi_e1) ->
                                     compileThread e2 >>= \ (r_e2,pi_e2) ->
                                     genReg           >>= \ r_res ->
                                     return (r_res,pi_e1 ++ pi_e2 ++ [DeclStmt (VarDecl [] (trTy ty) r_res
                                                                                (Just (opDenoteBin op (Var r_e1) (Var r_e2))))])

------------------
-- Control Flow --
------------------
compile (CTBranchIN c t f ty) =

  compileThread c >>= \(r_c, pi_c) ->
  compile t >>= \(r_t, pi_t) ->
  compile f >>= \(r_f, pi_f) ->
  genReg >>= \r_res ->
  return
    (r_res,

      pi_c ++

        [
          DeclStmt (VarDecl [] (trTy ty) r_res Nothing),

          IfThenElse
          (Var r_c)
          (pi_t ++ [Assign (LHSVar r_res) (Var r_t)])
          (Just (pi_f ++ [Assign (LHSVar r_res) (Var r_f)]))

        ])


compile (CTCaseIN e alts ty) =

  compileThread e >>= \(r_e, pi_e) ->
  genReg >>= \r_case ->
  rdEnv >>= \rho ->

  -- compile the body of each case alternative:
  (
    foldr
    (\(p, a) -> \m -> 

      let vs = patvars p
      in
        inEnv (xEnv rho vs (map RegBinding vs)) (compile a) >>= \(r, pi) ->
        m >>= \pi' ->
        return ((pi ++ [mkrassign r_case r]):pi')
    )
      (return []) alts

  ) >>= \pi_as ->

      -- form the boolean conditions for control flow:
  let bs   = map (\(p, _) ->  mkmatchcond (Var r_e) p) alts

      -- form the assignments corresponding to the pat var bindings:
      as   = map (\(p, _) -> mkpatassigns rho (Var r_e) p) alts

      -- put the initial assignments together with corresponding alt stmts:
      as'  = zipWith (++) as pi_as
  in
    return
      (r_case,
        pi_e ++ [foldbranch $ zip bs as'])


{-
  compileThread e              >>= \(r_e,pi_e) ->
  genReg                       >>= \r_res ->
  mapM (compileAlt r_res) alts >>= \etic_alts ->
  return
    (r_res, pi_e ++ [DeclStmt (VarDecl [] (trTy ty) r_res Nothing),
      MatchUnion (Var r_e) etic_alts])
-}

----------------------
-- Tuples and Lists --
----------------------
compile e@(CTPairIN e1 e2 ty) = compileThread e1 >>= \(r_e1, pi_e1) ->
                                compileThread e2 >>= \(r_e2, pi_e2) ->
                                genReg             >>= \r_res ->
                                return
                                  (r_res,
                                    pi_e1 ++ pi_e2 ++
                                      [DeclStmt $
                                        VarDecl [] (trTy ty) r_res $
                                          Just (MkPair (Var r_e1) (Var r_e2))])


--
-- we are temporarily compiling lists to stacks, which
-- will be themselves a temporary ETIC primitive, so
-- as to get the reifier example up and running in a timely fasion
--
-- lists are deprecated, and this case is transitional
--
-- DO NOT KEEP IT HERE
--
-- (2010.06.03) Schulz
--
compile (CTListIN es t) = (
                            foldr
                            (\e -> \m ->
                              compileThread e >>= \(r, p) ->
                              m >>= \(rs, ps) ->
                              return (r:rs, p:ps)
                            ) (return ([], [])) es

                          ) >>= \(rs, ps) ->

                          genReg >>= \r_res ->

                          -- declare a variable with an initially empty stack:
                          let d  = DeclStmt $ VarDecl [] (TyStack (trTy t))
                                     r_res (Just EmptyStack)

                              -- push the given expressions onto the stack:
                              as = foldl
                                   (\m -> \r ->

                                     (mkxassign r_res
                                       (Push (Var r) (Var r_res))):m

                                   ) [] rs
                          in
                            return
                              (r_res, d:(concat ps ++ as))
                                


---------------
-- Variables --
---------------
compile e@(CTVarIN x ty)        = rdEnv      >>= \ env ->
                                  rdStThread >>= \ stThread ->
                                  case (env x) of
                                    (RegBinding r)       -> return (r, [])
                                    (ProcBinding ret as) -> return
                                                              (ret,
                                                                [ExprStmt $
                                                                 FunCall x []])


compile e@(CTConIN ctor args _) = mapM compileThread args >>= \results ->
                                  return (map fst results)  >>= \rs_args ->
                                  return (map snd results)  >>= \pis_args ->
                                  genReg                    >>= \r_res ->
                                  return
                                    (r_res,
                                      concat pis_args ++
                                      [mkxassign r_res $
                                         CtorApp ctor (map Var rs_args)])


--------------
-- Literals --
--------------
compile (CTLitIN (C.LitInt i) _)      = genReg >>= \r ->
                                        return
                                          (r,
                                            [DeclStmt $ 
                                              VarDecl [] TyInt r $
                                                Just $
                                                  E.LitInt (fromIntegral i)])

compile (CTLitIN (C.LitBool b) _)     = genReg >>= \r ->
                                        return
                                          (r,
                                            [DeclStmt $
                                              VarDecl [] TyBool r $ 
                                                Just (E.LitBool b)])

compile (CTLitIN (C.LitChar c) _)     = genReg >>= \ r ->
                                        return
                                          (r,
                                            [DeclStmt $
                                              VarDecl [] TyChar r $
                                                Just (E.LitChar c)])

compile (CTLitIN (C.LitString s) _)    = genReg >>= \ r ->
                                         return
                                           (r,
                                             [DeclStmt $
                                               VarDecl [] TyString r $
                                                 Just (E.LitString s)])


compile (CTLitIN C.UnitEl _)          = return (r_unit,[])
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

--
-- get the identifiers to-be-bound out of a pattern:
--
patvars :: CTPat -> [String]
patvars (PNest p _)     = patvars p
patvars (PTuple p p' _) = (patvars p) ++ (patvars p')
patvars (PCon _ ps _)   = concat $ map patvars ps
patvars (PPause p _)    = patvars p
patvars (PDone p _)     = patvars p
patvars (PPauseRe p _)  = patvars p
patvars (PDoneRe p _)   = patvars p
patvars (PCons p p' _)  = (patvars p) ++ (patvars p')
patvars (PList ps _)    = concat $ map patvars ps
patvars (PVar x _)      = [x]
patvars _               = []

--
-- translate the variables appearing in a pattern
-- into a list of assignments corresponding to the specified binding
--
mkpatassigns :: Env -> Expr -> CTPat -> [Stmt]

mkpatassigns rho e (PNest p _)   = mkpatassigns rho e p

--
-- deconstructor patterns:
--
mkpatassigns rho e (PCon c ps _) = let fs  = attachl structfieldname ps
                                       e'  = StructMember e instancefieldname
                                       e'' = UnionMember e' $
                                               altfieldname ++
                                                 (show $
                                                   (\(ConstBinding n) -> n)
                                                     (rho c))

                                       fs' = map
                                               (\(l, p) ->
                                                 (StructMember e'' l, p))
                                                   fs
                                   in
                                     concat $
                                       map (\(e, p) -> mkpatassigns rho e p) fs'
                                 

mkpatassigns rho e (PTuple p p' _) = let a  = StructMember e fst_field
                                         a' = StructMember e snd_field
                                     in
                                       (mkpatassigns rho a p) ++
                                       (mkpatassigns rho a' p')

--
-- resumption patterns:
--
mkpatassigns rho e (PDoneRe p _)  = mkpatassigns rho (TRetOf e) p

mkpatassigns rho e (PPauseRe (PTuple p p' _) _) = let sig = SigOf e
                                                      tt  = TTail e
                                                  in
                                                    (mkpatassigns rho sig p) ++
                                                    (mkpatassigns rho tt p')

mkpatassigns rho e (PPauseRe (PVar p _) _)     = [mkxassign p e]
mkpatassigns rho e (PPauseRe (Wildcard _) _)   = []

mkpatassigns rho e (PDone p _)  = mkpatassigns rho (TRetOf e) p
mkpatassigns rho e (PPause p _) = mkpatassigns rho (TTail e) p

--
-- list patterns:
--
mkpatassigns rho e (PCons p p' _) = let h = Top e
                                        t = SRest e
                                    in
                                      (mkpatassigns rho h p) ++
                                      (mkpatassigns rho t p')

--
-- the actual assignment:
--
mkpatassigns rho e (PVar x _)      = [mkxassign x e]

--
-- stub case, while I work out everything
--
-- (2010.06.04) Schulz
--
mkpatassigns _ _ _                 = []

--
-- given the register with the matching expression,
-- form the boolean condition corresponding to
-- a match on a given pattern:
--
-- note that we implicitly incorporate the assumption
-- that constructors are not being partially applied
--
-- (2010.05.24) Schulz
--
mkmatchcond :: Expr -> CTPat -> Expr

mkmatchcond x (PNest p _)   = mkmatchcond x p

--
-- deconstructor patterns:
--
mkmatchcond x (PCon c ps _) =

      -- constructor match corresponds to correct enumerated value in dconflag
  let cm = IsEq (StructMember x dconflag)  (Var $ enumof c)

      -- associate each subpattern to its corresponding field
      fs = attachl structfieldname ps

      -- form conditions for each of the subpatterns, localized
      -- to the proper 'struct' field:
      fs' = map (\(m, p) -> mkmatchcond (StructMember x m) p) fs
  in
    foldr
      (\e -> \e' -> AndLogic e e') cm fs'

mkmatchcond x (PTuple p p' _) = let a  = StructMember x fst_field
                                    a' = StructMember x snd_field
                                in
                                  AndLogic (mkmatchcond a p) (mkmatchcond a' p')

--
-- list patterns:
--
mkmatchcond x (PCons p p' _)   = AndLogic (Not $ IsEmpty x) $
                                   AndLogic (mkmatchcond (Top x) p) $
                                     (mkmatchcond (SRest x) p)

mkmatchcond x (PList [] _)     = IsEmpty x

mkmatchcond x (PList (p:ps) t) = AndLogic
                                   (mkmatchcond (Top x) p)
                                     (mkmatchcond (SRest x) (PList ps t))


--
-- resumption patterns:
--
mkmatchcond r (PDoneRe p _)  = AndLogic (IsDone r) (mkmatchcond (TRetOf r) p)


mkmatchcond r (PPauseRe (PTuple p p' _) _) = AndLogic (Not $ IsDone r) $
                                               AndLogic
                                                 (mkmatchcond (SigOf r) p)
                                                 (mkmatchcond (TTail r) p')

mkmatchcond r (PPauseRe (PVar _ _) _)      = (Not $ IsDone r)
mkmatchcond r (PPauseRe (Wildcard _) _)    = (Not $ IsDone r)

mkmatchcond r (PDone p _)  = AndLogic (IsDone r) (mkmatchcond (TRetOf r) p)
mkmatchcond r (PPause p _) = AndLogic
                               (Not $ IsDone r) (mkmatchcond (TTail r) p)


--
-- literal patterns:
--
mkmatchcond r (PLit (C.LitInt n) _)  = IsEq r (E.LitInt (toInteger n))
mkmatchcond r (PLit (C.LitBool b) _) = E.LitBool b

--
-- unconditionally matching patterns:
--
mkmatchcond r (PVar _ _)             = E.LitBool True
mkmatchcond _ (Wildcard _)           = E.LitBool True

mkmatchcond _ x = Var $ "PATTERN_STUB_" ++ (show x)



--
-- this function involves deprecated elements
-- and is no longer in use
--
-- (2010.06.04) Schulz
--
compileAlt :: Reg -> (CTPat, INAST) -> M (Pat,[Stmt])
compileAlt r_dest (pat,e) =

  case pat of
    (PCon ctor subpats _) -> rdEnv >>= \ env ->
                             let vars     = concatMap patvars subpats
                                 etic_pat = PatMatch ctor (map trsubpat subpats)
                                 rho      = xEnv env vars (map RegBinding vars)
                             in
                               inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                               return
                                 (etic_pat,
                                   pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])

    (PTuple subpat1 subpat2 _) -> rdEnv >>= \ env ->
                                  let vars     = patvars subpat1 ++
                                                 patvars subpat2
                                                        
                                      etic_pat = PatTuple
                                                   [trsubpat subpat1,
                                                     trsubpat subpat2]
                                      rho      = xEnv env vars
                                                   (map RegBinding vars)
                                  in
                                    inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                                    return
                                      (etic_pat,
                                        pi_e ++
                                          [Assign (LHSVar r_dest) (Var r_e)])

    (PDone subpat _)    -> rdEnv >>= \ env ->
                           let vars     = concatMap patvars [subpat]
                               etic_pat = PatMatch "__Done" [trsubpat subpat]
                               rho      = xEnv env vars (map RegBinding vars)
                           in
                             inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                             return
                               (etic_pat,
                                 pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])

    --TODO :: Verify this pattern is correct
    (PDoneRe subpat _)  -> rdEnv >>= \ env ->
                           let vars     = concatMap patvars [subpat]
                               etic_pat = PatMatch "__DoneRe" [trsubpat subpat]
                               rho      = xEnv env vars (map RegBinding vars)
                           in
                             inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                             return
                               (etic_pat,
                                 pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])

    (PPause subpat _)   -> rdEnv >>= \ env ->
                           let vars     = concatMap patvars [subpat]
                               etic_pat = PatMatch "__Pause" [trsubpat subpat]
                               rho      = xEnv env vars (map RegBinding vars)
                           in
                             inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                             return
                               (etic_pat,
                                 pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])

    --TODO :: Verify this pattern is correct
    (PPauseRe subpat _) -> rdEnv >>= \ env ->
                           let vars     = concatMap patvars [subpat]
                               etic_pat = PatMatch "__PauseRe" [trsubpat subpat]
                               rho      = xEnv env vars (map RegBinding vars)
                           in
                             inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                             return
                               (etic_pat,
                                 pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])

    (Wildcard _)        -> compile e >>= \ (r_e,pi_e) ->
                           return
                             (PatDefault,
                               pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])

    (PNest p _)         -> compileAlt r_dest (p,e)

    (PVar v _)          -> rdEnv >>= \ env ->
                           let vars     = [v]
                               etic_pat = PatVar v
                               rho      = xEnv env vars (map RegBinding vars)
                           in
                             inEnv rho (compile e) >>= \ (r_e,pi_e) ->
                             return
                               (etic_pat,
                                 pi_e ++ [Assign (LHSVar r_dest) (Var r_e)])


                              -- more stubs, to examine output without lists:
                              -- (2010.05.19) Schulz

    (PCons _ _ _)       -> return (PatDefault, [])
    (PList _ _)         -> return (PatDefault, [])

    _                   -> error $ "Unsupported pattern form: " ++ show pat



--                  --
-- HELPER FUNCTIONS --
--                  --

--
-- fold a list of expression-statement pairs into
-- a sequence of if-then-else statements, in list-order
--
foldbranch :: [(Expr, [Stmt])] -> Stmt
foldbranch =

  foldr
  (\(e, p) -> \b ->

    IfThenElse e p (Just [b])

  ) Skip


--
-- form the initial environment of function virtual-register bindings:
-- 
--
mkfenv :: [INFunDec] -> M Env
mkfenv =

  foldl
  (\m -> \(INFunDec ((f, _), (as, _))) ->

    m >>= \rho ->
--    return $ tweek rho f (ProcBinding (retrof f) as)
    return $ tweek rho f (ProcBinding r_ret as)

  ) (rdEnv)

--
-- form bindings of constructors to their enumeration constants:
--
mkdconenv :: [DataDec] -> M Env
mkdconenv =

  foldr
  (\d -> \m ->

    case d of

    (DataDec (TyCon c) ps cs) -> rdEnv >>= \rho ->

                                 let cs'  = zip
                                              (map ((\(TyCon c) -> c) . fst) cs)
                                                ints
                                     rho' = xEnv rho (map fst cs')
                                              (map (ConstBinding . snd) cs')
                                 in
                                   inEnv rho' m >>= \rho'' ->
                                   return rho''
                                   

    (SigDec (TyCon c) ss)     -> rdEnv >>= \rho ->


                                 let reqs   = zip (map (fst . fst) ss) ints
                                     rsps   = zip (map (fst . snd) ss) ints
                                     rho''' = xEnv rho (map fst reqs)
                                                (map (ConstBinding . snd) reqs)
                                     rho'   = xEnv rho''' (map fst rsps)
                                                (map (ConstBinding . snd) rsps)
                                 in
                                   inEnv rho' m >>= \rho'' ->
                                   return rho''

  ) (rdEnv)


--
-- primitive operation translation:
--
opDenoteUn :: CTPrimOp -> (Expr -> Expr)
opDenoteUn (Un CTNeg) = Neg
opDenoteUn (Un CTNot) = Not
opDenoteUn (Un Fst)   = \e -> StructMember e fst_field
opDenoteUn (Un Snd)   = \e -> StructMember e snd_field
opDenoteUn o          = error $ "Unknown unary operator " ++ show o


opDenoteBin :: CTPrimOp -> (Expr -> Expr -> Expr)
opDenoteBin (Bin CTPlus)     = Add
opDenoteBin (Bin CTMinus)    = Sub
opDenoteBin (Bin CTMult)     = Mul
opDenoteBin (Bin CTIDiv)     = Div
opDenoteBin (Bin CTAnd)      = AndLogic
opDenoteBin (Bin CTOr)       = OrLogic
opDenoteBin (Bin CTEqTest)   = IsEq
opDenoteBin (Bin CTIneqTest) = NotEq
opDenoteBin (Bin CTLTTest)   = IsLT
opDenoteBin (Bin CTGTTest)   = IsGT
opDenoteBin (Bin CTLTETest)  = IsLTE
opDenoteBin (Bin CTGTETest)  = IsGTE
opDenoteBin (Bin CTCons)     = \e1 -> \e2 -> Push e1 e2
opDenoteBin o                = error $ "Unknown binary operator " ++ show o


--
-- transform a SigDec into a DataDec, since for the purposes
-- of this compilation path, they are the same;
--
sigtodata :: DataDec -> (DataDec, DataDec)
sigtodata (SigDec (TyCon c) ss) =

  let ctors = map (\((x, y), (x', y')) -> ((TyCon x, y), (TyCon x', y'))) ss
      reqs  = map fst ctors
      rsps  = map snd ctors
  in
    ((DataDec (TyCon (c ++ "__req")) [] reqs),
      (DataDec (TyCon (c ++ "__rsp")) [] rsps))
    


--                           --
-- CONSTANTS AND BOOKKEEPING --
--                           --

dummyreg :: Reg
dummyreg = "r_NOASSIGN"

--
-- a 'unit' register having a constant value;
-- assignments can be made to this, but they
-- should have no effect, e.g. this works
-- like 'r0' in Microblaze
--
-- (2010.05.19) Schulz
--
r_unit :: Reg
r_unit = "r_UNIT"

--
-- a distinguished register for holding the response
-- from the handler
--
r_signal :: Reg
r_signal = "r_SIGNAL"

--
-- it may be necessary to reference the program counter,
-- for the purpose of forming handler jump-backs:
--
r_pc :: Reg
r_pc = "PC"

--
-- it is also expedient (and not unreasonable) to use
-- something like the standard "return from subroutine"
-- register:
--
r_rts :: Reg
r_rts = "r_RTS"

--
-- function return value register:
--
r_ret :: Reg
r_ret = "__ret"


--
-- short-hand for assigning between registers
--

mkrassign :: Reg -> Reg -> Stmt
mkrassign r1 r2 = Assign (LHSVar r1) (Var r2)

--
-- another assignment short-hand
--
mkxassign :: Reg -> Expr -> Stmt
mkxassign r e = Assign (LHSVar r) e

--
-- naming convention for procedure return register:
--
retrof :: String -> Reg
retrof f = f ++ "__ret"


--
-- struct and union field naming conventions,
-- used in generating 'struct' and 'union' from 'data' decs:
--

dconflag :: String
dconflag = "__ctor__"

altfieldname ::  String
altfieldname = "__altinstance__"

structfieldname :: String
structfieldname = "__structfield__"


--
-- standard field names for cartesian product structs:
--
fst_field :: String
fst_field = "__fst"

snd_field :: String
snd_field = "__snd"


--
-- instance field for a top-level 'data'-declared struct;
-- this holds the actual data structure;
--
instancefieldname :: String
instancefieldname = "__instance__"


--
-- standard suffix for 'enum' constants produced from constructor decs:
--
enumof :: String -> String
enumof x = x ++ "__enum"

--
-- form a key-list of numerically suffixed labels from a given prefix:
--
attachl :: String -> [a] -> [(String, a)]
attachl s xs = zip (map (\x -> s ++ (show x)) ints) xs

ints :: [Int]
ints = iterate (+ 1) 0


-- THIS IS THE END OF THE FILE --
