--
--  this ~/cheapthreads/CTC/CT-1.0/TypeChecker.hs
--
--  the cleaned-up CT type-inferencer
--
--  put here 2010.01.13
--
--  Schulz
-- 

module CT.TypeChecker where


import CT.Syntax
import CT.ANAST
import CT.PrimitiveTySigs

import CT.Debug

import CT.MonadicConstructions



--                --
-- TOP LEVEL CALL --
--                --

cttc :: CTProg -> Either String ANProg
cttc p =
  case (prj $ tc p) of
    Nothing   -> Left "type inference failed\n"
    (Just as) -> Right as



tc :: CTProg -> TE (Maybe ANProg)
tc (CTProg (sigs'', defs', dats, syms, mons)) =

  -- prep the declarations:

  let (mn:defs) = promote_main defs'  -- 'main' heads the declaration list

      -- resolve type synonyms in type and data declarations:
      syms'     = resolvetysyms syms

      -- resolve type synonyms in type signatures:
      sigs'     = resolvetysigs syms' sigs''

      -- resolve type synonyms in data declarations:
      dats'     = resolvedattys syms' dats

      -- resolve type synonyms in monad layers:
      mons'     = resolvemontys syms' mons

  in

    -- form the initial type bindings:

    (mkstatetys mons') >>= \k ->                  -- form state type environment

    inEnv k (mkmconenv mons') >>= \m ->                 -- bind monad ctors
    inEnv m (mkdconenv $ rwmcondats m dats') >>= \d ->   -- bind data decs

    inEnv d (markfuns defs) >>= \rho ->  -- form function type environment


    -- do all inferencing inside of this global environment:
    inEnv rho
    (

      -- infer types for all declared functions:

      (foldr
         (\d -> \m ->

           (tyinfer_fun d) >>= \((x, xs), (a, (t, cs))) ->
           m >>= \(as, cs') ->
           return (((x, t), (xs, a)):as, (TY t, TY (rho x)):(cs ++ cs'))

         )

         -- type-infer 'main' as the base case:
         (
           tyinfer_fun mn >>= \((x, xs), (a, (t, cs))) ->
           return ([((x, t), (xs, a))], (TY t, TY (rho x)):cs)
         )

         -- apply the action to all the other definitions:
         defs  
      )

    ) >>= \(as, cs) ->

   let sigs  = (rwmconsigs rho sigs')  -- rewrite type constructors into monads
       cs'   = (mksigconstraints rho sigs) ++ cs -- constrain by type sig
   in

    -- try to unify the inferred types:
    case (unify cs' (Sol id)) of

      Failure c -> error $ "failed on constraint:   " ++ (show c) ++  "\n" ++
                         "in set:\n" ++ (pplist cs') ++
                         "\n\n in program\n" ++
                         (show (as, sigs, syms', dats', mons')) ++
                         "\n\n" ++ (show c)
    
      s@(Sol _) -> let as' = map (\((x, t), (xs, a)) -> 
                               ((x, (resolvevars s t)),
                                 (xs, (resolve (resolvevars s) a))))
                                  as

                       an  = (last as', init as')
                   in
                     return $ Just (an, ((rwmcondats m dats'), mons'))


pplist :: (Show a) => [a] -> String
pplist xs = '[':'\n':(foldr (\x -> \s -> (show x) ++ '\n':s) "" xs) ++ "]"


--                           --
-- DATA STRUCTURES USED HERE --
--                           --

type TyIdent = String

--
-- a constraint may apply to either types
-- or (monadic) type constructors:
--
data VTy = TY CTTy | MV MTy deriving Show

instance Eq VTy where
  (TY t)  == (TY t')  =  t == t'
  (MV m)  == (MV m')  =  m == m'
  _       == _        =  False


type Constraint = (VTy, VTy)

data Subst = Sol (VTy -> VTy)
           | Failure Constraint

deSol :: Subst -> (VTy -> VTy)
deSol (Sol f) = f


--
-- the type inferencer monad:
--
type TEnv = TyIdent -> CTTy

type TE a = EnvT TEnv (StateT Int Id) a



--
-- some basic operations in the monad:
--

--
-- project out of the monad:
--
prj :: TE a -> a
prj (ENV x) = fst $ deId ((deST (x (initenv))) (initct + 1))

--
-- the initial environment:
--
-- by convention, everything is initially mapped to the same
-- generic type variable
--
initenv :: TEnv
initenv = \_ -> initbind

initct :: Int
initct = 0

initbind :: CTTy
initbind = CTTyVar (tyvarpref ++ "__NOTHING__")

--
-- extend an environment:
--
extenv :: TyIdent -> CTTy -> TE TEnv
extenv v t =
  rdEnv >>= \e ->
  return (tweek v t e)

tweek :: (Eq a) => a -> b -> (a -> b) -> (a -> b)
tweek v t e = \x -> if x == v then t else e x


--
-- read as: "replace v with t in solution s"
--
--
tweeksol :: VTy -> VTy -> Subst -> Subst
tweeksol v t (Sol s) = Sol $ tweek v t s



--
-- update a constraint with a new substitution:
--
updconstr :: Subst -> [Constraint] -> [Constraint]
updconstr s =
   map
   (\(x, y) ->
     case x of

       (TY u) -> case y of

                   (TY v) -> (TY $ resolvevars s u, TY $ resolvevars s v)

                   (MV v) -> (x, y) -- this will end up as a unify-fail

       (MV u) -> case y of

                   (MV v) -> (MV $ resolvemons s u, MV $ resolvemons s v)

                   (TY v) -> (x, y)
  )



--
-- unpack the solution as a substitution
-- of a type:
--
tsol :: Subst -> (CTTy -> CTTy)
tsol (Sol s) =
  \x -> case s (TY x) of
          (TY t) -> t

--
-- unpack the solution as a substitution
-- of a monadic constructor variable:
--
msol :: Subst -> (MTy -> MTy)
msol (Sol s) =
  \x -> case s (MV x) of
          (MV t) -> t


--
-- recursively map all type variable substitutions
-- onto a constructed type::
--
resolvevars :: Subst -> CTTy -> CTTy

resolvevars s (CTAbsTy a b)      = CTAbsTy (resolvevars s a) (resolvevars s b)

resolvevars s (CTConTy c ts)     = CTConTy c (map (resolvevars s) ts)

resolvevars s (CTMTy m t)        = let m' = resolvemons s m
                                   in
                                     CTMTy ((msol s) m') (resolvevars s t)

resolvevars s (CTPairTy t t')    = CTPairTy (resolvevars s t) (resolvevars s t')

resolvevars s (CTListTy t)       = CTListTy (resolvevars s t)

-- this case goes through all substitutions
-- of variables for variables made by the unifier:
--
resolvevars s v@(CTTyVar _)      = if (tsol s v) == v
                                   then v
                                   else resolvevars s (tsol s v)

resolvevars s t = (tsol s) t

--
-- same as above for monadic types:
--
resolvemons :: Subst -> MTy -> MTy
resolvemons s m@(MVar _)    = (msol s) m
resolvemons s (ReactTy q r) = ReactTy (resolvevars s q) (resolvevars s r)
resolvemons _ m = m


--
-- increment the variable counter
--
counter :: TE Int
counter =
  liftEnv(
    get >>= \i ->
    upd (\_ -> i + 1) >>
    return i
  )

--
-- make a fresh type variable:
--
newtyvar :: TE TyIdent
newtyvar = counter >>= \i -> return (tyvarpref ++ (show i))

--
-- we separate fresh type constructors purely for
-- convenience; we could just as easily use 'newtyvar'
--
newconvar :: TE TyIdent
newconvar = counter >>= \i -> return (convarpref ++ (show i))


--
-- conventional prefix for an internal type variable:
--
tyvarpref :: String
tyvarpref = "tyvar__"

convarpref :: String
convarpref = "mvar__"






--                     --
-- TYPE INFERENCE CODE --
--                     --




--                            --
-- MAIN TYPE-INFERENCE ENGINE --
--                            --


tyinfer :: CTExpr -> TE (ANAST, (CTTy, [Constraint]))

tyinfer (CTLam x e)       = newtyvar >>= \v ->
                            extenv x (CTTyVar v) >>= \rho -> 
                            inEnv rho (tyinfer e) >>= \(a, (t, cs)) ->
                            let t' = CTAbsTy (rho x) t
                            in
                            return
                              (CTLamAN x a t', (t', cs))


tyinfer (CTApp e e')      = tyinfer e >>= \(a, (t, cs)) ->
                            tyinfer e' >>= \(a', (t', cs')) ->
                            newtyvar >>= \u' ->
                            newtyvar >>= \v' ->
                            let u   = CTTyVar u'
                                v   = CTTyVar v'
                                t'' = CTAbsTy u v
                                c   = (TY t, TY t'')
                                c'  = (TY u, TY t')
                            in
                              return
                                (CTAppAN a a' v,
                                  (v, c:c':(cs ++ cs')))
                                   

--
-- monadic expressions:
--

tyinfer (CTBind e e')     = tyinfer e >>= \(a, (t, cs)) ->
                            tyinfer e' >>= \(a', (t', cs')) ->
                            newconvar >>= \m' ->
                            newconvar >>= \n' ->
                            newtyvar >>= \u' ->
                            newtyvar >>= \v' ->
                            let u = CTTyVar u'
                                v = CTTyVar v'
                                m = MVar m'
                                n = MVar n'
                            in
                              return
                                (CTBindAN a a' (CTMTy n v),

                                  (CTMTy n v,
                                    (TY t, TY $ CTMTy m u):
                                    (TY t', TY $ CTAbsTy u (CTMTy n v)):
                                    (MV m, MV n):
                                    (cs ++ cs')
                                  )
                                )

tyinfer (CTNullBind e e') = tyinfer e >>= \(a, (t, cs)) ->
                            tyinfer e' >>= \(a', (t', cs')) ->
                            newconvar >>= \m' ->
                            newconvar >>= \n' ->
                            newtyvar >>= \u' ->
                            newtyvar >>= \v' ->
                            let u = CTTyVar u'
                                v = CTTyVar v'
                                m = MVar m'
                                n = MVar n'
                            in
                              return
                                (CTNullBindAN a a' t',

                                  (t',
                                    (TY t, TY $ CTMTy m u):
                                    (TY t', TY $ CTMTy n v):
                                    (MV m, MV n):
                                    (cs ++ cs')
                                  )
                                )

tyinfer (CTReturn e)      = tyinfer e >>= \(a, (t, cs)) ->
                            newconvar >>= \m ->
                            let t' = CTMTy (MVar m) t
                            in
                            return
                              (CTReturnAN a t', (t', cs))
                                

--
-- cases for special functions with already given types:
--

tyinfer (CTGet m)         = rdEnv >>= \rho ->
                            let t = CTMTy StateTy (rho m)
                            in
                              return
                                (CTGetAN m t, (t, []))

tyinfer (CTPut m e)       = rdEnv >>= \rho ->
                            tyinfer e >>= \(a, (t, cs)) ->
                            let t' = CTMTy StateTy CTUnitTy
                            in
                              return
                                (CTPutAN m a t', (t', (TY t, TY $ rho m):cs))

tyinfer (CTPop m)         = rdEnv >>= \rho ->
                            let t = CTMTy StateTy (rho m)
                            in
                              return
                                (CTPopAN m t, (t, []))

tyinfer (CTPush m e)      = rdEnv >>= \rho ->
                            tyinfer e >>= \(a, (t, cs)) ->
                            let t' = CTMTy StateTy CTUnitTy
                            in
                              return
                                (CTPushAN m a t', (t', (TY t, TY $ rho m):cs))

tyinfer (CTRead m i)      = tyinfer i >>= \(a, (t, cs)) ->
                            rdEnv >>= \rho ->
                            let t' = CTMTy StateTy (rho m)

                                -- index must be an Int:
                                c  = (TY t, TY CTIntTy)
                            in
                              return
                                (CTReadAN m a t', (t', c:cs))

tyinfer (CTWrite m i e)       = rdEnv >>= \rho ->
                                tyinfer i >>= \(a, (t, cs)) ->
                                tyinfer e >>= \(a', (t', cs')) ->
                                let t'' = CTMTy StateTy CTUnitTy

                                    -- index must be an Int:
                                    c   = (TY t, TY CTIntTy)
                                in
                                  return
                                    (CTWriteAN m a a' t'',
                                      (t'',
                                        c:(TY t', TY $ rho m):(cs ++ cs')))


tyinfer (CTStepRes e)     = tyinfer e >>= \(a, (t, cs)) ->
                            newtyvar >>= \v' -> 
                            let v  = CTTyVar v'
                                t' = CTMTy ResTy v
                            in
                            return
                              (CTStepAN a t',

                                (t', 
                                 (TY t, TY $ CTMTy StateTy v):cs)
                              )


tyinfer (CTResumeR e)     = tyinfer e >>= \(a, (t, cs)) ->
                            newtyvar >>= \v' -> 
                            let v  = CTTyVar v'
                                r  = CTMTy ResTy v
                                r' = CTMTy ResTy r
                                t' = r'
                            in
                            return
                              (CTResumeAN a t',

                                (t', 
                                 (TY t, TY r):cs)
                              )

tyinfer (CTStepReact e)   = tyinfer e >>= \(a, (t, cs)) ->
                            newtyvar >>= \v' -> 
                            newtyvar >>= \r -> 
                            newtyvar >>= \q -> 
                            let v   = CTTyVar v'
                                rsp = CTTyVar r
                                req = CTTyVar q
                                t'  = CTMTy (ReactTy req rsp) v
                            in
                            return
                              (CTStepAN a t',

                                (t', 
                                 (TY t, TY $ CTMTy StateTy v):cs)
                              )


--
-- note, once more, that reactive 'resume' takes no only the thread
-- to resume, by the response to pass -- which is the second arg
--
-- (2010.09.21) Schulz
--
tyinfer (CTResumeRe e e') = tyinfer e >>= \(a, (t, cs)) ->
                            tyinfer e' >>= \(a', (t', cs')) ->
                            newtyvar >>= \v' -> 
                            newtyvar >>= \req' ->
                            newtyvar >>= \rsp' ->
                            let v  = CTTyVar v'
                                req = CTTyVar req'
                                rsp = CTTyVar rsp'
                                re = CTMTy (ReactTy req rsp) v
                                r  = CTMTy ResTy re
                            in
                            return
                              (CTResumeReAN a a' r,

                                (r, 
                                 (TY t, TY re):cs)
                              )


tyinfer (CTLoopReact e)   = tyinfer e >>= \(a, (t, cs)) ->
                            newtyvar >>= \u' ->
                            newtyvar >>= \v' ->
                            newtyvar >>= \req' ->
                            newtyvar >>= \rsp' ->
                            let u   = CTTyVar u'
                                v   = CTTyVar v'
                                req = CTTyVar req'
                                rsp = CTTyVar rsp'
                                t'  = CTAbsTy v (CTMTy (ReactTy req rsp) u)
                            in
                              return 
                                (CTLoopAN a t', (t', (TY t, TY t'):cs))


tyinfer (CTSignal e)      = tyinfer e >>= \(a, (t, cs)) ->
                            newtyvar >>= \r -> 
                            newtyvar >>= \q -> 
                            let req = CTTyVar r
                                rsp = CTTyVar q
                                t'  = CTMTy (ReactTy req rsp) rsp
                            in
                            return
                              (CTSignalAN a t',

                                (t', 
                                 (TY t, TY req):cs)
                              )

tyinfer (CTGetReq e)      = tyinfer e >>= \(a, (t, cs)) ->
                            newtyvar >>= \r ->
                            newtyvar >>= \q ->
                            newtyvar >>= \v' ->
                            let req  = CTTyVar q
                                rsp  = CTTyVar r
                                v    = CTTyVar v'
                                re   = CTMTy (ReactTy req rsp) v
                                t'   = CTMTy ResTy req
                            in
                              return
                                (CTGetReqAN a t', (t', (TY t, TY re):cs))
                                  
                              

tyinfer (CTLoopRes e)     = tyinfer e >>= \(a, (t, cs)) ->
                            newtyvar >>= \u' ->
                            newtyvar >>= \v' ->
                            let u   = CTTyVar u'
                                v   = CTTyVar v'
                                t'' = CTMTy ResTy u
                                t'  = CTAbsTy v t''
                            in
                              return 
                                (CTLoopAN a t', (t', (TY t, TY t'):cs))


tyinfer (CTBreak e)       = tyinfer e >>= \(a, (t, cs)) ->
                            newtyvar >>= \u' ->
                            newconvar >>= \m' ->
                            let u  = CTTyVar u'
                                t' = CTMTy (MVar m') u
                            in
                              return (CTBreakAN a t', (t', (TY u, TY t):cs))

tyinfer (CTFix e)         = tyinfer e >>= \(a, (t, cs)) ->
                            newtyvar >>= \u' ->
                            newtyvar >>= \v' ->
                            newtyvar >>= \x' ->
                            newconvar >>= \m' ->
                            let u = CTTyVar u'
                                v = CTTyVar v'
                                x = CTTyVar x'

                                -- 'm' may unify to either 'R'
                                -- or 'Re' depending on the body
                                -- of the loop
                                m = MVar m'

                                -- type of fully applied 't':
                                c = unpackabs t

                            in
                              return
                                (CTFixAN a u,

                                  (u,

                                    (TY t, TY $ CTAbsTy u v):
                                    (TY u, TY v):
                                    (TY c, TY $ CTMTy m x):cs
                                  )
                                )


--
-- simple expressions:
--                           

tyinfer (CTVar x)         = rdEnv >>= \rho ->
                            return
                              (CTVarAN x (rho x),
                                (rho x, []))


--
-- primitives:
--
tyinfer (CTPrim1ary op@(Un Fst) e) = tyinfer e >>= \(a, (t, cs)) ->

                                     newtyvar >>= \z' ->
                                     newtyvar >>= \w' ->

                                     let (CTAbsTy u v)  = typeOfCTOp op
                                         z              = CTTyVar z'
                                         w              = CTTyVar w'
                                         t'             = (CTPairTy z w)
                                
                                     in
                                       rwpmty [u, v] >>= \([u', v'], cs') ->

                                       return
                                         (CTPrim1aryAN op a v',
                                           (v',
                                              (TY u', TY t):
                                              (TY t', TY t):
                                              (TY z, TY v'):
                                              (cs ++ cs'))
                                         )

tyinfer (CTPrim1ary op@(Un Snd) e) = tyinfer e >>= \(a, (t, cs)) ->

                                     newtyvar >>= \z' ->
                                     newtyvar >>= \w' ->

                                     let (CTAbsTy u v)  = typeOfCTOp op
                                         z              = CTTyVar z'
                                         w              = CTTyVar w'
                                         t'             = (CTPairTy z w)
                                
                                     in
                                       rwpmty [u, v] >>= \([u', v'], cs') ->

                                       return
                                         (CTPrim1aryAN op a v',
                                           (v',
                                              (TY u', TY t):
                                              (TY t', TY t):
                                              (TY w, TY v'):
                                              (cs ++ cs'))
                                         )


tyinfer (CTPrim1ary op e) = tyinfer e >>= \(a, (t, cs)) ->

                            let (CTAbsTy u v) = typeOfCTOp op
                            in
                              rwpmty [u, v] >>= \([u', v'], cs') ->

                              return
                                (CTPrim1aryAN op a v',
                                  (v', (TY u', TY t):(cs ++ cs'))
                                )


tyinfer (CTPrim2ary op@(Bin CTCons) e e') = tyinfer e >>= \(a, (t, cs)) ->
                                            tyinfer e' >>= \(a', (t', cs')) -> 
                                            let l = CTListTy t
                                                c = (TY l, TY t')
                                            in
                                              return
                                                (CTPrim2aryAN op a a' t',
                                                  (t',
                                                    c:(cs ++ cs')
                                                  )
                                                )

tyinfer (CTPrim2ary op e e') = let (CTAbsTy u (CTAbsTy v w)) = typeOfCTOp op
                               in
                                 tyinfer e >>= \(a, (t, cs)) -> 
                                 tyinfer e' >>= \(a', (t', cs')) -> 
                                 rwpmty [u, v, w] >>= \([u', v', w'], cs'') ->
                                 return 
                                   (CTPrim2aryAN op a a' w',
                                      (w',
                                        (TY u', TY t):
                                        (TY v', TY t'):
                                        (cs ++ cs' ++ cs'')
                                      )
                                   )

tyinfer (CTPrim3ary op e e' e'') = let (CTAbsTy u
                                         (CTAbsTy v
                                           (CTAbsTy w z))) = typeOfCTOp op
                                   in
                                     tyinfer e >>= \(a, (t, cs)) -> 
                                     tyinfer e' >>= \(a', (t', cs')) -> 
                                     tyinfer e'' >>= \(a'', (t'', cs'')) -> 

                                     rwpmty [u,v,w,z] >>=
                                       \([u',v',w',z'],cs''') ->

                                     return 
                                       (CTPrim3aryAN op a a' a'' z',
                                          (z',
                                            (TY u', TY t):
                                            (TY v', TY t'):
                                            (TY w', TY t''):
                                            (cs ++ cs' ++ cs'' ++ cs''')
                                          )
                                       )


--
-- control flow:
--
tyinfer (CTBranch (CTGuard b) e e') = tyinfer b >>= \(g, (u, bs)) ->
                                      tyinfer e >>= \(a, (t, cs)) ->
                                      tyinfer e' >>= \(a', (t', cs')) ->
                                      return 
                                        (CTBranchAN g a a' t,
                                          (t,
                                            (TY u, TY CTBoolTy):
                                            (TY t, TY t'):
                                            (bs ++ cs ++ cs')
                                          )
                                        )

tyinfer (CTCase d (alt:as))       =   tyinfer d >>= \(x, (o, cs'')) ->
                                      altinfer o alt >>= \(a, (t, cs)) ->

                                      -- i.e. tyinfer each alt in the list:
                                      (foldr 

                                        (\alt -> \m ->
                                          altinfer o alt >>= \(a', (t, cs)) ->
                                          m >>= \(as', (t', cs')) ->
                                          return ((a':as'),
                                                   (t',
                                                     (TY t, TY t'):
                                                     (cs ++ cs')
                                                   )
                                                 )  
                                        ) (return ([], (t, cs))) as

                                      ) >>= \(as', (t', cs')) ->

                                      return
                                        (CTCaseAN x (a:as') t',
                                          (t', cs' ++ cs''))


--
-- constructed values:
--

--
-- general constructors:
--
-- a constructor is assumed to have a type declaration in the environment;
--
-- this case works in a fashion similar to that for general application;
-- the only difference is that it folds over a list as opposed to working
-- through a recursive syntactic structure
--
tyinfer (CTCon x ys)      = rdEnv >>= \rho ->

  -- this case DOES NOT presently support partial application
  -- (2010.05.07) Schulz

                            let t  = unpackabs $ rho x
                                r  = (CTConAN x [] t, (t, []))
                                ts = unfoldabs (rho x)
                                zs = zip ys ts
                            in
                              foldr 
                              (\(y, s) -> \m ->
                                tyinfer y >>= \(a', (t', cs')) ->
                                newtyvar >>= \u' ->
                                m >>= \((CTConAN x' as' _), (t'', cs'')) ->

                                let c = (TY t', TY s)
                                in
                                  return
                                    (CTConAN x' (a':as') t,
                                      (t, c:(cs' ++ cs'')))

                              )
                                (return r) zs


-- products:
tyinfer (CTPair e e')               = tyinfer e >>= \(a, (t, cs)) ->
                                      tyinfer e' >>= \(a', (t', cs')) -> 
                                      let t'' = CTPairTy t t'
                                      in
                                      return
                                        (CTPairAN a a' t'',
                                          (t'', cs ++ cs'))

-- lists:
tyinfer (CTList es)                 = newtyvar >>= \v' ->
                                      let v = CTTyVar v'
                                      in

                                        (
                                          foldr
                                          (\e -> \m ->

                                            tyinfer e >>= \(a, (t, cs)) ->
                                            m >>= \(as, (t', cs')) ->
                                            return 
                                              (a:as,
                                                (t', 
                                                (TY t, TY t'):(cs ++ cs'))
                                              )

                                          )
                                          (return ([], (v, []))) es

                                        ) >>= \(as, (t, cs)) -> 

                                        return
                                          (CTListAN as (CTListTy t),
                                            ((CTListTy t), cs))

--
-- literals:
--

tyinfer (CTLit (LitInt n))  = return (CTLitAN (LitInt n) CTIntTy, (CTIntTy, []))
tyinfer (CTLit (LitBool b)) = return (CTLitAN (LitBool b) CTBoolTy,
                                       (CTBoolTy, []))

tyinfer (CTLit (LitString s)) = return (CTLitAN (LitString s) CTStringTy,
                                         (CTStringTy, []))

tyinfer CTUnit = return (CTUnitAN CTUnitTy, (CTUnitTy, []))



--
-- rewrite polymorphic type variables in primitive op
-- type signatures;
--
-- this is necessary because each instance of a polymorphic op
-- should have distinct variables in order to unify correctly;
--
-- it is also necessary to preserve the constraints implicit
-- in the type signatures, e.g. "a -> a" should result in a
-- constraint that the result and operand must unify
--
rwpmty :: [CTTy] -> TE ([CTTy], [Constraint])
rwpmty ts =

  -- assign unique identifiers to each type variable in the list:
  (
    foldr
    (\t -> \m ->

      case t of

        -- cases for the cartesian projections:
        (CTPairTy u v) -> case (u, v) of
                            (CTTyVar _, CTTyVar _) -> newtyvar >>= \u' ->
                                                      newtyvar >>= \v' ->
                                                      m >>= \ts ->
                                                      let u = CTTyVar u'
                                                          v = CTTyVar v'
                                                      in
                                                        return
                                                          ((CTPairTy u v):ts)

                            (CTTyVar _, t)         -> newtyvar >>= \u' ->
                                                      m >>= \ts ->
                                                      let u = CTTyVar u'
                                                      in
                                                        return
                                                          ((CTPairTy u t):ts)

                            (t, CTTyVar _)         -> newtyvar >>= \u' ->
                                                      m >>= \ts ->
                                                      let u = CTTyVar u'
                                                      in
                                                        return
                                                          ((CTPairTy t u):ts)

                            _                      -> return (t:ts)

   
        -- presence of a type variable indicates a generic
        -- variable that needs be uniquely tagged:

        (CTTyVar _)    -> newtyvar >>= \u ->
                          m >>= \ts ->
                          return ((CTTyVar u):ts)

        -- otherwise, the type is rigid and needs no modification
        _              -> m >>= \ts ->
                          return (t:ts)
                     

    ) (return []) ts

  ) >>= \ts' ->

  -- form contraints specifying which must unify:
  
  let zs  = zip ts ts'

      cs  =  foldr
             (\(x, y) -> \cs ->

               case x of

                 -- check for equality among variables in the list;
                 -- form constraints accordingly
                 (CTTyVar _) -> case
                                (lookup x (filter (not . ((==) (x, y))) zs))
                                of

                                  (Just y') -> (TY y, TY y'):cs

                                  Nothing   -> cs

                 -- if no variable, nothing to check
                 _           -> cs

             )
               [] zs

  in
    return (ts', cs)


--
-- straightforward break-out call for inferring case alternatives,
-- accounting for any type constraints that may be implicit
-- in their patterns (e.g. from 'Pause' and 'Done' or lists)
--
-- we pass in the type of the 'of' part of the 'case' expression
-- so as to constrain the use of special patterns, e.g. make
-- sure that we only try to match 'Pause' and 'Done' for resumptions,
-- and list patterns for lists
--
-- identifiers in patterns have the usual lexical scoping rules,
-- i.e. an identifier appearing in the matching pattern of an
-- alternative overrides any identifiers in the outer environment
-- (hence the use of 'inEnv' below)
--

altinfer :: CTTy -> (CTPat, CTExpr) ->
              TE ((CTPat, ANAST), (CTTy, [Constraint]))

altinfer o (p, e) = patinfer p >>= \(rho, (p', (t, cs))) ->
                    inEnv rho (tyinfer e) >>= \(a, (t', cs')) ->
                    return ((p', a), (t', (TY o, TY t):(cs ++ cs')))




--
-- infer the type of a pattern,
-- annoate the pattern,
-- and form a type-environment for
-- typing an associated expression
--
--
patinfer :: CTPat -> TE (TEnv, (CTPat, (CTTy, [Constraint])))

patinfer (PCon x ps _)   = rdEnv >>= \rho ->

                           (
                             foldr
                             (\p -> \m ->
                               patinfer p >>= \(rho', (p', (t, cs))) ->
                               inEnv rho' m >>= \(rho'', (ps', (ts', cs'))) ->
                               return
                                 (rho'',
                                   ((p':ps'), ((t:ts'), cs ++ cs')))
--                                   (ps' ++ [p'], ((ts' ++ [t]), cs ++ cs')))
                             )
                               (rdEnv >>= \rho -> (return (rho, ([],([],[])))))
                                 ps

                           ) >>= \(rho', (ps', (ts, cs))) ->

                           let t    = contypeof (rho x)
                               t'   = foldabs (ts ++ [t])
                               ts'  = init $ unfoldabs (rho x)
                               cs'  = zip (map TY ts') (map TY ts)
                           in
                             return
                               (rho',
                                 (PCon x ps' (contypeof (rho x)),
                                   (t, (TY (rho' x), TY t'):(cs ++ cs'))))



patinfer (PCons p p' _)  = patinfer p >>= \(rho, (q, (t, cs))) ->
                           inEnv rho
                             (patinfer p') >>= \(rho', (q', (t', cs'))) ->
                           return
                             (rho',
                               (PCons q q' (CTListTy t),
                                 (CTListTy t,
                                   (TY (CTListTy t), TY t'):(cs ++ cs'))))


patinfer (PList ps _)    = newtyvar >>= \v ->
                           rdEnv >>= \rho ->

                           (
                             foldr
                             (\p -> \m ->
                               patinfer p >>= \(rho, (p', (t, cs))) ->
                               inEnv rho m >>= \(rho', (ps', (t', cs'))) ->
                               return (rho',
                                        (p':ps',
                                          (t',
                                            (TY t, TY t'):(cs ++ cs'))))

                             )  (return (rho, ([], (CTTyVar v, [])))) ps

                           ) >>= \(rho', (ps', (t, cs))) ->
                           return
                               (rho',
                                 (PList ps' (CTListTy t),
                                   (CTListTy t, cs)))

patinfer (PTuple p p' _) = patinfer p >>= \(rho, (q, (t, cs))) ->
                           inEnv rho
                             (patinfer p') >>= \(rho', (q', (t', cs'))) ->
                           return
                               (rho',
                                 (PTuple q q' (CTPairTy t t'),
                                   (CTPairTy t t', (cs ++ cs'))))

patinfer (PPause p _)    = patinfer p >>= \(rho, (p', (t, cs))) ->
                           newtyvar >>= \v' ->
                           let v  = CTTyVar v'
                               t' = CTMTy StateTy (CTMTy ResTy v)
                               c  = (TY t, TY t')
                           in
                           return
                               (rho,
                                 (PPause p' (CTMTy ResTy v),
                                   (CTMTy ResTy v, c:cs)))

patinfer (PDone p _)     = patinfer p >>= \(rho, (p', (t, cs))) ->
                           newtyvar >>= \v ->
                           return
                               (rho,
                                 (PDone p' (CTMTy ResTy t),
                                   (CTMTy ResTy (CTTyVar v), cs)))

patinfer (PPauseRe p _)  = patinfer p >>= \(rho, (p', (t, cs))) ->
                           newtyvar >>= \v' ->
                           newtyvar >>= \req' ->
                           newtyvar >>= \rsp' ->
                           let req = CTTyVar req'
                               rsp = CTTyVar rsp'
                               v   = CTTyVar v'
                               re  = ReactTy req rsp
                               t'  = CTPairTy req
                                     (CTAbsTy rsp (CTMTy StateTy (CTMTy re v)))
                               c   = (TY t, TY t')
                           in
                           return
                               (rho,
                                 (PPauseRe p' (CTMTy re v),
                                   (CTMTy re v, c:cs)))

patinfer (PDoneRe p _)   = patinfer p >>= \(rho, (p', (t, cs))) ->
                           newtyvar >>= \v ->
                           newtyvar >>= \req ->
                           newtyvar >>= \rsp ->
                           let re = ReactTy (CTTyVar req) (CTTyVar rsp)
                           in
                           return
                               (rho,
                                 (PDoneRe p' (CTMTy re t),
                                   (CTMTy re (CTTyVar v), cs)))

patinfer (PVar x _)      = newtyvar >>= \v ->
                           let t = CTTyVar v
                           in
                             extenv x t >>= \rho ->
                             return (rho, (PVar x t, (t, [])))

patinfer (PLit l _)      = rdEnv >>= \rho ->

                           case l of
                             (LitInt n)  -> return
                                              (rho,
                                                (PLit l CTIntTy,
                                                  (CTIntTy, [])))

                             (LitBool b)  -> return
                                              (rho,
                                                (PLit l CTBoolTy,
                                                  (CTBoolTy, [])))

                             UnitEl      -> return
                                              (rho,
                                                (PLit l CTUnitTy,
                                                  (CTUnitTy, [])))

patinfer (Wildcard _)     = rdEnv >>= \rho ->
                            newtyvar >>= \v ->
                            let t = CTTyVar v
                            in
                              return (rho, ((Wildcard t), (t, [])))

patinfer (PNest p _)      = patinfer p >>= \ (rho, (p', (t, cs))) ->
                            return (rho, (PNest p t, (t, cs)))




--
-- THE FOLLOWING BLOCK OF CODE IS NOT IN USE
--
-- 2010.02.02 Schulz
--


--
-- check the type of an expression, without annotating;
--
-- this is the simpler predecessor of 'tyinfer':
--
--tycheck :: CTExpr -> TE (CTTy, [Constraint])

tycheck (CTLam x e)       = newtyvar >>= \v ->
                            extenv x (CTTyVar v) >>= \rho -> 
                            inEnv rho (tycheck e) >>= \(t, cs) ->
                            return (CTAbsTy (rho x) t, cs)

tycheck (CTApp e e')      = tycheck e >>= \(t, cs) ->
                            tycheck e' >>= \(t', cs') ->
                            newtyvar >>= \v' ->
                            let v  = CTTyVar v'
                                c  = (t, (CTAbsTy t' v))
                            in
                              return (v, c:(cs ++ cs'))

--
-- monadic expressions:
--

tycheck (CTBind e e')     = tycheck e >>= \(t, cs) ->
                            tycheck e' >>= \(t', cs') ->
                            newconvar >>= \m' ->
                            newtyvar >>= \a' ->
                            newtyvar >>= \b' ->
                            let a = CTTyVar a'
                                b = CTTyVar b'
                                m = MVar m'
                            in
                              return
                                (CTMTy m b,
                                  (t, CTMTy m a):
                                  (t', CTAbsTy a (CTMTy m b)):
                                  (cs ++ cs')
                                )

tycheck (CTNullBind e e') = tycheck e >>= \(t, cs) ->
                            tycheck e' >>= \(t', cs') ->
                            newconvar >>= \m' ->
                            newtyvar >>= \a' ->
                            newtyvar >>= \b' ->
                            let a = CTTyVar a'
                                b = CTTyVar b'
                                m = MVar m'
                            in
                              return
                                (t',
                                  (t, CTMTy m a):
				  (t', CTMTy m b):
				  (cs ++ cs')
                                )

tycheck (CTReturn e)      = tycheck e >>= \(t, cs) ->
                            newconvar >>= \m ->
                            return (CTMTy (MVar m) t, cs)

--
-- cases for special functions with already given types:
--

tycheck (CTGet m)         = rdEnv >>= \rho ->
                            return (CTMTy StateTy (rho m), [])

tycheck (CTPut m e)       = rdEnv >>= \rho ->
                            tycheck e >>= \(t, cs) ->
                            return (CTMTy StateTy CTUnitTy,
                                     (t, rho m):cs)
{-

-- old case: the syntax has changed to explicitly distinguish
-- 'step' in R from 'step' in Re
-- (2010.02.22) Schulz
tycheck (CTStep e)        = tycheck e >>= \(t, cs) ->
                            newtyvar >>= \t' -> 
                            return (CTMTy ResTy (CTTyVar t'),
                                     (t, CTMTy StateTy (CTTyVar t')):cs)
-}


tycheck (CTFix (CTLam _ e))         = tycheck e >>= \(t, cs) ->
                                      newtyvar >>= \a' ->
                                      newtyvar >>= \x' ->
                                      let a = CTTyVar a'

                                          -- type of fully applied 't':
                                          c = unpackabs t

                                          x = CTTyVar x'
                                      in
                                        return
                                          (CTAbsTy a (CTMTy ResTy x),
                                            (c, CTMTy ResTy x):cs)

tycheck (CTFix e)         = error $ "\'fix\' expecting a lambda expression " ++
                                    "but got: " ++ (show e)


--
-- simple expressions:
--                           

tycheck (CTVar x)         = rdEnv >>= \rho ->
                            return (rho x, [])

-- a constructor is assumed to have a type declaration in the environment

--
-- data types have also changed here;
--
-- (2010.02.22) Schulz
--
{-
tycheck (CTCon x)         = rdEnv >>= \rho ->
                            return (rho x, [])
-}

tycheck (CTPrim1ary op e) = let (CTAbsTy a b) = typeOfCTOp op
                            in
                              tycheck e >>= \(t, cs) -> 
                              return (b, (a,t):cs)

tycheck (CTPrim2ary op e e') = let (CTAbsTy a (CTAbsTy b c)) = typeOfCTOp op
                               in
                                 tycheck e >>= \(t, cs) -> 
                                 tycheck e' >>= \(t', cs') -> 
                                 return (c, (a,t):(b,t'):(cs ++ cs'))

tycheck (CTBranch (CTGuard b) e e') = tycheck b >>= \(a, bs) ->
                                      tycheck e >>= \(t, cs) ->
                                      tycheck e' >>= \(t', cs') ->
                                      return 
                                        (t,
                                          (a, CTBoolTy):
                                          (t, t'):
                                          (bs ++ cs ++ cs')
                                        )

tycheck (CTCase _ ((_,e):as))       = tycheck e >>= \(t, cs) ->

                                      -- i.e. tyinfer each alt in the list:
                                      (foldr

                                        (\(_, e) -> \m ->
                                          tycheck e >>= \(t, cs) ->
                                          m >>= \(t', cs') ->
                                          return (t', (t, t'):(cs ++ cs'))
                                        )

                                        (return (t, cs)) as

                                      ) >>= \(t', cs') ->
                                      return (t', cs ++ cs')


tycheck (CTPair e e')               = tycheck e >>= \(t, cs) ->
                                      tycheck e' >>= \(t', cs') -> 
                                      return (CTPairTy t t', cs ++ cs')

--
-- literals:
--

--tycheck (CTLitInt _)      = return (CTIntTy, [])
--tycheck (CTLitBool _)     = return (CTBoolTy, [])
tycheck CTUnit            = return (CTUnitTy, [])

--
-- END UNUSED CODE
--



--
-- unpack an abstraction type to obtain the
-- type obtained on full application:
--
unpackabs :: CTTy -> CTTy
unpackabs (CTAbsTy _ b) = unpackabs b 
unpackabs b = b

--
-- re-pack an abstraction type with a different
-- type to return on full application:
--
repackabs :: CTTy -> CTTy -> CTTy
repackabs e (CTAbsTy a b) = CTAbsTy a (repackabs e b)
repackabs e _ = e

--
-- get the domain of an abstraction type:
--
domof :: CTTy -> CTTy
domof (CTAbsTy a _) = domof a
domof a = a

--
-- get the codomain of an abstraction type:
--
codomof :: CTTy -> CTTy
codomof (CTAbsTy _ b) = b
codomof b = b

--
-- fold a list of types into an abstraction type:
--
foldabs :: [CTTy] -> CTTy
foldabs xs = foldr (\a -> \b -> CTAbsTy a b) (last xs) (init xs)

--
-- unfold an abstraction type into a list:
--
unfoldabs :: CTTy -> [CTTy]
unfoldabs (CTAbsTy a b) = a:(unfoldabs b)
unfoldabs b = [b]


--
-- extract the constructed type resulting from
-- the full application of a constructor
--
contypeof :: CTTy -> CTTy
contypeof (CTAbsTy _ b)   = contypeof b
contypeof t@(CTConTy _ _) = t
contypeof t@(CTRspTy _ _) = t
contypeof t@(CTReqTy _ _) = t


--              --
-- MAIN UNIFIER --
--              --

--
-- this is a slightly modified implementation of the
-- naive unification algorithm presented in
-- [Turbak, Sheldon, Gifford (13.3.2)]
--
--
unify :: [Constraint] -> Subst -> Subst

--
-- unify two monadic types:
--
unify (c@((MV x), (MV y)):cs) s =

  if x == y then unify cs s

  else

  case x of

    (MVar m)      -> let s'  = tweeksol (MV x) (MV y) s
                         cs' = updconstr s' cs
                     in
                       unify cs' s'

    -- since ReactT takes arguments, they must also unify:
    (ReactTy r q) -> case y of
                       (ReactTy r' q') -> let cs' = (TY r, TY r'):
                                                    (TY q, TY q'):cs
                                          in
                                            unify cs' s

                       (MVar m')       -> let s'  = tweeksol (MV y) (MV x) s
                                              cs' = updconstr s' cs
                                          in
                                            unify cs' s'

                       _               -> Failure c

    -- in all other cases, one of x or y must
    -- be a variable, or we are attempting to unify 
    -- unequal, fixed types:
    _             -> case y of
                       (MVar m') -> let s'  = tweeksol (MV y) (MV x) s
                                        cs' = updconstr s' cs
                                     in
                                       unify cs' s'

                       _         -> Failure c


--
-- main unification case:
--
unify (c@((TY x), (TY y)):cs) s =

  if (x == y) then unify cs s  -- if types are identical, constraint is trivial

  -- otherwise, unify:
  else
    case x of

      -- arrow type:
      (CTAbsTy a b) -> case y of
                         (CTAbsTy a' b') -> unify ((TY a, TY a'):
                                                   (TY b, TY b'):cs) s

                         (CTTyVar _)     -> let s'  = tweeksol (TY y) (TY x) s
                                                cs' = updconstr s' cs
                                            in
                                              unify cs' s'

                         _               -> Failure c


      -- non-monadic constructed type:
      (CTConTy q ts) -> case y of
                          (CTConTy q' ts')   -> if (q == q') &&
                                                   (length ts == length ts')

                                                then
                                                  let vs  = map TY ts
                                                      vs' = map TY ts'
                                                  in
                                                    unify ((zip vs vs') ++ cs) s

                                                else Failure c

                          (CTTyVar v)     -> let s'  = tweeksol (TY y) (TY x) s
                                                 cs' = updconstr s' cs
                                             in
                                               unify cs' s'

                          _               -> Failure c



      -- monadic types:

      -- substitute a monadic functor variable (LHS):
      (CTMTy m@(MVar _) t)    -> case y of

                                 -- unify with a monadic type on the RHS:
                                 (CTMTy m' t') -> let s'  = tweeksol (MV m) 
                                                                     (MV m') s
                                                      cs' = updconstr s' $
                                                              (TY t, TY t'):cs
                                                  in
                                                    unify cs' s'



                                 -- or unify with a type variable:
                                 (CTTyVar _) -> let s'  = tweeksol (TY y)
                                                                   (TY x) s
                                                    cs' = updconstr s' cs
                                                in
                                                  unify cs' s'

                                 _            -> Failure c


      -- otherwise, fixed m-type on the LHS:

      -- reactive resumptions; unify the arguments:
      (CTMTy (ReactTy q r) t) -> case y of
                                   (CTMTy (ReactTy q' r') t') -> unify
                                                                  (
                                                                  (TY r, TY r'):
                                                                  (TY q, TY q'):
                                                                  (TY t, TY t'):
                                                                  cs)

                                                                  s

                                   _                           -> unify
                                                                   (
                                                                   (TY y, TY x):
                                                                   cs)

                                                                   s

      -- general case:
      (CTMTy m t)    -> case y of

                          -- substitute a monadic functor variable (RHS):
                          (CTMTy m'@(MVar _) t') -> let s'  = tweeksol (MV m')
                                                                       (MV m) s
                                                        cs' = updconstr s' $
                                                              (TY t, TY t'):cs
                                                    in
                                                      unify cs' s'


                          -- otherwise, both m-types have literal constructors:
                          (CTMTy m' t') -> if m == m'
                                           then
                                             unify ((TY t, TY t'):cs) s
                                           else
                                             Failure c

                          -- unify with a type variable:
                          (CTTyVar _) -> let s'  = tweeksol (TY y) (TY x) s
                                             cs' = updconstr s' cs
                                         in
                                           unify cs' s'


                          _             -> Failure c


      -- reactive requests and responses:
      (CTReqTy q _)  -> case y of

                          -- request part of the same dec always unify:
                          (CTReqTy q' _) -> if q == q'
                                            then
                                              unify cs s
                                            else
                                              Failure c

                          -- otherwise, type variable:
                          (CTTyVar _) ->  let s'  = tweeksol (TY y) (TY x) s
                                              cs' = updconstr s' cs
                                         in
                                           unify cs' s'

                          _             -> Failure c

      (CTRspTy q _)  -> case y of

                          -- response part of the same dec always unify:
                          (CTRspTy q' _) -> if q == q'
                                            then
                                              unify cs s
                                            else
                                              Failure c

                          -- otherwise, type variable:
                          (CTTyVar _) ->  let s'  = tweeksol (TY y) (TY x) s
                                              cs' = updconstr s' cs
                                         in
                                           unify cs' s'

                          _             -> Failure c


      -- list type:
      (CTListTy t)   -> case y of
                          (CTListTy t') -> unify ((TY t, TY t'):cs) s

                          (CTTyVar _)   -> let s'  = tweeksol (TY y) (TY x) s
                                               cs' = updconstr s' cs
                                           in
                                             unify cs' s'

                          _             -> Failure c


      -- pair type:
      (CTPairTy t u) -> case y of

                          (CTPairTy t' u') -> unify ((TY t, TY t'):
                                                     (TY u, TY u'):cs) s

                          (CTTyVar _)      -> let s'  = tweeksol (TY y) (TY x) s
                                                  cs' = updconstr s' cs
                                              in
                                                unify cs' s'

                          _                -> Failure c



      -- otherwise, try for a type variable:
      (CTTyVar a) -> if (occurs a y)
                       then Failure c
                       else
                         let s'  = tweeksol (TY x) (TY y) s
                             cs' = updconstr s' cs
                         in
                           unify cs' s'


      -- same as preceding case, orders reversed:
      _             -> case y of
                         (CTTyVar a) -> if (occurs a x)
                                        then Failure c
                                        else
                                          let s'  = tweeksol (TY y) (TY x) s
                                              cs' = updconstr s' cs
                                          in
                                            unify cs' s'

                         _             -> Failure c

--
-- cannot unify monadic and non-monadic types,
-- except in case (above) of a type variable
--
unify (c@(TY _, MV _):_) _ = Failure c
unify (c@(MV _, TY _):_) _ = Failure c

-- if no more constraints, we're done
unify [] s = s



--
-- check to see if a rigid type variable
-- occurs in another given type
--
occurs :: String -> CTTy -> Bool
occurs _ CTIntTy            = False
occurs _ CTBoolTy           = False
occurs _ CTUnitTy           = False
occurs _ CTStringTy         = False
occurs v (CTTyVar u)        = u == v
occurs v (CTAbsTy t t')     = (occurs v t) || (occurs v t')
occurs v (CTPairTy t t')    = (occurs v t) || (occurs v t')
occurs v (CTListTy t)       = occurs v t
occurs v (CTConTy _ ts)     = or (map (occurs v) ts)
occurs v (CTMTy (MVar m) t) = (m == v) || (occurs v t)
occurs v (CTMTy _ t)        = (occurs v t)

occurs v (CTReqTy u ts)      = (u == v) || any (occurs v) (concat $ map snd ts)
occurs v (CTRspTy u ts)      = (u == v) || any (occurs v) (concat $ map snd ts)

occurs v t = error $ show t



--                --
-- INITIALIZATION --
--                --


--
-- gather all constraints imposed by
-- explicit type signatures;
--
-- functions are identified by the type
-- variables they are marked with in 'markfuns'
--
mksigconstraints :: TEnv -> [TySig] -> [Constraint]
mksigconstraints rho ds =

  foldr
    (\(TySig f t) -> \cs -> (TY $ rho f, TY t):cs)
      [] ds


--
-- rewrite constructed types as expressly
-- monadic types, when appropriate, in the
-- type signatures
--
-- this is necessary due to an idiosyncracy
-- of the parser, which parses monadic types
-- in type signatures in the same way it
-- parses any other constructed types;
-- since this is more a type than a syntactic
-- distinction, it makes more sense to make
-- the change here, than in the parser
--
rwmconsigs :: TEnv -> [TySig] -> [TySig]
rwmconsigs rho =

  let rw = (\t ->

             case t of
               -- this is the important case: change a constructed type
               -- to an explicitly monadic type:
               (CTConTy (TyCon c) [t']) -> case (rho c) of
                                          
                                             -- if c matches a monad, replace:
                                             (CTMTy m _) -> (CTMTy m
                                                              (rw t'))

                                             -- otherwise, continue:
                                             _           -> CTConTy (TyCon c)
                                                                    [rw t']

               (CTConTy c ts) -> CTConTy c (map rw ts)

               -- this case shouldn't happen, but this is
               -- not really the place to check for it:
               (CTMTy m t)               -> CTMTy m (rw t)

               -- other types that need to run through:
               (CTAbsTy t t')            -> CTAbsTy (rw t) (rw t')
               (CTPairTy t t')           -> CTPairTy (rw t) (rw t')

               -- leave everything else alone:
               _                         -> t
           )
  in
    foldr
      (\(TySig f t) -> \cs -> (TySig f (rw t)):cs) []

--
-- same as above, but for monads in data declarations
--
rwmcondats :: TEnv -> [DataDec] -> [DataDec]
rwmcondats rho =

  let rw  = (\t ->

             case t of
               -- this is the important case: change a constructed type
               -- to an explicitly monadic type:
               (CTConTy (TyCon c) [t']) -> case (rho c) of
                                          
                                             -- if c matches a monad, replace:
                                             (CTMTy m _) -> (CTMTy m t')

                                             -- otherwise, continue:
                                             _           -> CTConTy (TyCon c)
                                                                    [rw t']

               (CTConTy c ts) -> CTConTy c (map rw ts)

               -- this case shouldn't happen, but this is
               -- not really the place to check for it:
               (CTMTy m t)               -> CTMTy m (rw t)

               -- other types that need to run through:
               (CTAbsTy t t')            -> CTAbsTy (rw t) (rw t')
               (CTPairTy t t')           -> CTPairTy (rw t) (rw t')

               -- leave everything else alone:
               _                         -> t
           )

      rwd = \as ->

               foldr
               (\(c', ts) -> \as' ->

                 let ts' = foldr
                           (\t -> \ts' ->

                             (rw t):ts'

                           )
                             [] ts
                 in
                   (c', ts'):as'

               ) [] as


      rws  = \ps ->

               foldr
               (\((c, ts), (c', ts')) -> \ps' ->

                 let rwt = foldr
                           (\t -> \ts'' ->

                             (rw t):ts''

                           )
                             []

                     ws  = rwt ts
                     ws' = rwt ts'

                 in
                   ((c, ws), (c', ws')):ps'

               )
                 [] ps


      rwd' = \d -> case d of
                    (DataDec c xs as) -> DataDec c xs (rwd as)
                    (SigDec c ps)     -> SigDec c (rws ps)


  in
    foldr
      (\d -> \ds -> (rwd' d):ds) [] 


--
-- mark each declared function with
-- a unique type variable, to be resolved later;
--
-- functions are initially marked with abstraction types
-- according to how many arguments they are given;
--
markfuns :: [FunDec] -> TE TEnv
markfuns ds =

  foldr
  (\(FunDec f xs e) -> \m ->

    newtyvar >>= \v ->
    extenv f (CTTyVar v) >>= \rho ->
    inEnv rho m

  ) (rdEnv) ds


--
-- make an environment corresponding to
-- the declared types of the elements of the
-- state monad:
--
-- this folds all of the declarations
-- at once, ignoring non-state declarations
--
-- note that memory layer names are bound to the base
-- type of their elements, e.g.
--
--  MemT N (Int) M
--
-- results in the binding M |-> Int
--
-- Type synonyms appearing in monad declarations are
-- also resolved on this pass; hence the need for the first arg;
--
mkstatetys :: [MonadDec] -> TE TEnv
mkstatetys =

  let st = (\d -> 
             case d of
               (CTStateT _ ks) -> foldr
                                   (\(_, (x, t)) -> \m ->

                                     extenv x t >>= \rho ->
                                     inEnv rho m


                                   ) (rdEnv) ks
  
               _               -> rdEnv
           )
  in

    foldr
    (\d -> \r ->

      (st d) >>= \rho ->
      inEnv rho r

    ) rdEnv


--
-- bind the identifiers in the monad declarations
-- to their corresponding monadic constructors,
-- i.e. 'K', 'R', or 'Re'
--
-- note that the extension to the environment
-- is a little quirky; the identifier in the
-- declaration is mapped to an application
-- of its corresponding monadic functor to
-- a generic type variable.
--
--
mkmconenv :: [MonadDec] -> TE TEnv
mkmconenv =

  let st = (\d -> 

             newtyvar >>= \a' -> 
             let a = (CTTyVar a')
             in

             case d of

               (CTStateT k _)      -> extenv k (CTMTy StateTy a)
                                 
               (CTResT r _)        -> extenv r (CTMTy ResTy a)

               (CTReactT re q r _) -> extenv re (CTMTy (ReactTy q r) a)

           )
  in

    foldr
    (\d -> \r ->

      (st d) >>= \rho ->
      inEnv rho r

    ) rdEnv

--
-- same as above, but for data declarations:
--
--
mkdconenv :: [DataDec] -> TE TEnv
mkdconenv =

  -- bind the type identifier in the declaration,
  -- and bind all constructors to that type:
  let dec x = case x of
                (DataDec (TyCon c) ps cs ) ->
                                      let t = CTConTy (TyCon c) (map CTTyVar ps)
                                      in
                                        extenv c t >>= \rho ->

                                        foldr
                                        (\((TyCon c), ts) -> \m ->

                                          extenv c
                                            (foldabs (ts ++ [t])) >>= \rho ->
                                          inEnv rho m
                    
                                        ) rdEnv cs

      -- the sigdec case is almost identical; it's broken out here
      -- purely to handle the slightly different syntactic structure
      --
      -- note, however, that this environment formation DOES NOT
      -- yet take into account the correct pairing of requests and responses;
      -- this is no great trouble, as yet, since the pairing should be implied
      -- wherever 'signal_Re' is invoked
      --

                (SigDec (TyCon x) ss) ->
                           let t = CTConTy (TyCon x) []
                           in
                             extenv x t >>= \rho ->
  
                             foldr
                             (\((c, ts), (c', ts')) -> \m ->
  
                               let req = CTReqTy x [(c, ts)]
                                   rsp = CTRspTy x [(c', ts')]
                               in

                                 extenv c (foldabs (ts ++ [req])) >>= \rho ->
                                 inEnv rho
                                   (extenv c'
                                     (foldabs (ts' ++ [rsp]))) >>= \rho' ->
                                 inEnv rho' m

                             ) rdEnv ss


  in

    foldr
    (\d -> \r ->

      (dec d) >>= \rho ->
      inEnv rho r

    ) rdEnv





--
-- infer the type of a function:
--
tyinfer_fun :: FunDec -> TE ((CTIdent, [CTIdent]),(ANAST, (CTTy, [Constraint])))
tyinfer_fun (FunDec f xs e) =

  -- associate a unique type variable
  -- to each function parameter:
  (
    foldr
    (\x -> \m -> 
      newtyvar >>= \v ->
      extenv x (CTTyVar v) >>= \rho ->
      inEnv rho m

    ) (rdEnv) xs

  ) >>= \rho -> 

  -- infer the type of the function body:
  inEnv rho (tyinfer e) >>= \(a, (t, cs)) ->

  -- where type of the function must unify according
  -- to the number and type of its parameters:
  let t' = foldabs ((map rho xs) ++ [t])
  in
    return ((f, xs), 
             (a, 
               (t',
                 cs)))


--
-- substitute all type synonyms appearing
-- in type signatures:
--
--
resolvetysigs :: [TypeDec] -> [TySig] -> [TySig]
resolvetysigs ds ss =
  let res = (\d@(TypeDec c t) -> \sig ->

    -- we presently assume that type synonyms
    -- do not appear in other type synonyms.
    -- Although this assumption is not especially
    -- well justified, it's a lah-di-dah kind of detail
    -- better left for later polishing
    -- 
    -- (2010.01.26) Schulz

              case sig of
                (CTAbsTy a b)      -> CTAbsTy (res d a) (res d b)

                t'@(CTConTy c' []) -> if c == c'
                                      then t
                                      else t'

                (CTConTy c' ts)    -> CTConTy c' (map (res d) ts)

                (CTMTy m t')       -> CTMTy m (res d t')

                (CTPairTy t' t'')  -> CTPairTy (res d t') (res d t'')

                (CTListTy t)       -> CTListTy (res d t)

                x                  -> x
            )
  in
    map
      (\(TySig f t) ->

        TySig f $
        (foldr
          (\sym -> \sig -> res sym sig) t ds)

      ) ss


--
-- flatten the hierarchy of type synonym declarations
-- by making the appropriate substitutions between type signatures
--
resolvetysyms :: [TypeDec] -> [TypeDec]
resolvetysyms (t:ts) =


  -- NOTE: this is an off-the-cuff coding,
  -- and may diverge in the instance of
  -- mutually dependent type declarations,
  -- e.g. "type A = B; type B = A;",
  -- or cause problems elsewhere
  --
  -- 2010.04.30 Schulz

  let res    = \syms -> \t ->
                  case t of
                    (CTAbsTy a b)      -> CTAbsTy (res syms a) (res syms b)

                    t'@(CTConTy c' []) -> case (lkptysym c' syms) of
                                            (Just t) -> t
                                            _        -> t'

                    (CTConTy c' ts)    -> CTConTy c' (map (res syms) ts)

                    (CTMTy m t')       -> CTMTy m (res syms t')

                    (CTPairTy t' t'')  -> CTPairTy (res syms t') (res syms t'')

                    (CTListTy t)       -> CTListTy (res syms t)

                    x                  -> x

      ressym = \syms' -> \(TypeDec c t) -> TypeDec c (res syms' t)
      t' = ressym ts t

  in
   t':(resolvetysyms (map (ressym [t']) ts))

resolvetysyms [] = []


resolvemontys :: [TypeDec] -> [MonadDec] -> [MonadDec]
resolvemontys ts ms = 
  let st = (\d ->
             case d of
               (CTStateT k ks) -> CTStateT k $
                                   foldr
                                   (\(l, (x, t)) -> \ms ->

                                     case t of
                                       (CTConTy c []) -> case lkptysym c ts of
                                                           (Just t') -> (l,
                                                                          (x,
                                                                            t'))
                                                                        :ms

                                                           _         -> (l,
                                                                          (x,
                                                                            t))
                                                                        :ms

                                       _              -> (l, (x, t)):ms


                                   ) [] ks

               _               -> d
           )
  in

    foldr
    (\d -> \r ->

      (st d):r

    ) [] ms


resolvedattys :: [TypeDec] -> [DataDec] -> [DataDec] 
resolvedattys ts ds =


  -- NOTE: this is an off-the-cuff coding,
  -- and may diverge in the instance of
  -- mutually dependent type declarations,
  -- e.g. "type A = B; type B = A;",
  -- or cause problems elsewhere
  --
  -- 2010.04.30 Schulz

  let res    = \syms -> \t ->
                  case t of
                    (CTAbsTy a b)      -> CTAbsTy (res syms a) (res syms b)

                    t'@(CTConTy c' []) -> case (lkptysym c' syms) of
                                            (Just t) -> t
                                            _        -> t'

                    (CTConTy c' ts)    -> CTConTy c' (map (res syms) ts)

                    (CTMTy m t')       -> CTMTy m (res syms t')

                    (CTPairTy t' t'')  -> CTPairTy (res syms t') (res syms t'')

                    (CTListTy t)       -> CTListTy (res syms t)

                    x                  -> x

      resdat = \syms -> \d ->
                 case d of
                   (DataDec c xs ts) -> let ts' = foldr
                                                  (\(c', t') -> \ts' -> 

                                                    (c',(map (res syms) t')):ts'

                                                  )
                                                    [] ts
                                        in
                                          DataDec c xs ts'

                   (SigDec c cs)     -> let cs' = foldr
                                                  (\((x, ts), (x', ts')) ->
                                                   \cs' ->

                                                    let rs  = map (res syms) ts
                                                        rs' = map (res syms) ts'
                                                    in
                                                      ((x, rs), (x', rs')):cs'
                                                  )
                                                    [] cs
                                        in
                                          SigDec c cs'

  in
    map (resdat ts) ds



--
-- map a type substitution onto the annotated syntax tree:
--
--
resolve :: (CTTy -> CTTy) -> ANAST -> ANAST

resolve s (CTAppAN e e' t) = CTAppAN (resolve s e) (resolve s e') (s t)
resolve s (CTLamAN x e t)  = CTLamAN x (resolve s e) (s t)

resolve s (CTBindAN e e' t)     = CTBindAN (resolve s e) (resolve s e') (s t)
resolve s (CTNullBindAN e e' t) = CTNullBindAN
                                    (resolve s e) (resolve s e') (s t)
resolve s (CTReturnAN e t)      = CTReturnAN (resolve s e) (s t)


resolve s (CTGetAN x t)        = CTGetAN x (s t)
resolve s (CTPutAN x e t)      = CTPutAN x (resolve s e) (s t)
resolve s (CTPopAN x t)        = CTPopAN x (s t)
resolve s (CTPushAN x e t)     = CTPushAN x (resolve s e) (s t)
resolve s (CTReadAN x i t)     = CTReadAN x (resolve s i) (s t)
resolve s (CTWriteAN x i e t)  = CTWriteAN x (resolve s i) (resolve s e) (s t)

resolve s (CTStepAN e t)        = CTStepAN (resolve s e) (s t)
resolve s (CTResumeAN e t)      = CTResumeAN (resolve s e) (s t)
resolve s (CTResumeReAN e e' t) = CTResumeReAN
                                    (resolve s e) (resolve s e') (s t)
resolve s (CTLoopAN e t)        = CTLoopAN (resolve s e) (s t)
resolve s (CTBreakAN e t)       = CTBreakAN (resolve s e) (s t)
resolve s (CTFixAN e t)         = CTFixAN (resolve s e) (s t)

resolve s (CTSignalAN e t)      = CTSignalAN (resolve s e) (s t)
resolve s (CTGetReqAN e t)      = CTGetReqAN (resolve s e) (s t)

resolve s (CTPrim1aryAN op e t)    = CTPrim1aryAN op (resolve s e) (s t)
resolve s (CTPrim2aryAN op e e' t) = CTPrim2aryAN op
                                       (resolve s e) (resolve s e')  (s t)

resolve s (CTPrim3aryAN op e e' e'' t) = CTPrim3aryAN op
                                           (resolve s e)
                                           (resolve s e')
                                           (resolve s e'')  (s t)

resolve s (CTBranchAN b e e' t) = CTBranchAN (resolve s b)
                                             (resolve s e) (resolve s e') (s t)

resolve s (CTCaseAN e as t) = CTCaseAN (resolve s e)
                                 (map (\(x, y) -> (x, resolve s y)) as) (s t)

resolve s (CTPairAN e e' t) = CTPairAN (resolve s e) (resolve s e') (s t)
resolve s (CTListAN es t)   = CTListAN (map (resolve s) es) (s t)

resolve s (CTVarAN x t)    = CTVarAN x (s t)
resolve s (CTConAN x as t) = CTConAN x (map (resolve s) as) (s t)

resolve s (CTLitAN l t)     = CTLitAN l (s t)

resolve s (CTUnitAN t)      = CTUnitAN (s t)



lkptysym :: TyCon -> [TypeDec] -> Maybe CTTy
lkptysym c ((TypeDec c' t):ts) = if c' == c then Just t else lkptysym c ts
lkptysym _ []                  = Nothing


-- THIS IS THE END OF THE FILE --
