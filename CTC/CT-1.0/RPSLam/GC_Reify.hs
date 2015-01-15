module RPSLam.GC_Reify where 

import CT.Syntax
import CT.MonadicConstructions
import RPSLam.EssenceSyn
import RPSLam.GC hiding (Env)

import RPSLam.ULamParser

import CT.PPT

{-
In the following, the interface functions (e.g., add, appEnvRe, mkfunRe, etc.)
could be reified as well. For example, corresponding to appEnvRe would be:
	appEnvReReify :: Name -> CTExpr
	appEnvReReify x = CTBind (CTSignal (CTVar "rdenvRe")) (...))

Or, you can keep the interface function as an uninterpreted variable.
Either way works.  I think the latter will probably be easier: just emit the
code for each call.
-}

type SignalName = String


data Env = Env
type Store   = Int
newtype M a = M (Env -> Store -> (a,Store))
deM (M x) = x
instance Monad M where
    return x = M (\ r s -> (x,s))
    (M x) >>= f = M (\ r s -> let (v,s1) = x r s in deM (f v) r s1)

update :: (Store -> Store) -> M Store
rdenv  :: M Env
inenv  :: Env -> M a -> M a

update f      = M (\ r s -> (f s,f s))
rdenv         = M (\ r s -> (r,s))
inenv r (M x) = M (\ _ -> x r)

runM (M x) = fst $ x Env 0

reify = putStrLn . ppt . runM . interp_

reify_show = putStrLn . show . runM . interp_

--
-- used to pass the output string to the CT front-end:
--
reify_term = ppt . runM. interp_



test = map CTVar ["fee", "fie", "foe", "fum"]

gensym = update (\ i -> i + 1) >>= return . ("x" ++) . show

compose vs = gensym >>= \ v -> return (CTLam v (fullapply (CTVar v) vs))

fullapply applicand = foldr CTApp applicand 

--
-- Careful: I'm treating stepRe as a variable.
-- This doesn't jibe with the syntax as Ben defined it.
-- It just makes the programming easier.
--
mkstepRe     = CTVar "step_Re"
mkread       = CTVar "read"
mkproj       = CTVar "prj"
mklkup x     = CTApp (CTVar "lkup") (CTVar x)
mkcon0 x     = CTCon x []
mksignalV_ x = CTApp (CTVar "signalV") x

notype = CTTyVar "crud"

appEnvRe_ :: Name -> M CTExpr
appEnvRe_ x = compose rhs >>= return . CTBind (mksignalV_ $ mkcon0 "RdEnv") 
    where rhs = [mkstepRe,mkread,mklkup "x",mkproj]
--appEnvRe_ x = compose rhs >>= return . CTBind (CTSignal $ mkcon0 "RdEnv") 
--    where rhs = [mkstepRe,mkread,mklkup "x",mkproj]

mkCl x e = interp_ e >>= \ pi_e -> 
           gensym        >>= \ r -> 
--              return (CTLam r (CTCon "Cl" [CTVar x,pi_e,CTVar r]))
              return (CTLam r (CTCon "Cl" [CTLit (LitString x),pi_e,CTVar r]))

--
-- N.b., in the above, (CTVar "return") is used instead of CTReturn.
-- This introduces a little confusion that could be cleared up by a simplifier.
--
mkfunRe_ :: Name -> Term -> M CTExpr
mkfunRe_ x e = mkCl x e    >>= \ clxe ->
                   let
                      rhs = [CTVar "return",clxe,mkproj]
                   in
                      compose rhs >>= \ f ->   
--                      return (CTBind (CTSignal (mkcon0 "RdEnv")) f)
                      return (CTBind (mksignalV_ (mkcon0 "RdEnv")) f)

xEnv_ :: CTExpr -> CTExpr -> CTExpr -> CTExpr
xEnv_ rho x l = let l' = CTApp (CTVar "unwrapNum") l
                in
                  CTApp (CTApp (CTApp (CTVar "xEnv") rho) x) l'

inenvRe_ :: CTExpr -> CTExpr -> CTExpr
--inenvRe_ rho x = CTSignal (CTCon "InEnv" [rho,x])
inenvRe_ rho x = mksignalV_ (CTCon "InEnv" [rho,x])

storeRe_ :: CTExpr -> CTExpr
--storeRe_ x = CTSignal (CTCon "Store" [x])
storeRe_ x = mksignalV_ (CTCon "Store" [x])


applyRe_ :: CTExpr -> String -> CTExpr -> String -> CTExpr
applyRe_ cl x v x' = CTBind cl (CTLam x (CTCase (CTVar x) [(p,e)]))

   where p = PCon "Cl"
               [PVar "x" notype, PVar "phi" notype,PVar "rho" notype] notype

         e = CTBind v (CTLam x' (CTBind (storeRe_ (CTVar x')) (CTLam "l" $
              inenvRe_
                 (xEnv_ (CTVar "rho") (CTVar "x") (CTVar "l"))
                 (CTVar "phi"))))

{-
applyRe_ :: CTExpr -> CTExpr -> CTExpr
applyRe_ cl v = CTCase cl [(p,e)]

   where p = PCon "Cl"
               [PVar "x" notype, PVar "phi" notype,PVar "rho" notype] notype

         e = CTBind (storeRe_ v) (CTLam "l" $
              inenvRe_
                 (xEnv_ (CTVar "rho") (CTVar "x") (CTVar "l"))
                 (CTVar "phi"))
-}

--
-- this is written according to the CT definition in
-- 'CT-1.0/TestPrograms/gc.ct'
--
signalV_ :: SignalName -> CTExpr
signalV_ sig =
  (CTBind
    (CTSignal (CTVar sig)) (CTLam "rsp"
    (CTCase (CTVar "rsp")
      [
        (PNest (PCon "Val1" [PVar "v" CTUnitTy] CTUnitTy) CTUnitTy,
          CTReturn (CTVar "v")),

        (PNest (PCon "Val2" [PVar "v" CTUnitTy] CTUnitTy) CTUnitTy,
          CTReturn (CTVar "v")),

        (PNest (PCon "Val3" [PVar "v" CTUnitTy] CTUnitTy) CTUnitTy,
          CTReturn (CTVar "v")),

        (PNest (PCon "RdEnvRe" [PVar "e" CTUnitTy] CTUnitTy) CTUnitTy,
          CTReturn (CTCon "Environ" [CTVar "e"]))
      ]
    ))
  )



interp_ :: Term -> M CTExpr
--interp_ (Var x)    = return $ CTApp (CTVar "appEnvRe") (CTVar x)
interp_ (Var x)    = return $ CTApp (CTVar "appEnvRe") (CTLit (LitString x))

interp_ (Con i)    = return $ CTReturn (CTCon "Num" [CTLit (LitInt i)])

interp_ (Add u v)  = interp_ u >>= \ ur ->
                     interp_ v >>= \ vr ->
                     return $
                         (CTBind ur (CTLam "u" $
                          CTBind vr (CTLam "v" $
                             (CTApp 
                                 (CTApp (CTVar "add") (CTVar "u")) 
                                                      (CTVar "v")))))

interp_ (Lam x e)  = mkfunRe_ x e

interp_ (App f t)  = interp_ f >>= \ fr -> 
                     interp_ t >>= \ tr -> 
                     gensym >>= \x -> 
                     gensym >>= \x' -> 
                     return $ applyRe_ fr x tr x'

interp_ (IFZERO t1 t2 t3) = interp_ t1 >>= \ t1_ ->
                            interp_ t2 >>= \ t2_ ->
                            interp_ t3 >>= \ t3_ ->
                            return $
                                CTBind t1_ (CTLam "v" $
                                CTCase (CTVar "v") 
                                     [
                                       (PCon "Num"
                                         [PLit (LitInt 0) notype] notype, t2_),

                                       (PCon "Num"
                                          [Wildcard notype] notype, t3_)
                                     ])

hand_ (CTReturn v)   = CTReturn (CTReturn v)

hand_ (CTBind p@(CTSignal (CTCon "Cont" [])) r) =

  let p' = CTStepRes p
      r' = CTStepRes (hand_ r)
  in
    CTBind p' r'


hand_ (CTBind p@(CTSignal (CTCon "RdEnv" [])) r) =

  let p'     = CTStepRes p
      r'     = CTStepRes (hand_ r)

      getenv = CTStepRes (
                 CTBind
                   (CTGet "Env")
                   (CTLam "RDENV_VAR"
                     (CTReturn (CTCon "Environ" [CTVar "RDENV_VAR"]))))

  in
    CTBind p (CTBind getenv r')


hand_ (CTBind p@(CTSignal (CTCon "InEnv" [rho, phi])) r) =

  let p'     = CTStepRes p
      r'     = CTStepRes (hand_ r)
      phi'   = CTStepRes phi
      mkenv  = CTStepRes (CTPut "Env" rho)
  in
    CTBind p' (CTBind mkenv (CTBind phi' r'))


hand_ (CTBind p@(CTSignal (CTCon "Store" [v])) r) =

  let p'     = CTStepRes p
      r'     = CTStepRes (hand_ r)
      gc     = CTVar "gc"  -- call to gc
      store  = CTStepRes (CTWrite "GC_Var" (CTVar "GC_RET") v)
  in
    CTBind (CTBind gc (CTLam "GC_RET" store)) r'


e0 = App (Lam "x" (Var "x")) (Con 0)
