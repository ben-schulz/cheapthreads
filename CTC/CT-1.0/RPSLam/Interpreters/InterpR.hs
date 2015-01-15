--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/interpreters/InterpR.hs
--
-- a monadic-style interpreter for PCF;
--
-- iteration two: the environment monad, lifted into the resumption monad
--
-- put here (2010.10.25)
--
-- Schulz
--

module Interpreters.InterpR where

import Prelude 

import PCF.Syntax
import MonadicConstructions

--
-- values in the identity monad:
--
data V_R = Wrong 
       | Num Int
       | Bol Bool
       | Cl Name Env Term
       | RecCl Name Env Term


instance Show V_R where
    show Wrong   = "Wrong"
    show (Num i) = show i
    show (Bol b) = show b
    show (Cl x _ _)    = "<closure " ++ x ++ ">"
    show (RecCl x _ _) = "<closure " ++ x ++ ">"


type Env = [(Name, V_R)]


type R a = ResT (EnvT Env Id) a


--
-- the interpreter:
--
interp_r :: Term -> V_R
interp_r t = deId (deENV (run_R (interp t)) initenv)

initenv = []

interp :: Term -> R V_R
interp (Lam x t)  = mkfun x t

interp (App t t') = interp t' >>= \a ->
                    interp t >>= \f ->
                    apply f a

interp (Inc t)     = interp t >>= \n ->
                     case n of 
                       (Num n) -> return (Num (n + 1))
                       _       -> return Wrong

interp (Dec t)     = interp t >>= \n ->
                     case n of 
                       (Num n) -> return (Num (n - 1))
                       _       -> return Wrong

interp (ZTest t)     = interp t >>= \n ->
                       case n of
                         (Num 0) -> return (Bol True)
                         (Num _) -> return (Bol False)
                         _       -> return Wrong

interp (EF t t' t'') = interp t >>= \b ->
                       case b of
                         (Bol False) -> interp t''
                         (Bol True)  -> interp t'
                         _           -> return Wrong


interp (Mu x t)   = step_R rdEnv >>= \rho -> 
                    let rho' = xEnv rho x (RecCl x rho (Mu x t))
                    in
                      inEnv_R rho' (interp t)


interp (Var x)    = appEnv x >>= \v' ->
                    case v' of
                      (RecCl x' rho' t) -> inEnv_R rho' (interp t)
                      v                 -> return v

interp (Con n)    = return (Num n)

interp (Bit b)    = return (Bol b)


------------ Generalized Form

inEnv_R :: Env -> R V_R -> R V_R
inEnv_R rho = map_R (inEnv rho)

xEnv :: Env -> Name -> V_R -> Env
xEnv rho x v = (x, v):rho

--
-- apply the environment:
--
lkp :: Name -> Env -> R V_R
lkp x ((y,b):bs) = if x == y then return b else lkp x bs
lkp x [] = return Wrong

appEnv :: Name -> R V_R
appEnv n = step_R rdEnv >>= \rho -> lkp n rho

--
-- form an application:
--
apply :: V_R -> V_R -> R V_R
apply (Cl x rho t) v    = let rho' = xEnv rho x v
                          in
                            inEnv_R rho' (interp t)

apply (RecCl x rho t) v = let rho' = xEnv rho x v 
                          in
                            inEnv_R rho' (interp t)

apply _ _       = return Wrong


--
-- create a function from an abstraction:
--
mkfun :: Name -> Term -> R V_R
mkfun x t = step_R (rdEnv >>= \rho -> return (Cl x rho t))

mkrecfun :: Name -> Term -> R V_R
mkrecfun x t = step_R (rdEnv >>= \rho -> return (RecCl x rho t))


-- THIS IS THE END OF THE FILE --
