--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/interpreters/InterpE.hs
--
-- a monadic-style interpreter for PCF;
--
-- iteration one: the environment monad
--
-- put here (2010.10.25)
--
-- Schulz
--

module Interpreters.InterpE where

import Prelude 

import PCF.Syntax
import MonadicConstructions

--
-- values in the identity monad:
--
data V_E = Wrong 
       | Num Int
       | Bol Bool
       | Cl Name Env Term
       | RecCl Name Env Term

instance Show V_E where
    show Wrong         = "Wrong"
    show (Num i)       = show i
    show (Bol b)       = show b
    show (Cl x _ _)    = "<closure " ++ x ++ ">"
    show (RecCl x _ _) = "<closure " ++ x ++ ">"

type Env = [(Name, V_E)]


type E a = EnvT Env Id a

--
-- the interpreter:
--
interp_e :: Term -> V_E
interp_e t = deId (deENV (interp t) initenv)

initenv = []

interp :: Term -> E V_E
interp (Lam x t)  = mkfun x t

interp (App t t') = interp t >>= \f ->
                    interp t' >>= \a ->
                    apply f a

interp (Inc t)    = interp t >>= \n ->
                    case n of
                      (Num n) -> return (Num (n + 1))
                      _       -> return Wrong

interp (Dec t)    = interp t >>= \n ->
                    case n of
                      (Num n) -> return (Num (n - 1))
                      _       -> return Wrong

interp (ZTest t)  = interp t >>= \n ->
                    case n of
                      (Num 0) -> return (Bol True)
                      (Num _) -> return (Bol False)
                      _       -> return Wrong


interp (EF t t' t'') = interp t >>= \b ->
                       case b of
                         (Bol False) -> interp t''
                         (Bol True)  -> interp t'
                         _           -> return Wrong


interp (Mu x t)   = rdEnv >>= \rho ->
                    let rho' = xEnv rho x (RecCl x rho (Mu x t))
                    in
                      inEnv rho' (interp t)

interp (Var x)    = appEnv x >>= \v' ->
                    case v' of
                      (RecCl x' rho' t) -> inEnv rho' (interp t)
                      v                 -> return v


interp (Con n)    = return (Num n)

interp (Bit b)    = return (Bol b)

------------ Generalized Form

xEnv :: Env -> Name -> V_E -> Env
xEnv rho x v = (x, v):rho

--
-- apply the environment:
--
lkp :: Name -> Env -> E V_E
lkp x ((y,b):bs) = if x == y then return b else lkp x bs
lkp x [] = return Wrong

appEnv :: Name -> E V_E
appEnv n = rdEnv >>= \rho -> lkp n rho

--
-- form an application:
--
apply :: V_E -> V_E -> E V_E
apply (Cl x rho t) v    = let rho' = xEnv rho x v
                          in
                            inEnv rho' (interp t)

apply (RecCl x rho t) v = let rho' = xEnv rho x v 
                          in
                            inEnv rho' (interp t)

apply _ _       = return Wrong


--
-- create a function from an abstraction:
--
mkfun :: Name -> Term -> E V_E
mkfun x t = rdEnv >>= \rho -> return (Cl x rho t)



-- THIS IS THE END OF THE FILE --
