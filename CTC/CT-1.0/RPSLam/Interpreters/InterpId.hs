--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/interpreters/InterpId.hs
--
-- a monadic-style interpreter for PCF;
--
-- iteration zero: the identity monad
--
-- put here (2010.10.25)
--
-- Schulz
--

module Interpreters.InterpId where

import Prelude 

import PCF.Syntax
import MonadicConstructions

--
-- values in the identity monad:
--
data V_Id = Wrong 
       | Num Int
       | Bol Bool
       | Cl Name Env Term
       | RecCl Name Env Term

instance Show V_Id where
    show Wrong          = "Wrong"
    show (Num i)        = show i
    show (Bol b)        = show b
    show (Cl x _ _)     = "<closure " ++ x ++ ">"
    show (RecCl x _  _) = "<recclosure " ++ x ++ ">"

type Env = [(Name, V_Id)]


--
-- the interpreter:
--
interp_id :: Term -> V_Id
interp_id t = deId (interp initenv t)

initenv = []

interp :: Env -> Term -> Id V_Id
interp rho (Lam x t)  = mkfun rho x t

interp rho (App t t') = interp rho t >>= \f ->
                        interp rho t' >>= \a ->
                        apply f a

interp rho (Inc t)    = interp rho t >>= \n ->
                        case n of
                          (Num n) -> return (Num (n + 1))
                          _       -> return Wrong

interp rho (Dec t)    = interp rho t >>= \n ->
                        case n of
                          (Num n) -> return (Num (n - 1))
                          _       -> return Wrong

interp rho (ZTest t)     = interp rho t >>= \n ->
                           case n of
                             (Num 0) -> return (Bol True)
                             (Num _) -> return (Bol False)
                             _       -> return Wrong

interp rho (EF t t' t'') = interp rho t >>= \b ->
                           case b of
                             (Bol False) -> interp rho t''
                             (Bol True)  -> interp rho t'
                             _           -> return Wrong


interp rho (Mu x t)   = let rho' = xEnv rho x (RecCl x rho (Mu x t))
                        in
                          interp rho' t

interp rho (Var x)    = appEnv x rho >>= \v' ->
                        case v' of
                          (RecCl x' rho' t) -> interp rho' t
                          v                 -> return v

interp rho (Con n)    = return (Num n)

interp rho (Bit b)    = return (Bol b)


------------ Generalized Form

xEnv :: Env -> Name -> V_Id -> Env
xEnv rho x v = (x, v):rho

--
-- apply the environment:
--
appEnv :: Name -> Env -> Id V_Id
appEnv x ((y,b):bs) = if x == y then return b else appEnv x bs
appEnv x [] = return Wrong


--
-- form an application:
--
apply :: V_Id -> V_Id -> Id V_Id
apply (Cl x rho t) v    = let rho' = xEnv rho x v
                          in
                            interp rho' t

apply (RecCl x rho t) v = let rho' = xEnv rho x v 
                          in
                            interp rho' t

apply _ _               = return Wrong


--
-- create a function from an abstraction:
--
mkfun :: Env -> Name -> Term -> Id V_Id
mkfun rho x t = return (Cl x rho t)



-- THIS IS THE END OF THE FILE --
