--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/interpreters/PCF.hs
--
-- a pure-functional interpreter for PCF;
--
-- top-level specification for RPS-compilation paper
--
-- put here (2010.10.24)
--
-- Schulz
--

module PCF.DefInterp where

import PCF.Syntax

import Prelude 

---------------------
-- Language syntax --
---------------------


data V = Wrong 
       | Num Int
       | Bol Bool
       | Cl Name Env Term
       | RecCl Name Env Term

instance Show V where
    show Wrong         = "Wrong"
    show (Num i)       = show i
    show (Bol b)       = show b
    show (Cl x _ _)    = "<closure " ++ x ++ ">"
    show (RecCl x _ _) = "<recclosure "  ++ x ++ ">"

type Env = [(Name,V)]


--                 --
-- THE INTERPRETER --
--                 --

interp_pcf :: Term -> V
interp_pcf = interp initenv

initenv = []

interp :: Env -> Term -> V
interp rho (Lam x t)  = mkfun rho x t

interp rho (App t t') = let f = interp rho t
                            a = interp rho t'
                        in
                          apply f a

interp rho (Inc t)    = let n = interp rho t
                        in
                          case n of
                            (Num n') -> Num (n' + 1)
                            _        -> Wrong

interp rho (Dec t)    = let n = interp rho t
                        in
                          case n of
                            (Num n') -> Num (n' - 1)
                            _        -> Wrong

interp rho (ZTest t)     = let n = interp rho t
                           in
                             case n of
                               (Num 0) -> Bol True
                               (Num _) -> Bol False
                               _       -> Wrong

interp rho (EF t t' t'') =  let b = interp rho t
                            in
                              case b of
                                (Bol False) -> interp rho t''
                                (Bol True)  -> interp rho t'
                                _           -> Wrong

interp rho (Mu x t)   = let rho' = xEnv rho x (RecCl x rho (Mu x t))
                        in
                          interp rho' t

interp rho (Var x)    = case (appenv x rho) of
                          (RecCl x' rho' t) -> interp rho' t
                          v                 -> v

interp rho (Con n)    = Num n

interp rho (Bit b)    = Bol b

------------ Generalized Form

xEnv :: Env -> Name -> V -> Env
xEnv rho x v = (x, v):rho

--
-- apply the environment:
--
appenv :: Name -> Env -> V
appenv x ((y,b):bs) = if x == y then b else appenv x bs
appenv x [] = Wrong


--
-- form an application:
--
apply :: V -> V -> V
apply (Cl x rho t) v    = interp (xEnv rho x v) t
apply (RecCl x rho t) v = interp (xEnv rho x v) t
apply _ _               = Wrong

--
-- create a function from an abstraction:
--
mkfun :: Env -> Name -> Term -> V
mkfun rho x t = Cl x rho t


-- THIS IS THE END OF THE FILE --
