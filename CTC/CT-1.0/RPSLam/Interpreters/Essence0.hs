--
-- this is ~/cheapthreads/ctc_working/CT-1.0/RPSLam/interpreters/PCF.hs
--
-- a pure-functional interpreter for Plotkin's PCF;
--
-- top-level specification for RPS-compilation paper
--
-- put here (2010.10.24)
--
-- Schulz
--

module Essence0 where

import Prelude 

type Name = String
data Term = Var Name
          | Con Int
          | Add Term Term
          | Lam Name Term
          | App Term Term

data I a = I a

unitI   :: a -> I a
unitI v = (I v)

bindI :: (I a) -> (a -> I b) -> I b
(I x) `bindI` f = f x

data V = Wrong 
           | Num Int
           | Fun (V -> I V)

instance Show V where
    show Wrong   = "Wrong"
    show (Num i) = show i
    show (Fun _) = "<function>"

type Env = [(Name,V)]

showI :: I V -> String
showI (I v) = show v

ex = App double one
   where double = Lam "x" (Add (Var "x") (Var "x"))
         one    = Con 1

wrong = Add double one
   where double = Lam "x" (Add (Var "x") (Var "x"))
         one    = Con 1

------------ Generalized Form

mkfun :: Env -> Name -> (Env -> I V) -> I V
mkfun e x phi = return (Fun (\ arg -> phi ((x,arg):e)))

instance Monad I where
    return = unitI
    (>>=)  = bindI

appenv :: Name -> Env -> I V
appenv x []         = return Wrong
appenv x ((y,b):bs) = if x==y then return b else appenv x bs

add :: V -> V -> I V
add (Num i) (Num j) = return (Num (i+j))
add _ _             = return Wrong

apply :: V -> V -> I V
apply (Fun k) a = k a
apply _ _       = return Wrong

interp :: Term -> Env -> I V
interp (Var x) e   = appenv x e
interp (Con i) e   = return (Num i)
interp (Add u v) e = interp u e >>= \ a ->
                      interp v e >>= \ b ->
                        add a b
interp (Lam x v) e = mkfun e x (interp v)
interp (App t u) e = interp t e >>= \ f -> 
                      interp u e >>= \ a -> 
                        apply f a

test t = showI (interp t [])


