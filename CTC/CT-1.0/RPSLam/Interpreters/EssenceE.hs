module EssenceE where

import Prelude hiding (lookup)
import MonadicConstructions
import EssenceSyn

{-

As Essence0, but in the Env monad.

-}

------------
-- Values --
------------
data V = Wrong 
       | Num Int
       | Fun (V -> E V)

instance Show V where
    show Wrong   = "Wrong"
    show (Num i) = show i
    show (Fun _) = "<function>"

---------------
-- The monad --
---------------
type E  = EnvT Env Id

------------------
-- Environments --
------------------
type Env = [(Name,V)]

xEnv :: Env -> Name -> V -> Env
xEnv rho n v = (n,v):rho

lookup :: Name -> Env -> E V
lookup x []         = return Wrong
lookup x ((y,b):bs) = if x==y then return b else lookup x bs

inExtEnv :: Name -> V -> E V -> E V
inExtEnv n v phi = rdEnv >>= \rho ->
                       inEnv (xEnv rho n v) phi

mkfun :: Name -> E V -> E V
mkfun n phi = rdEnv >>= \ rho ->
                      return (Fun $ \ v -> inEnv (xEnv rho n v) phi)

appEnv :: Name -> E V
appEnv n = rdEnv >>= lookup n

apply :: V -> V -> E V
apply (Fun f) v = f v

---------------------
-- The interpreter --
---------------------

add :: V -> V -> E V
add (Num i) (Num j) = return (Num (i+j))
add _ _             = return Wrong

interp :: Term -> E V
interp (Var x)   = appEnv x
interp (Con i)   = return (Num i)
interp (Add u v) = interp u >>= \a ->
                   interp v >>= \b ->
                      add a b
interp (Lam x v) = mkfun x (interp v)
interp (App t u) = interp t >>= \f -> 
                   interp u >>= \a -> 
                      apply f a

test :: Term -> String
test t = show (deId (deENV (interp t) []))
