module EssenceECPS where

import Prelude hiding (lookup)
import MonadicConstructions hiding (rdEnv,inEnv)
import qualified MonadicConstructions as MC
import EssenceSyn

{-

As EssenceE, but CPS'd E monad.

-}


------------
-- Values --
------------
data V = Wrong 
       | Num Int
       | Fun (V -> C V)

instance Show V where
    show Wrong   = "Wrong"
    show (Num i) = show i
    show (Fun _) = "<function>"

---------------
-- The monad --
---------------
type E = EnvT Env Id
type C = ContT String E

rdEnv:: C Env
rdEnv = liftCPS MC.rdEnv

inEnv :: Env -> C a -> C a
--
-- Bill's definition:
--
--inEnv rho (CPS phi) = (CPS (\ k -> MC.inEnv rho (phi k))) 


-- 
-- definition from "Monad Transformers and Modular Interpreters"
-- by Liang, Hudak and Jones, 1995:
--
inEnv rho (CPS phi) =
  (CPS (\ k -> MC.rdEnv >>= \rho' -> MC.inEnv rho (phi (MC.inEnv rho' . k)))) 

-- why doesn't this work?
--
-- Schulz (2010.10.23)
--


------------------
-- Environments --
------------------
type Env = [(Name,V)]

xEnv :: Env -> Name -> V -> Env
xEnv rho n v = (n,v):rho

lookup :: (Monad m) => Name -> Env -> m V
lookup x []         = return Wrong
lookup x ((y,b):bs) = if x==y then return b else lookup x bs

inExtEnv :: Name -> V -> C V -> C V
inExtEnv n v phi = rdEnv >>= \rho ->
                       inEnv (xEnv rho n v) phi

mkfun :: Name -> C V -> C V
mkfun n phi = rdEnv >>= \ rho ->
                      return (Fun $ \ v -> inEnv (xEnv rho n v) phi)

appEnv :: Name -> C V
appEnv n = rdEnv >>= lookup n

apply :: V -> V -> C V
apply (Fun f) v = f v

---------------------
-- The interpreter --
---------------------

add :: V -> V -> C V
add (Num i) (Num j) = return (Num (i+j))
add _ _             = return Wrong

interp :: Term -> C V
interp (Var x)   = appEnv x
interp (Con i)   = return (Num i)
interp (Add u v) = interp u >>= \a ->
                   interp v >>= \b ->
                      add a b
interp (Lam x v) = mkfun x (interp v)
interp (App t u) = interp t >>= \f -> 
                   interp u >>= \a -> 
                      apply f a

--test :: Term -> String
test t = deId $ deENV ((deCPS (interp t)) (return . show)) []
