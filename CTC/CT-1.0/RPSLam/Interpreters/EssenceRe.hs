{-# LANGUAGE NoMonomorphismRestriction #-}
module EssenceRe where

import Prelude
import MonadicConstructions hiding (inEnv,rdEnv)
import EssenceSyn
import System.IO.Unsafe

------------
-- Values --
------------

data V = Wrong 
       | Num Int
       | Cl Name Env (Re V)

-- Actually, we *do* need to use closures rather than functions as
-- Re has no environment component.

instance Show V where
    show Wrong      = "Wrong"
    show (Num i)    = show i
    show (Cl _ _ _) = "<function>"

--------------------------
-- Requests & Responses --
--------------------------

data Req = Cont              -- Continue
         | MkCl Name (Re V)  -- Make closure
         | Ap V V            -- Apply
         | LkUp Name         -- Look up name

data Rsp = Ack               -- Acknowledge
         | Val V             -- Return value

---------------
-- The monad --
---------------

type K   = Id                -- *********
type R   = ResT K            -- *********
type Re  = ReactT Req Rsp K  -- *********

etaR :: a -> R a
etaR = Done

etaRe :: a -> Re a
etaRe = D

etaK :: a -> K a
etaK = return

---------------------------------
---  Extra Monadic Structure  ---
---------------------------------

signalV :: Req -> Re V
signalV q = P (q, \ (Val v) -> etaK $ etaRe $ v)

stepR :: K a -> R a
stepR phi = Pause (phi >>= (etaK . etaR))

------------------
-- Environments --
------------------

type Env = [(Name,V)]

xEnv :: Env -> Name -> V -> Env
xEnv rho n phi = (n,phi):rho

lkup x ((y,b):bs) = if x==y then b else lkup x bs

-----------------
-- The handler --
-----------------

loop :: (Re V -> R (Re V)) -> Re V -> R V
loop f (D v) = Done v
loop f phi   = (f phi) >>= loop f

go :: Env -> Re V -> R V
go rho = loop $ hand rho  

unfold :: Monad a => (b -> Bool) -> (b -> ResT a c) -> (b -> c -> b) -> b -> ResT a ()
unfold p h t x = if p x then Done () else h x >>= unfold p h t . (t x)

getsig (P(q,r))  = q
getsig (P(q,r))  = q
getcont (P(q,r)) = r
getcont (P(q,r)) = r
step phi         = Pause (phi >>= return . Done)


{-
data Req = Cont              -- Continue
         | MkCl Name (Re V)  -- Make closure
         | Ap V V            -- Apply
         | LkUp Name         -- Look up name

data Rsp = Ack               -- Acknowledge
         | Val V             -- Return value
handle :: (Domain,Req,Re (),System) -> (R (Re ()),System)
handle (Hi,Cont,t,sys)                = (stepHi (getcont t Ack),sys)
handle (Lo,Cont,t,sys)                = (stepLo (getcont t Ack),sys)
handle (Hi,Rcv,t,sys@(_,_,[]))        = (return t,sys)
handle (Hi,Rcv,t,sys@(ts,ls,(h:hs)))  = (stepHi (getcont t (Rcvd h)),(ts,ls,hs))
handle (Lo,Rcv,t,sys@(_,[],_))        = (return t,sys)
handle (Lo,Rcv,t,sys@(ts,(l:ls),hs))  = (stepLo (getcont t (Rcvd l)),(ts,ls,hs))
handle (Hi,(Bcst m),t,sys@(ts,ls,hs)) = (stepHi (getcont t Ack),(ts,ls,m:hs))
handle (Lo,(Bcst m),t,sys@(ts,ls,hs)) = (stepLo (getcont t Ack),(ts,m:ls,m:hs))

-}

--
-- the idea here is to have a call stack (t:ts) and environment stacks (rhos) 
-- in the System
--
type System = (Req,[Re V],[Env])

handle (Cont,t:ts,rhos)               = (getcont t Ack,rho)
handle (MkCl n phi,t:ts,rhos)         = (getcont t (Val (Cl n rho phi)),ts,rho)
handle (Ap (Cl n rho' phi) v,ts,rhos) = (getsig phi,phi:ts,xEnv rho n v : rhos)

hand :: Env -> Re V -> R (Re V)
hand rho (D v)                         = return (D v)
hand rho (P (Cont,r))                  = stepR (r Ack)
hand rho (P (MkCl n phi, r))           = stepR (r (Val (Cl n rho phi)))
hand rho (P (Ap (Cl n rho' phi) v, r)) = go (xEnv rho' n v) phi >>= stepR . r . Val

hand rho (P (Ap _ v, r))               = stepR (r (Val Wrong))
hand rho (P (LkUp n,r))                = stepR (r (Val (lkup n rho))) 

run (Pause phi) = phi >>= run
run (Done v)    = return v

mkfun :: Name -> Re V -> Re V
mkfun n phi = signalV $ MkCl n phi

appEnv :: Name -> Re V
appEnv n = signalV $ LkUp n

apply :: V -> V -> Re V
apply f v = signalV $ Ap f v

---------------------
-- The interpreter --
---------------------

add :: V -> V -> Re V
add (Num i) (Num j) = return (Num (i+j))
add _ _             = return Wrong

interp :: Term -> Re V
interp (Var x)   = appEnv x
interp (Con i)   = return (Num i)
interp (Add u v) = interp u >>= \a ->
                   interp v >>= \b ->
                      add a b
interp (Lam x v) = mkfun x (interp v)
interp (App t u) = interp t >>= \f ->
                   interp u >>= \a ->
                      apply f a

doit :: Term -> String
doit t = show v where
             v = deId $ run (go [] (interp t))

extreme = map doit unittests             
unittests = [lottalets,ex,ex1,ex2,ex3,ex4]             