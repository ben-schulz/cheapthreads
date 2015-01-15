module EssenceReHeap where

import Prelude hiding (read)
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

type K   = StateT Sto Id     -- *********
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

type Env = [(Name,Loc)]           -- ***************

xEnv :: Env -> Name -> Loc -> Env -- ***************
xEnv rho n l = (n,l):rho

lkup x ((y,b):bs) = if x==y then b else lkup x bs

------------------
--  The Heap    --
------------------

type Sto = [(Loc,V)]              -- ***************

writeLoc :: Loc -> V -> K ()
writeLoc l val = u (\s -> (l,val):(rest s))
   where rest s = filter (\ (loc,v) -> loc/= l) s

read :: Loc -> K V
read l = g >>= \s -> etaK (lookupSto l s)
                where lookupSto l s = case lookup l s of
                                          Nothing  -> Wrong
                                          (Just x) -> x

{-
findFreeLoc :: K Loc
findFreeLoc = g >>= \s -> etaK (ffl 0 s)
                  -- This is stupidly inefficient
                  where ffl :: Loc -> Sto -> Loc
                        ffl n sto = case lookup n sto of
                                        Nothing -> n
                                        _       -> ffl (n+1) sto
-}

-- instrumented version
findFreeLoc :: K Loc
findFreeLoc = g >>= \s -> 
              let
                  newloc = ffl 0 s
              in
                  seq (unsafePerformIO (putStrLn $ "Allocating: " ++ show newloc))
                      (etaK newloc)
                  -- This is stupidly inefficient
                  where ffl :: Loc -> Sto -> Loc
                        ffl n sto = case lookup n sto of
                                        Nothing -> n
                                        _       -> ffl (n+1) sto

store :: V -> K Loc
store v = findFreeLoc >>= \ l -> writeLoc l v >> return l

-----------------
-- The handler --
-----------------

loop :: (Re V -> R (Re V)) -> Re V -> R V
loop f (D v) = Done v
loop f phi   = (f phi) >>= loop f

go :: Env -> Re V -> R V
go = loop . hand

hand :: Env -> Re V -> R (Re V)
hand rho (D v)                         = return (D v)
hand rho (P (Cont,r))                  = stepR (r Ack)
hand rho (P (MkCl n phi, r))           = stepR (r (Val (Cl n rho phi)))
hand rho (P (Ap (Cl n rho' phi) v, r)) = stepR (store v) >>= \ l ->
                                     --  ^^^^^^^^^^ ******
                                         go (xEnv rho' n l) phi >>= 
                                             stepR . r . Val
hand rho (P (Ap _ v, r))               = stepR (r (Val Wrong))
hand rho (P (LkUp n,r))                = stepR (read (lkup n rho)) >>= 
                                               stepR . r . Val  -- ******

run (Pause phi) = phi >>= run
run (Done v)    = return v

mkfun :: Name -> Re V -> Re V
mkfun n phi = signalV $ MkCl n phi

appenv :: Name -> Re V
appenv n = signalV $ LkUp n

apply :: V -> V -> Re V
apply f v = signalV $ Ap f v

---------------------
-- The interpreter --
---------------------

add :: V -> V -> Re V
add (Num i) (Num j) = return (Num (i+j))
add _ _             = return Wrong

interp :: Term -> Re V
interp (Var x)   = appenv x
interp (Con i)   = return (Num i)
interp (Add u v) = interp u >>= \a ->
                   interp v >>= \b ->
                      add a b
interp (Lam x v) = mkfun x (interp v)
interp (App t u) = interp t >>= \f ->
                   interp u >>= \a ->
                      apply f a


--doit :: Term -> String
doit t =  v where
             v = fst $ deId $ deST (run (go [] (interp t))) []

-- test and doit appear equal:
extreme = map (\ t -> (doit t)) unittests             
unittests = [lottalets,ex,ex1,ex2,ex3,ex4]             

{-
-- Retained for consistency with EOFP
test :: Term -> String
test t = show v where
             (Fin v) = fst $ deId $ deST (run (handler [] (interp t))) []

-- So we can see the final state of the store
test' :: Term -> (Rsp,Sto)
test' t = deId $ deST (run (handler [] (interp t))) []
-}

-- defunctionalized loop and handler

---data HandlerConfig = H Env (Re V) Sto