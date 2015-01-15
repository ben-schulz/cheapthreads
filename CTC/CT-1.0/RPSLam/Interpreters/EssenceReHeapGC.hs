module EssenceReHeapGC where

import Prelude hiding (read)
import MonadicConstructions hiding (inEnv,rdEnv)
import EssenceSyn
import MIR hiding (Name)
import System.IO.Unsafe

{-

As in EssenceReHeap, all variables are heap-allocated. Garbage collection is
performed.

-}

---------------------
-- Language syntax --
---------------------

data V = Wrong 
       | Num Int
       | Cl Name Env (Re V)

-- Actually, we *do* need to use closures rather than functions as
-- Re has no environment component.

instance Show V where
    show Wrong      = "Wrong"
    show (Num i)    = show i
    show (Cl _ _ _) = "<function>"

---------------
-- The monad --
---------------

--- Requests & Responses
data Req = Cont             -- Continue
         | MkCl Name (Re V) -- Make closure
         | Ap V V           -- Apply
         | LkUp Name        -- Look up name

data Rsp = Ack              -- Acknowledge
         | Val V            -- Return value

type K   = StateT Sto Id
type R   = ResT K
type Re  = ReactT Req Rsp K

etaR :: a -> R a
etaR = Done

etaRe :: a -> Re a
etaRe = D

etaK :: a -> K a
etaK = return

etaId :: a -> Id a
etaId = return
                  ---------------------------------
                  ---  Extra Structure with Re  ---
                  ---------------------------------

signal :: Req -> Re Rsp
signal q = P (q, etaK . etaRe)

signalV :: Req -> Re V
signalV q = P (q, \ (Val v) -> etaK $ etaRe $ v)

signull :: Req -> Re ()
signull q = P (q, \ _ -> etaK (etaRe ()))

stepR :: K a -> R a
stepR phi = Pause (phi >>= (etaK . etaR))

---------------------
-- Envs and stores --
---------------------

type Env   = [(Name,Loc)]
type Sto   = [(Loc,V)]
type Stack = [Env]

xEnv :: Env -> Name -> Loc -> Env                                           -- ******
xEnv rho n l = (n,l):rho

writeLoc :: Loc -> V -> K ()
writeLoc l val = u (\s -> (l,val):[(x,y)|(x,y)<-s,x/=l])

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
                  newloc  = ffl 0 s
              in
                  seq (unsafePerformIO (putStrLn $ "Allocating: " ++ show newloc))
                      (etaK newloc)
                  -- This is stupidly inefficient
                  where ffl :: Loc -> Sto -> Loc
                        ffl n sto = case lookup n sto of
                                        Nothing -> n
                                        _       -> ffl (n+1) sto
                        

------------------------
-- Garbage collection --
------------------------

findLiveLocs :: Stack -> [Loc]
findLiveLocs sta = concatMap (map snd) sta

freeDeadLocs :: [Loc] -> Sto -> Sto
freeDeadLocs ls sto = seq freeing
                          (filter (\(l,v) -> l `elem` ls) sto)
     where
         deadlocs = filter (\(l,v) -> not (l `elem` ls)) sto
         freeing  = case deadlocs of
                         [] -> unsafePerformIO (putStr $ "")
                         _  -> unsafePerformIO (putStrLn $ "Freeing: " ++ (show deadlocs) ++ "\n")

gcThreshold :: Int
gcThreshold = 1

gcHelper :: Stack -> Sto -> Sto
gcHelper sta sto = if length sto > gcThreshold 
                   then
                         freeDeadLocs (findLiveLocs sta) sto
                   else
                         sto

gc :: Stack -> K ()
gc stk = u (gcHelper stk)

-----------------
-- The handler --
-----------------

--
-- loop is really a kind of map
--
loop :: (Re V -> R (Re V)) -> Re V -> R V
loop f (D v) = Done v
loop f phi   = (f phi) >>= loop f

go :: Stack -> Re V -> R V
go = loop . hand

store :: V -> K Loc
store v = findFreeLoc >>= \ l -> writeLoc l v >> return l

hand :: Stack -> Re V -> R (Re V)
hand stk (D v)                         = return (D v)
hand stk (P (Cont,r))                  = stepR (r Ack)
hand stk (P (MkCl n phi, r))     = stepR (r (Val (Cl n (head stk) phi)))
--hand stk (P (MkCl n phi, r))     = stepR ("set up env in heap" >>= \ l ->  r (Val (Cl n (head stk) phi)))
--
-- stores v in the heap at l first, then performs the application
--
hand stk (P (Ap (Cl n rho' phi) v, r)) = seq msg x
     where msg = unsafePerformIO (putStrLn $ "Binding: " ++ n ++ "\n")                                                    
           x   = stepR (gc stk) >>           -- ******
                 stepR (store v) >>= \ l ->  
                 go (xEnv rho' n l : stk) phi >>=
                   stepR . r . Val
hand stk (P (Ap _ v, r))               = stepR (r (Val Wrong))
--
-- first reads heap location l where n is stored, then passes the result on
--
hand (rho:stk) (P (LkUp n,r))          = stepR (read l) >>=       -- ******
                                               stepR . r . Val  
    where l               = lookupEnv n rho
          lookupEnv n rho = case lookup n rho of
                                 (Just v) -> v
                                 Nothing  -> error $ show l ++ " is unbound"

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
doit t =  v 
    where
        v = fst $ deId $ deST (run (go [[]] (interp t))) []

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

------------------------------------
-- Handler and interpreter in MIR --
------------------------------------


mkfun_r :: String -> MIR -> MIR
mkfun_r n phi = MirSignalV (MirMkCl n phi)

appenv_r :: String -> MIR
appenv_r n    = MirSignalV (MirLkUp n)

apply_r :: MIR -> MIR -> MIR
apply_r f v   = MirSignalV (MirAp f v)

-- This is supposed to be a reified version of hand, but it's not even close.
-- To do: fix this.
hand_r (MirMkCl n phi)              = (MirVal (MirCl n MirTopEnvStk phi))
hand_r (MirAp (MirCl n rho' phi) v) = (MirStepR MirGC) `MirRBindNull`
                                     ((MirStepR (MirStore v)) `MirRBind` (MirLam "l"
                                        (MirInExtEnv n (MirVar "l") phi)))
hand_r (MirAp _ v)                  = MirVal MirWrong
hand_r (MirLkUp n)                  = (MirStepR (MirRead l))
                                       where
                                           l   = MirLookup n rho
                                           rho = MirTopEnvStk

handE stk (MirReturnRe e)                          = MirReturnR (MirReturnRe e)

{- What about this? This looks closer to hand. --- Bill.
handE stk (ReD e)                          = RDone (ReD e)
handE stk (ReP ECont r)                    = StepR (EApp r EAck)
handE stk (ReP (EMkCl n phi) r)            = StepR (EApp r (EVal (ECl n (ETop stk) phi)))
handE stk (ReP (EAp (ECl n rho' phi) v) r) =                                     
                 (StepR $ EGC stk) `ERBindNull` 
                 ((StepR (EStore v)) `ERBind` (ELam "l"  
                 (GO (ExEnv rho' n (EVar "l") : stk) phi) `ERBind` (ELam "x"
                   (StepR (EApp r (EVal (EVar "x")))))))
handE stk (ReP (EAp _ v) r)                = StepR (EApp r (EVal EWrong))

handE stk (ReP (ELkUp n) r)          = (StepR (ERead l)) `ERBind` (ELam "v"
                                               (StepR (EApp r (EVal (EVar "v"))))) 
    where l   = ELookup n rho
          rho = ETop stk
-}

-- this is a reified interpreter that creates a MIR representation
-- corresponding to the Re computation produced by interp:
interp_r :: Term -> MIR
interp_r (Var x)   = appenv_r x
interp_r (Con i)   = MirReturnRe (MirNum i)
interp_r (Add u v) = interp_r u `MirReBind` (MirLam "a"
                     (interp_r v `MirReBind` (MirLam "b"
                        (MirAdd (MirVar "a") (MirVar "b")))))
interp_r (Lam x v) = mkfun_r x (interp_r v)
interp_r (App u v) = interp_r u `MirReBind` (MirLam "f"
                     (interp_r v `MirReBind` (MirLam "v"
                        (apply_r (MirVar "f") (MirVar "v")))))
                      
