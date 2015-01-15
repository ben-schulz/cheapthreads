module RPSLam.GC where

import Prelude hiding (read)
import CT.MonadicConstructions hiding (inEnv,rdEnv)
import RPSLam.EssenceSyn
import Data.List

u = upd

g = get

------------
-- Values --
------------

data V = Wrong
       | Error String
       | Num Int
--       | Cl Name Term Env -- proper closures
       | Cl Name (Re V) Env -- proper closures
       | Environ Env

add (Num i) (Num j) = return (Num (i+j))
add x y             = error $ show x ++ "," ++ show y
--add _ _             = return (Error "add")

instance Show V where
    show Wrong      = "Wrong"
    show (Error m)  = "Error: " ++ m
    show (Num i)    = show i
    show (Cl x _ e) = '(':x ++ ',':("<code>") ++ ',':(show e) ++ ")"
    show (Environ r) = show r

--------------------------
-- Requests & Responses --
--------------------------

data Req = Cont              -- Continue
         | RdEnv             -- rdEnv signal
         | InEnv Env (Re V)  -- inEnv signal
         | Store V           -- store signal

data Rsp = Ack               -- Acknowledge
         | Val V             -- Return value
--         | RspEnv Env      -- Return environment
         | RspLoc Loc        -- Return location

------------------
-- Environments --
------------------

type Env = [(Name,Loc)]          

xEnv :: Env -> Name -> Loc -> Env
xEnv rho n l = (n,l):rho

lkup x ((y,b):bs) = if x==y then b else lkup x bs

----------------
-- The monads --
----------------

type Sto   = [(Loc,V)]
type K  = StateT Sto IO
type R  = ResT K
type Re = ReactT Req Rsp K

etaK :: a -> K a
etaK = return

etaR :: a -> R a
etaR = Done

etaRe :: a -> Re a
etaRe = D

---------------------
--  Heap Routines  --
---------------------

writeLoc :: Loc -> V -> K ()
writeLoc l val = u (\s -> (l,val):(rest s))
   where rest s = filter (\ (loc,v) -> loc/= l) s

read :: Loc -> K V
read l = g >>= \s -> etaK (lookupSto l s)
    where lookupSto l s = case lookup l s of
                               Nothing -> error $ "can't read loc " ++ show l
--                                          Nothing  -> (Error "read")
                               (Just x) -> x

-- instrumented version
findFreeLoc :: K Loc
findFreeLoc = do
                 s          <- g
                 let newloc =  ffl 0 s
                 liftSt $ putStrLn $ "Allocating: " ++ show newloc
                 return newloc
{-
                  where ffl :: Loc -> Sto -> Loc
                        ffl n sto = case lookup n sto of
                                        Nothing -> n
                                        _       -> ffl (n+1) sto
-}
                  where ffl :: Loc -> Sto -> Loc
                        ffl n sto = case lookup n sto of
                                      Nothing           -> n

                                      (Just (Environ [])) -> ffl (n + 1) sto
                                      (Just (Environ e))  -> let ls = map snd e
                                                                 n' = head $ sort ls
                                                             in
                                                               ffl (n' + n + 2) sto

                                      (Just (Cl _ _ [])) -> ffl (n + 1) sto
                                      (Just (Cl _ _ e))  -> let ls = map snd e
                                                                n' = head $ sort ls
                                                            in
                                                              ffl (n' + n + 1) sto

                                      _                 -> ffl (n+1) sto


storeK :: V -> K Loc
storeK v = findFreeLoc >>= \ l -> writeLoc l v >> return l

------------------------
-- Garbage collection --
------------------------

type Stack = [Env]        -- *****


findLiveLocs :: Stack -> Sto -> [Loc]
findLiveLocs sta sto = let ls = concatMap (map snd) sta
                           cl = \v -> case v of
                                        (Environ e) -> (map snd) e
                                        (Cl _ _ e)  -> (map snd) e
                                        _           -> []
                       in
                         ls ++ (foldr (\(_, v) -> \ls' -> (cl v) ++ ls') [] sto)
                   


freeDeadLocs :: [Loc] -> Sto -> K Sto
freeDeadLocs ls sto = do
                         let deadlocs = map fst $ filter (\(l,v) -> not (l `elem` ls)) sto
--                             deadlocs' = filter (\(l,v) -> not (elem l ls)) sto
                             livelocs = filter (\(l,v) -> l `elem` ls) sto
--                         liftSt $ putStrLn $ "Freeing: " ++ (show deadlocs')
--                         liftSt $ putStrLn $ "Live: " ++ (show livelocs)
                         return livelocs

gcThreshold :: Int
gcThreshold = 2

gcHelper :: Stack -> Sto -> K Sto
gcHelper stk sto = if length sto > gcThreshold 
                   then
                         freeDeadLocs (findLiveLocs stk sto) sto
                   else
                         return sto

gc :: Stack -> K ()
gc stk = g >>= \ sto ->
         gcHelper stk sto >>= \ sto' ->
            u (const sto')

---------------------------------
---  Extra Monadic Structure  ---
---------------------------------

signalV :: Req -> Re V
signalV q = P (q, \ (Val v) -> return $ etaRe $ v)

{-
signalE :: Req -> Re Env
signalE q = P (q, \ (RspEnv rho) -> return (etaRe rho))
-}

signalL :: Req -> Re Loc
signalL q = P (q, \ (RspLoc loc) -> return (etaRe loc))

signal :: Req -> Re Rsp
signal q = P (q, return . etaRe)

stepR :: K a -> R a
stepR phi = Pause (phi >>= (return . etaR))

stepRe :: K a -> Re a
stepRe phi = P (Cont,\ Ack -> phi >>= (return . etaRe))

runR :: R a -> K a
runR (Done v)    = return v
runR (Pause phi) = phi >>= runR

---------------------------------------------------
-- Below is the resumption-passing style version --
---------------------------------------------------

rdenvRe :: Re V
rdenvRe       = signalV RdEnv

inenvRe :: Env -> Re V -> Re V
inenvRe rho x = signalV (InEnv rho x)

storeRe :: V -> Re Loc
storeRe x = signalL (Store x)

-- Necessary bookkeeping
prj :: V -> Env
prj (Environ r) = r

appEnvRe :: Name -> Re V
appEnvRe x = signal RdEnv >>= stepRe . read . lkup x . proj
    where proj (Val (Environ r)) = r

mkfunRe :: Name -> Re V -> Re V
mkfunRe x e = signal RdEnv >>= etaRe . (Cl x e) . proj
    where proj (Val (Environ r)) = r

applyRe :: V -> V -> Re V
applyRe (Cl x phi rho) v = storeRe v >>= \ l -> -- *****
                           inenvRe (xEnv rho x l) phi
--                            inenvRe (xEnv rho x l) (interpRe e)
applyRe x y             = error $ "apply: " ++ show x ++ "," ++ show y

interpRe :: Term -> Re V
interpRe (Var x)   = appEnvRe x
interpRe (Con i)   = return (Num i)
interpRe (Add u v) = interpRe u >>= \ a ->
                     interpRe v >>= \ b ->
                        add a b
interpRe (Lam x e) = mkfunRe x (interpRe e)
interpRe (App t u) = interpRe t >>= \ f ->
                     interpRe u >>= \ a ->
                        applyRe f a
interpRe (IFZERO t1 t2 t3) = interpRe t1 >>= \ v ->
                                case v of
                                     (Num 0) -> interpRe t2
                                     (Num _) -> interpRe t3
     --                              _       -> return (Error "IFZERO")

-----------------
-- The handler --
-----------------

loop :: (Re V -> R (Re V)) -> Re V -> R V
loop f (D v) = Done v
loop f phi   = (f phi) >>= loop f

hand :: Stack -> Re V -> R (Re V) -- ****** hand takes Stack instead of Env
hand stk (D v)                  = return (D v)
hand stk (P (Cont,r))           = stepR (r Ack)
hand (rho:stk) (P (RdEnv,r))    = stepR (r (Val (Environ rho)))
hand stk (P (InEnv rho' phi,r)) = go (rho':stk) phi >>= stepR . r . Val
hand stk (P (Store v,r))        = stepR (gc stk >> storeK v >>= \ l -> r (RspLoc l))


go :: Stack -> Re V -> R V
go stk = loop $ hand stk

goRe :: Term -> IO ()
goRe t = deST (runR (go [[]] (interpRe t))) [] >>= \ (v,_) ->
         putStrLn (show v) >>
            putStrLn "----"

extreme = mapM_ goRe unittests             
unittests = [lottalets,ex,ex1,ex2,ex3,ex4]             

t1 = App rator rand
    where rator = Lam "x" (Add (Var "x") (Con 1))
          rand  = Con 99
