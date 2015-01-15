--
-- This is taken from GarbageCollection/GPCE09-code/GC.hs, and hacked up for
-- Cheap Threads.
--
-- We should re-synchronize it with the original before publication.
--

----------------
-- The monads --
----------------

monad K  = StateT(Heap) Heap
monad R  = ResT K
monad Re = ReactT Req Rsp K

---------------------
-- Language syntax --
---------------------

type Name = String
type Loc  = Int
data Term = Var String
          | Con Int
          | Add Term Term
          | Lam String Term
          | App Term Term
          | IFZERO Term Term Term
          deriving Show

------------
-- Values --
------------

data V = Wrong
       | Num Int
       | Cl String (Re V) Env
       | Environ Env

add :: V -> V -> Re V
add x y = case x of
             (Num i) -> case y of
                           (Num j)       -> return (Num (i+j))
                           Wrong         -> return Wrong
                           (Cl n phi e)  -> return Wrong
                           (Environ e)   -> return Wrong
             Wrong         -> return Wrong
             (Cl n phi e)  -> return Wrong
             (Environ e)   -> return Wrong

--------------------------
-- Requests & Responses --
--------------------------

data Req = Cont              -- Continue
         | RdEnv             -- rdEnv signal
         | InEnv Env (Re V)  -- inEnv signal

data Rsp = Ack               -- Acknowledge
         | Val V             -- Return value
--         | RspEnv Env        -- Return environment

------------------------
-- Garbage collection --
------------------------

-- This is gonna need some tweaking anyway, so it's a no-op for now
gc :: [Env] -> K ()
gc stk = return ()

---------------------------------------------------
-- Below is the resumption-passing style version --
---------------------------------------------------

signalV :: Req -> Re V
signalV q = signalRe q >>= \ rsp ->
            case rsp of
               (Val v) -> return v

rdenvRe :: Re V
rdenvRe       = signalV RdEnv

inenvRe :: Env -> Re V -> Re V
inenvRe rho x = signalV (InEnv rho x)

-- Necessary bookkeeping
prj :: V -> Env
prj v = case v of
           (Environ r) -> r

appEnvRe :: String -> Re V
appEnvRe x = rdenvRe >>= \ rho -> (stepRe (readHeapK (lkup x (prj rho))))

mkfunRe :: String -> Term -> Re V
mkfunRe x e = rdenvRe >>= \ rho -> return (Cl x (interpRe e) (prj rho))

applyRe :: V -> V -> Re V
applyRe u v = case u of
                 (Cl x phi rho) -> stepRe (storeHeapK v) >>= \ l ->
                                     inenvRe (xEnv rho x l) phi
                 Wrong          -> return Wrong
                 (Num x)        -> return Wrong
                 (Environ rho)  -> return Wrong
                 
interpRe :: Term -> Re V
interpRe t = case t of
                (Var x)   -> appEnvRe x
                (Con i)   -> return (Num i)
                (Add u v) -> interpRe u >>= \ a ->
                             interpRe v >>= \ b ->
                                add a b
                (Lam x e) -> mkfunRe x e
                (App t u) -> interpRe t >>= \ f ->
                             interpRe u >>= \ a ->
                                applyRe f a
                (IFZERO t1 t2 t3) -> interpRe t1 >>= \ v ->
                                       case v of
                                          (Num n)      -> if n == 0 then interpRe t2 else interpRe t3
                                          Wrong        -> return Wrong
                                          (Cl n phi e) -> return Wrong
                                          (Environ e)  -> return Wrong

-----------------
-- The handler --
-----------------

{-
--
-- Should probably make this a built-in???
--
loop :: (Re V -> R (Re V)) -> Re V -> R V
loop f (D v) = Done v
loop f phi   = (f phi) >>= loop f
-}

hand :: [Env] -> Re V -> R (Re V) -- ****** hand takes Stack instead of Env
hand stk phi = stepR (isDoneRe phi) >>= \ d ->
               if d
                  then return phi
                  else
                    stepR (getreqRe phi) >>= \ req ->
                    case req of
                       Cont  -> stepR (putrspRe Ack phi)
                       RdEnv -> stepR (putrspRe (Val (Environ (head stk))) phi)
                       (InEnv rho' phi') -> stepR (gc (rho':stk)) >>
                                            go (rho':stk) phi' >>= \ v ->
                                              stepR (putrspRe (Val v) phi)

go :: [Env] -> Re V -> R V
--go stk phi = loop (hand stk) phi
go stk phi = stepR (return (Num 42))

t :: Term
t = (App (Lam "x" (Con 42)) (Con 0))

mklet :: String -> Term -> Term -> Term
mklet x v e = App (Lam x e) v

lottalets :: Term
lottalets = mklet "a" (Con 5) (mklet "b" (Con 6) (mklet "c" (Con 7) (mklet "d" (Con 8) (mklet "e" (Con 9) (mklet "f" (Con 10) (Con 0))))))

ex :: Term
ex = Add lottalets (mklet "x" (Con 5) (Var "x"))

fnl :: Term
fnl = Lam "sum" (Lam "n" (IFZERO (Var "n") 
                                 (Con 0) 
                                 (Add (Var "n") 
                                      (App (Var "sum") 
                                        (Add (Var "n") (Con (-1))))
                                 )
                          )
                )


y :: Term
y = Lam "f" (App
                 (Lam "x" (App (Var "f") (App (Var "x") (Var "x")) )) 
                 (Lam "x" (App (Var "f") (App (Var "x") (Var "x")) )) 
             )

sum :: Term
sum = App y fnl

e :: Term
e = Lam "x" (App (Var "h") 
                 (Lam "a" (App (App (Var "x") (Var "x")) (Var "a"))))


yv :: Term
yv = Lam "h" (App e e)

sumv :: Term
sumv = App yv fnl 

sum3 :: Term
sum3 = App sumv (Con 3)

ex1 :: Re V
ex1 = interpRe (Add (Con 1) (Con 2))

ex2 :: Re V
ex2 = interpRe (Lam "x" (Add (Var "x") (Var "x")))

ex3 :: Re V
ex3 = interpRe (App (Lam "x" (Var "x")) (Con 2))

--main :: Re V
--main = interpRe sum3


