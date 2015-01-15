
----------------
-- The monads --
----------------

monad K  = StateT(Heap) Heap
monad R  = ResT K
monad Re = ReactT Q K

signal Q = (Cont,OK)
         | (RdEnv,RspEnv Val)
         | (InEnv Env (Re V),Val V)




---------------------
-- Language syntax --
---------------------

type Name = String
type Loc  = Int
data Term = Var String
          | Con Int
          | Add (Term) (Term)
          | Lam String Term
          | App (Term) (Term)
          | IFZERO (Term) (Term) (Term)

------------
-- Values --
------------

data V = Wrong
       | Num Int
       | Cl String (ReV) Env
       | Environ Env


--add :: Blah
add x y = case (x,y) of
            (Num i,Num j) -> return (Num (i+j))
            (_,_)         -> return Wrong

--gc :: Blah
gc stk = return ()

--signalV :: Blah
signalV = signal q >>= \rsp ->
          case rsp of
            (Val v) -> return v

--rdenvRe :: Blah
rdenvRe = signalV RdEnv

--inenvRe :: Blah
inenvRe rho x = signalV (InEnv rho x)

--prj :: Blah
prj v = case v of
          (Environ r) -> r

--appEnvRe :: Blah
appEnvRe x = rdenvRe >>= \rho -> (step_Re (readHeapK lkup x (prj rho)))

--mkfunRe :: Blah
mkfunRe x e = rdenvRe >>= \ rho -> return (Cl x (interpRe e) (prj rho))

--applyRe :: Blah
applyRe u v = case u of
                 (Cl x phi rho) -> step_Re (storeHeapK v) >>= \ l ->
                                     inenvRe (xEnv rho x l) phi
                 Wrong          -> return Wrong
                 (Num x)        -> return Wrong
                 (Environ rho)  -> return Wrong

--interpRe :: Blah
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

--hand :: Blah
hand stk phi = step_R (isDoneRe phi) >>= \ d ->
               if d
                  then return phi
                  else
                    step_R (getreqRe phi) >>= \ req ->
                    case req of
                       Cont  -> step_R (putrspRe Ack phi)
                       RdEnv -> step_R (putrspRe (Val (Environ (head stk))) phi)
                       (InEnv rho' phi') -> step_R (gc (rho':stk)) >>
                                            go (rho':stk) phi' >>= \ v ->
                                              step_R (putrspRe (Val v) phi)


--go stk phi = step_R (return (Num 42))



t :: Term
t = (App (Lam "x" (Con 42)) (Con 0))

mklet :: String -> Term -> Term -> Term
mklet x v e = App (Lam x e) v

lottalets :: Term
lottalets = mklet "a" (Con 5) (mklet "b" (Con 6) (mklet "c" (Con 7) (mklet "d")(Con 8) (mklet "e" (Con 9) (mklet "f" (Con 10) (Con 0)))))

ex :: Term
ex = Add lottalets (mklet "x" (Con 5) (Var "x"))

fnl :: Term
fnl = Lam "sum" (Lam "n" (IFZERO (Var "n") (Con 0) (Add (Var "n") (App (Var "sum") (Add (Var "n") (Con (-1)))) ) ) )


y :: Term
y = Lam "f" (App (Lam "x" (App (Var "f") (App (Var "x") (Var "x")) )) (Lam "x" (App (Var "f") (App (Var "x") (Var "x")) )))

sum :: Term
sum = App y fnl

e :: Term
e = Lam "x" (App (Var "h") (Lam "a" (App (App (Var "x") (Var "x")) (Var "a"))))



yv :: Term
yv = Lam "h" (App e e)

sumv :: Term
sumv = App yv fnl

sum3 :: Term
sum3 = App sumv (Con 3)

ex1 :: ReV
ex1 = interpRe (Add (Con 1) (Con 2))

ex2 :: ReV
ex2 = interpRe (Lam "x" (Add (Var "x") (Var "x")))

ex3 :: ReV
ex3 = interpRe (App (Lam "x" (Var "x")) (Con 2))

main :: ReV
main = unroll (interpRe sum3)

