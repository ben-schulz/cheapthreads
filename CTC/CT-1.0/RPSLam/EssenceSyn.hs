module RPSLam.EssenceSyn where

---------------------
-- Language syntax --
---------------------

type Name = String
type Loc  = Int
data Term = Var Name
          | Con Int
          | Add Term Term
          | Lam Name Term
          | App Term Term
          | LetRef Name Term Term
          | Deref Term
          | PutRef Term Term
          | Seq Term Term
          | IFZERO Term Term Term
          deriving Show

--------------------
-- A few examples --
--------------------
-- Y = \ f -> (\ x -> f (x x)) (\ x -> f (x x)) 


--
-- fnl = \sum -> \n -> IFZERO n 0 (n + (sum (n - 1)))
-- sum = y fnl
--
--sum = App y fnl
sum = App (App fnl (Lam "x" (Var "x"))) (Con 9)
  where fnl = Lam "sum" (Lam "n" (IFZERO (Var "n") 
                                         (Con 0) 
                                        (Add (Var "n") 
                                             (App (Var "sum") 
                                                  (Add (Var "n") (Con (-1))))
                                        )))

--
-- \f -> (\x -> f (x x)) (\x -> f (x x))
--
y = Lam "f" (App
                 (Lam "x" (App (Var "f") (App (Var "x") (Var "x")) )) 
                 (Lam "x" (App (Var "f") (App (Var "x") (Var "x")) )) 
             )

--
-- e = \x -> (h (\a -> ((x x) x) a))
--
-- \h -> (e e)
--
yv = Lam "h" $
       App e e
  where
      e = Lam "x" (App (Var "h") 
                       (Lam "a" (App (App (Var "x") (Var "x")) (Var "a"))))

--
-- fnl = \sum -> \n -> IFZERO n 0 (n + (sum (n - 1)))
--
-- (yv fnl)
--
-- (\x -> (fnl (\a -> ((x x) a)))) (\x -> (fnl (\a -> ((x x) a))))
--
--
sumv = App yv fnl 
  where fnl = Lam "sum" (Lam "n" (IFZERO (Var "n") 
                                         (Con 0) 
                                        (Add (Var "n") 
                                             (App (Var "sum") 
                                                  (Add (Var "n") (Con (-1))))
                                        )))


sum3 = App sumv (Con 3)
             
{-
   let lottalets = (let a=5, b=6, c=7, d=8, e=9, f=10 in 0)
    in lottalets + (let x=5 in x)
-}
mklet x v e = App (Lam x e) v
lottalets = mklet "a" (Con 5) $ mklet "b" (Con 6) $ mklet "c" (Con 7) $ mklet "d" (Con 8) $ mklet "e" (Con 9) $ mklet "f" (Con 10) (Con 0)
ex = Add lottalets (mklet "x" (Con 5) (Var "x"))

ex1 = App plus arg
  where plus = Lam "x" (Add (Var "x") (Var "x"))
        arg  = (Add (Con 99) (Con 8))
ex2 = (Add (Con 99) (Con 8))
ex3 = Lam "x" (Add (Var "x") (Var "x"))
ex4 = Var "x"

letexp x e e' = App (Lam x e') e

paper1 = Add e (Add e (Add e (Add e (Add e (Add e (Con 0))))))
    where e = letexp "x" (Con 100) (Var "x") -- (Add (Var "x") (Var "x"))

paper2 = Add e (Add e (Con 0))
    where e = sum3

{- (\x -> letref r := x
              in r := !r + !r;
                 r) 21 -}
ex5 = (App (Lam "x" (LetRef "r" (Var "x") (Seq (PutRef (Var "r") (Add (Deref (Var "r")) (Deref (Var "r")))) (Var "r")))) (Con 21))
ex6 = (Deref ex5)

{- for i = 1 to 10 ( letref r := i in r ) -}
ex7 = foldr1 Seq [c n|n <- [1..10]]
      where c n = LetRef "r" (Con n) (Var "r")

{- Do the above inside the scope of a letref; the cell containing 42 should
   not be GC'ed -}
ex8 = (LetRef "r" (Con 42) ex7)

{- (letref r := 69 in 0) ; ex8

   The 69 should be freed when GC happens (because it is out of scope) but
   the 42 should stay. -}
ex9 = Seq (LetRef "r" (Con 69) (Con 0)) ex8

{- letref r := 0
       in letref r' := r
              in (r := r' ; ex7)

   Forces GC on circular references -- currently this diverges because the
   "mark" phase does not keep track of where it's already been.
-}
ex10 = LetRef "r" (Con 0) (LetRef "r'" (Var "r") (Seq (PutRef (Var "r") (Var "r'")) ex7))

