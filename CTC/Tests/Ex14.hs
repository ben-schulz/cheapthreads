monad K = StateT(Int) Reg
monad R = ResT K

data Term =
     Con Int
   | Sum Term Term
   
interp :: Term -> Int
interp t = case t of
              (Con i)     -> i
              (Sum t1 t2) -> (interp t1) + (interp t2)

t :: Term
t = Sum (Sum (Con 8) (Con 8)) (Sum (Con 1) (Con 2))
              
main :: R ()
main = fix (\k -> \x -> k (interp t)) 0
