data Blotz =
     Jump Int Int
   | Taz Int Int

f :: Int -> Int
f x = x+1

g :: Int -> Blotz
g x = Taz x 47

main :: Re Int
main = case (g 82) of
          (Jump x y) -> return 8
          (Taz x y)  -> return (f (x+y))
