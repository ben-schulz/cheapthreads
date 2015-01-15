--
-- Don't even ask what this is about. :)
--

data D =
    A Bool Bool
  | B Int
    
data E =
    C D D

mkD :: Bool -> D
mkD x = A x x

mkD' :: Bool -> D
mkD' x = B (if x then 1 else 0)

loop :: E -> Bool -> R ()
loop x y = fix(\k -> \d -> \b -> k (C (mkD b) (mkD' b)) (if b then False else True)) x y

main :: R ()
main = loop (C (A True False) (A False True)) True
