monad K = StateT(Int) G
monad R = ResT K

noargs :: K Int
noargs = return 6

canweuseit :: Int -> K Int
canweuseit x = noargs >>= \ y -> return (x+y)

bar :: Int -> K ()
bar x = return ()

doof :: K Int
doof = bar 1 >> bar 2 >> bar 3 >> return 86

foo :: K Int
foo = doof >>= \ x -> canweuseit (x+1)

main :: R ()
main = fix(\ k -> \ x -> stepR(canweuseit x) >>= \ newx ->
                         stepR(bar 4) >>
			 stepR doof >>= \ y ->
			 stepR getGK >>= \ z ->
                           k (newx+y+z)) 0
