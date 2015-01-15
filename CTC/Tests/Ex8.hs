monad K = StateT(Int) G
monad R = ResT K

fst :: (Int,Bool) -> Int
fst x = case x of
           (a,b) -> a

snd :: (Int,Bool) -> Bool
snd x = case x of
           (a,b) -> b
           
main :: R ()
main = return (fst (1,False)) >>= \ x -> stepR (putGK x)
