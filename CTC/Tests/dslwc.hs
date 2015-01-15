monad K = StateT(Int) G
monad R = ResT K

actionA :: K ()
actionA = getGK >>= \ g -> putGK (g+1)

actionB :: K ()
actionB = getGK >>= \ g -> putGK (g-1)

main :: R ()
main = 
       ((fix (\k -> \a -> \b ->
            stepR (putGK a >> actionA >> getGK) >>= \ newa ->
            stepR (putGK b >> actionB >> getGK) >>= \ newb ->
              k newa newb)) 0 0)
