--
-- this is a (slightly awkward) tweeking of the DSLWC
-- example into something equivalent that will pass
-- the front-end in its current state;
--
-- everything eccentric in the code may be assumed to
-- be a consequence of some idiosyncracy of the front-end
--
-- (2010.01.28) Schulz
--

monad K = StateT(Int) G
monad R = ResT K

actionA :: (K ())
actionA = get G >>= \ g -> put G (g+1)

actionB :: (K ())
actionB = get G >>= \ g -> put G (g-1)


main :: (R ())
main =  
       ((fix (\k -> \x ->
            step (put G (fst x) >> actionA >> get G) >>= \ newa ->
            step (put G (snd x) >> actionB >> get G) >>= \ newb ->
              k (newa, newb) >>= \y -> 
              return (y + 0)
             )) (0,0)) >> return ()
