--
-- this is ~/cheapthreads/ctc/tests/HardSep/HardSep.ct.hs
--
-- adaptations of the original hardwired separation spec
-- from pure Haskell into RPS/CT style
--
-- put here 01.09.2009
--
-- Schulz
--

--
-- Monads:
--

monad K = StateT(Int) A + StateT(Int) B

monad R = ResT K

--
-- these are the actions:
--
actionA :: K Int
actionA = (getA >>= \x -> putA(x + 1))

actionB :: K Int
actionB = (getB >>= \y -> putB(y + 1))

--
-- these are the threads:
--
threadA = fix (\k -> step actionA >> k)
threadB = fix (\k -> step actionB >> k)


--
-- this is the shared channel:
--
chan :: R () -> R () -> R ()
chan phi1 phi2 =
  fix (\ k -> \phi1' -> \ phi2' ->
    case phi1' of
      (Pause r1) -> case phi2' of
                      (Pause r2) -> step r1 >>= \ k1 ->
                                    step r2 >>= \ k2 ->
                                      k k1 k2)
  phi1 phi2


--
-- the main:
--
main :: R ()
main = chan threadA threadB
