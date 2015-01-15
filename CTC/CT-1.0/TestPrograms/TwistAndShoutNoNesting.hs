--
-- Bill originally put forward this example as something we want
-- to compile that does not yet pass the front-end;
--
-- It is essentially the same as './TwistKernel.hs',
-- the only differences being syntactic.  As such, I'm putting
-- it up as a possibly useful comparison, to check the output
-- of both the front-end and the code generator.
--
-- The example now passes the front-end correctly.
--
-- 2010.02.04 Schulz
--

monad K = StateT (Int) G

monad R = ResT K

--main :: R () -> R () -> R ()
main = (fix (\ tw -> \ phi -> \ gamma ->
--                     case MkPair phi gamma of
--                          (MkPair (Done _) y)   -> y
--                          (MkPair x (Done _))   -> x
--                          (MkPair (Pause x) _)  -> step_R x >>= \ k -> tw gamma k)) (return ()) (return ())
                       case phi of
                         (Done _)  -> gamma
                         (Pause x) -> case gamma of
                                        (Done _) -> phi
                                        _        -> step_R x >>= \ k -> tw gamma k)) (return ()) (return ())


-- where:
--
--step x = Pause (x >>= (return . Done))
--
--fix f = f (fix f)
--
-- or something like it
--
