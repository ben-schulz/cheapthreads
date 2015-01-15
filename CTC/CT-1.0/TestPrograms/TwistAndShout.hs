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

data Plurkk = Drack Int | Drock Int Int

monad K = StateT (Int) G

monad R = ResT K

main :: R Int
main = (fix (\ tw -> \ phi -> \ gamma ->
                     case (phi,gamma) of
                          (Done _,y)  -> y
                          (x,Done _)  -> x
                          (Pause x,_) -> step_R x >>= \ k -> tw gamma k)) (return 1066) (return 1776)
--main = (fix(\ m -> \ phi -> case phi of
--                             (Done y)  -> return y
--                             (Pause x) -> step_R x >>= \ k -> m k)) (return 9)

-- where:
--
--step x = Pause (x >>= (return . Done))
--
--fix f = f (fix f)
--
-- or something like it
--
