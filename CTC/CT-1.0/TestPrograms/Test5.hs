--
-- as of 2010.01.27, the CT front-end accepts this program:
--
-- Schulz
--

monad K = StateT(Int) G
monad R = ResT K

main :: (R ())
main = step_R(get G >>= \x -> put G (foo x)) >> return ()


foo :: Int -> Int
foo = \x -> x + 1

bar = \x -> \y -> \xs -> (y:x:[])

