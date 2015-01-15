--
-- this is ~/cheapthreads/ctc_working/CT-1.0/TestPrograms/Test1.hs
--
-- the CT parser's first syntactically complete test program
--
-- put here 2010.01.07
--
-- Schulz
--

type Rsp = Int

data Rsp = OK | WriteOut Int

monad K = StateT(Int) G + StateT(Int) H
monad Re = ReactT Req Rsp K

main :: Int -> (Re ())
main z =
  step_R (

    get G >>= \x ->
    put G (x + 1) >>= \y ->
    return (x * y + 1)

  ) >>

  fix(\k ->
    step_R(phi) >>= \x ->
    if (not x) then return (fst ((), ((), ())))
    else k
  ) >>

  return ()

foo :: Int
foo = 0

q = f x y z

x = 3

y = 42

x = 3 + 3

y = 42

x = if ninetythree then ninetyfour else ninetyfive

yagrad :: Tape
yagrad = x + y + y + y + z

dromedary = -x - y
