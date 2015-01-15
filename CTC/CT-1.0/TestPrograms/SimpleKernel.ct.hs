--
-- this is ~/cheapthreads/ctc_working/CT-1.0/TestPrograms/SimpleKernel.ct.hs
--
-- a simple round-robin scheduler written in CT
--
-- put here 2010.01.29
--
-- Schulz
--

monad K = StateT (Int) G

monad R = ResT K


main :: K Int -> K Int -> R ()
main x y =

    (
      fix
      (\k -> \a -> \b ->

        step_R a >>
        step_R b >>
        k a b

      )

    ) x y

-- END
