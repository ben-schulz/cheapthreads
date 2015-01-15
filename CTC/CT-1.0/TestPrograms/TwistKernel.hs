
monad K = StateT(Int) G

monad R = ResT K

main :: (R ()) -> (R ()) -> (R ())
main phi psi =

    (loop_R
    (\t -> 

      if (isDone (fst t))
      then
        -- 'x' done, run remainder of y and stop
        snd t >> break (return (), return ())
      else 
        (nextOf (fst t)) >>= \r -> 
        return (snd t, r)

    )) (phi, psi) >>

    return ()

isDone x =
  case x of
    (Done _)  -> True
    (Pause _) -> False

nextOf :: (R ()) -> (R (R ()))
nextOf r =
  case r of
    (Pause x) -> step_R x
    (Done a)  -> step_R (return a)

