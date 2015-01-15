monad K = StateT (Int) G

main :: K ()
main = fix (\k -> getGK >>= \ x -> putGK x >> k)
