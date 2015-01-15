monad K = StateT(Int) G
monad R = ResT K

data Foo = Bar Int Int
         | Baz Int

main :: R ()
main = fix (\ k -> \ state -> k (case state of
                                    (Bar a b) -> Baz b
                                    (Baz a)   -> Bar (a+1) a
                                )) (Bar 0 0)
