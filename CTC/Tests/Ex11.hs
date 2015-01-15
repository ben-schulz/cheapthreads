f :: Int -> Int
f x = (g x) + 1 - y

g :: Int -> Int
g x = (f x) - 1 + x + y + z + case j of
                                 (Crock q) -> q
                                 (Crick z) -> q
                                 (Creck h) -> g h

x :: Int
x = x

p :: Int -> Int
p x = g x

data Foo = Bar | Baz
