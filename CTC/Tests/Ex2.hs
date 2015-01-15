data D = D Int | G Int Int

data F = F D D

foop :: Int -> F
foop x = F (G x x) (D 1)

feep :: Int -> D
feep x = G x x

doof :: D -> F
doof d = F d d
