data D = A Int | B Bool

foo :: D -> Int
foo d = case d of
           (A x) -> x
           (B x) -> if x then 1 else 2

fee :: D -> D
fee d = case d of
           (A x) -> B False
           (B x) -> B x
           
faa :: D -> (Int,Bool)
faa d = case d of
           (A x) -> (x,False)
           (B x) -> (0,x)
