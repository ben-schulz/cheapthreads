foo :: Int -> Int
foo x = if True then x+5 else x

foop :: Int -> X Int

flop :: X Int
flop = foop 5 >>= \ j -> return j

doink :: X ()

flep :: X Int
flep = doink >> return 6
