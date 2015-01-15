data V = Boeuf Int

{-
bloggle :: Int
bloggle = head (1:(1:(1:([]::[Int]))))

main :: Re V
main = return (Boeuf bloggle)
-}

main :: Re V
main = return (Boeuf 1)
