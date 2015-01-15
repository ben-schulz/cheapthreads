--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Compile/Constants.hs
--
-- a collection of the name/label/other conventional constants used
-- in the RPS demonstration compiler
--
-- put here (2011.01.05)
--
-- Schulz
--

module Compile.Constants where


--                 --
-- STANDARD LABELS -- 
--                 --


--
-- program entry point:
--
mainl :: String
mainl = "__MAIN"

initl :: String
initl = "__INIT"


--
-- handler entry point:
--
handler :: String
handler = "__HANDLER"



--
-- fresh label prefix used in the term code:
--
tlocal :: String
tlocal = "LOCAL"


--
-- fresh label prefix used in the handler code:
--
hlocal :: String
hlocal = "HANDL"




--                   --
-- STRUCTFIELD NAMES -- 
--                   --


--
-- field used for storing the constructor component of all constructed values 
--
confld :: String
confld = "con"

--
-- field used for pattern matching pause or done in resumption-typed values
--
donefld :: String
donefld = "isdone"


--
-- field used for matching current request in reactive resumption-typed values:
--
reqfld :: String
reqfld = "req"


--
-- field used for matching current PC value in resumption-typed values:
--
callfld :: String
callfld = "callback"


--
-- return value from a given resumption:
--
valfld :: String
valfld = "val"


--
-- a generic structure field prefix for constructing values
--
structfld :: String
structfld = "__field"


--
-- a simple function for forming generic structure fields
--
attachl :: String -> [a] -> [(String, a)]
attachl s xs = zip (map (\x -> s ++ (show x)) ints) xs

ints :: [Int]
ints = iterate (+ 1) 0




--              --
-- OTHER VALUES --
--              --

--
-- environment is initially empty
--
initenv :: [a]
initenv = []


--
-- signal constructors:
--
qmkcl :: String
qmkcl = "MkCl"

qmkreccl :: String
qmkreccl = "MkRecCl"

qapply :: String
qapply = "Apply"

qlkp :: String
qlkp = "Lkp"



-- THIS IS THE END OF THE FILE --
