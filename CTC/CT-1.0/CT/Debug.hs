--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/Debug.hs
--
-- a module containing some simple debugging facilities
--

module CT.Debug where

import System.IO.Unsafe

--           --
-- DEBUGGING --
--           --


--
-- everybody's favorite:
--

dbtrace :: String -> a -> a
dbtrace s x = unsafePerformIO (putStrLn s >> return x)
