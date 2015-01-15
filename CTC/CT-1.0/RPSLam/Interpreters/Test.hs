--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/interpreters/Test.hs
--
-- top level calls for testing the various RPS lambda interpreters;
-- Haskell-like concrete syntax is put through the parser, to bypass the
-- headache of contructing abstract syntax terms by hand
--
-- put here (2010.10.24) Schulz
--

module Interpreters.Test where

import PCF.Parser
import PCF.Syntax

-- interpreters for the RPS demonstration:
import PCF.DefInterp
import Interpreters.InterpId
import Interpreters.InterpE
import Interpreters.InterpR
import Interpreters.InterpRe
import Interpreters.InterpRSI

-- ... and something different:
import Interpreters.InterpErr

import System.IO

--
-- pure interpreter:
--
pcf fp = runfrom interp_pcf fp

--
-- iteration 0: identity monad
--
run_id fp = runfrom interp_id fp

--
-- iteration 1: environment monad
--
run_e fp = runfrom interp_e fp

--
-- iteration 2: lifted environment monad
--
run_r fp = runfrom interp_r fp

--
-- iteration 3: factoring into reactive term, resumptive handler
--
run_re fp = runfrom interp_re fp


--
-- something different: factoring into reactive term and resumptive 
-- handler with supervisory value checking:
--
run_err fp = runfrom interp_err fp

--
-- test all the interpreters, and check for consistency:
--
run_all fp = readFile fp >>= \t ->

  let p = run interp_pcf t
      i = run interp_id t
      e = run interp_e t
      r = run interp_r t
      k = run interp_re t
      x = run interp_err t
  in
    putStrLn ("PCF : " ++ (show p)) >>
    putStrLn ("Id  : " ++ (show i)) >>
    putStrLn ("E   : " ++ (show e)) >>
    putStrLn ("R   : " ++ (show r)) >>
    putStrLn ("Re  : " ++ (show k)) >>
    putStrLn ("Err : " ++ (show x)) >>
    putStrLn ""

--
-- run with a given input string:
--
run :: (Term -> a) -> String -> a
run int lam = int (pcfparse lam)


--
-- read the initial input string from a file:
--
runfrom :: (Term -> a) -> FilePath -> IO a
runfrom int fp = readFile fp >>= \t ->
                 putStrLn t >>
                 putStrLn (show $ pcfparse t) >>
                 putStrLn "--->\n" >>
                 return (run int t) 


-- THIS IS THE END OF THE FILE --
