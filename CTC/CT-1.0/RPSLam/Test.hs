--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Test.hs
--
-- top-level testing calls for the RPS demonstration compiler
--
-- put here (2010.12.14)
--
-- Schulz
--

module Test where

import PPT

import CPS

import PCF.Syntax
import PCF.Parser
import PCF.DefInterp

import Interpreters.Test

import Compile.RSyntax
import Compile.ReSyntax
import Compile.Parser
import Compile.RPSInterp
import Compile.CodeGen
import Compile.HCompile
import Compile.ScopeVars
import Compile.Constants

import Targets.Syntax
import Targets.Interp

import Text.ParserCombinators.Parsec

import System.IO


run_obj :: FilePath -> IO ()
run_obj fp = compile fp >>= \(Prog p) ->
             hcompile "Compile/handler.rps" >>= \(Act h a) ->

             let a' = Act h (codecat mkinit a)
             in
               openFile fp ReadMode >>= \h -> 
               hGetContents h >>= \t ->
               putStrLn "" >>
               putStrLn t >>
               putStr "\n==> " >>
               putStrLn (ppt (interp_obj (Prog (a':p)))) >>
               hClose h >>
               return ()


compile :: FilePath -> IO Prog
compile fp = readFile fp >>= \t ->
             let l = pcfparse t
                 r = rps l
                 p = codegen r
             in
--               putStrLn "PCF term: \n" >>
--               putStrLn (ppt l) >>
--               putStrLn "\nRPS transform: \n" >>
--               putStrLn (ppt r) >>
--               putStrLn "\nObject: \n" >>
--               putStrLn (ppt p) >>

               openFile outfile WriteMode >>= \h ->
               openFile rpsoutfile WriteMode >>= \h' ->
               hPutStr h' (ppt r) >>
               hPutStr h (ppt p) >>
               hClose h >>
               hClose h' >>

               return p



hcompile :: FilePath -> IO Act
hcompile fp = readFile fp >>= \t ->
              let ast = prj_sv (sv_interp (rpsparse t))
                  obj = Act handler (prj_h (hcompile_act ast))
              in
--                putStrLn (ppt ast) >>
--                putStrLn (show ast) >>
--                putStrLn (ppt obj) >>

                openFile houtfile WriteMode >>= \h ->
                hPutStr h (ppt obj) >>
                hClose h >>

                return obj

rpsparse :: String -> CTExpr
rpsparse t = case (runParser ctexpr () "" t) of
               (Right x) -> x
               (Left e)  -> error $ show e

--
-- a handy function for computing CPS transforms,
-- which has become very tiresome to do by hand:
--
cpst :: FilePath -> IO ()
cpst fp = readFile fp >>= \s ->
          let x = rpsparse s 
          in
            putStrLn (ppt (run_m (cps x))) >>
            return ()


rpsoutfile :: FilePath
rpsoutfile = "./a.rps"

outfile :: FilePath
outfile = "./a.out"

houtfile :: FilePath
houtfile = "./h.out"


-- THIS IS THE END OF THE FILE --
