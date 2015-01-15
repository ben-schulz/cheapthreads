--
-- this is ~/cheapthreads/CTC/CT-1.0/Test.hs
--
-- main testing functions for cleaned-up CT
--
-- put here 2009.12.30
--
-- Schulz
--

module Test where

import System.IO
import Text.ParserCombinators.Parsec

-- the CT front-end:
import CT.Syntax
import CT.Factored
import CT.Parser
import CT.OpTable
import CT.TypeChecker
import CT.PrimitiveTySigs
import CT.ANAST
import CT.INAST
import CT.Inliner
import CT.Uncase
import CT.ScopeVars
--import CT.Unroll

-- first intermediate phase, CT -> RSI:
import RSI.Syntax
import RSI.Compile

-- branches from first intermediate phase:
import RSI.Imr.Compile


-- second intermediate phase, RSI -> SAL:
import RSI.SAL.Syntax
import RSI.SAL.Compile
import RSI.SAL.RAllocate
import RSI.SAL.FlowAnalysis


-- target-specific back-ends:
import Targets.ObjGen
import Targets.Microblaze.InsSet
import Targets.Microblaze.Selector


-- the defunctionalizer:
import CT.DFun.DFun
import CT.DFun.DFunOpt
import CT.DFun.WriteFSM

-- OESS intermediate phase modules:
import Deprecated.OESS.Syntax
import Deprecated.OESS.Compile

-- old code generation facilities:
--import Deprecated.Compiler.Codegen
--import Deprecated.Compiler.Interp
--import Deprecated.ETIC.Print
--import Deprecated.ETIC.GenC

-- from the APLAS'10 paper:
import RPSLam.GC_Reify
import RPSLam.ULamParser

-- typeclass for formatted output:
import CT.PPT


--import Control.Monad.Identity



--
-- top-level call to the compiler:
--
-- first argument is an option flag
--
ctc :: String -> FilePath -> IO Obj
ctc opt fp =
  openFile fp ReadMode >>= \h ->
  hGetContents h >>= \s ->
  preprocess s >>= \s' ->

  (
    case (runParser ctprog () fp s') of

      (Left _) -> error $ "parse error in " ++ fp

      -- if success, run it through the type-checker:
      (Right p) -> return $ cttc p

  ) >>= \as ->

  (
    case as of

      (Left _)  -> error $ "type error in " ++ fp

      (Right a) -> let toin   = \((x, y), (z, w)) ->
                                  (INFunDec ((x, y), (z, toinast w)))

                       unwrap = \(INFunDec x) -> x
                   in
                     case opt of

                     -- flagged for inline:
--                     "-i" -> let ast = inline $ scopevars $ toinprog a
                     "-i" -> let ast = inline $ scopevars $ noinline $ toinprog a
                                 s   = '\n':(ppt ast) ++ "\n"
                             in
                               putStrLn s >>
                               return ast

                     -- test case for the pattern unnester:
                     "-u" -> let ast = uncase $ scopevars $ noinline $ toinprog a
                                 s   = '\n':(ppt ast) ++ "\n"
                             in
                               putStrLn s >>
                               return ast

                     -- test case for the pattern unnester, scopevars bypassed (Adam):
                     "-us" -> let ast = uncase $ noinline $ toinprog a
                                  s   = '\n':(ppt ast) ++ "\n"
                              in
                                putStrLn s >>
                                return ast

                     -- ditto; the `t' means that the type checker is bypassed (that
                     -- aspect is handled above)  --Adam
                     "-ust" -> let ast = uncase $ noinline $ toinprog a
                                   s   = '\n':(ppt ast) ++ "\n"
                               in
                                 putStrLn s >>
                                 return ast

                     -- default pass:
                     _    -> let ast = scopevars $ noinline $ toinprog a
                                 s   = '\n':(ppt ast) ++ "\n"
                             in
                               putStrLn s >>
                               return ast

  ) >>= \ast ->

  -- currently use the 'Imr' path by default;
  -- I don't want to have to throw an option every time I call this;
  -- 
  -- (2010.11.02) Schulz
  let rsi = rsi_gen ast
      imr = imr_pass rsi
      sal = (gen_flow . gen_sal) imr
      obj = ((objgen default_arch) . (ralloc default_target)) sal
      out = ppt obj
  in

    -- dump all intermediate representations, for debugging:
    putStrLn (show ast) >>
    putStrLn "\n\n\n\n" >>
    putStrLn (show rsi) >>
    putStrLn "\n\n\n\n" >>
    putStrLn (show imr) >>
    putStrLn "\n\n\n\n" >>
    putStrLn  (ppt sal) >>
    putStrLn "\n\n\n\n" >>
    putStrLn (ppt (ralloc default_target sal)) >>
    putStrLn "\n\n\n\n" >>
    putStrLn (ppt obj) >>
    putStrLn "\n\n\n\n" >>

    -- dump the final object code to screen,
    putStrLn out >>
    putStrLn "\n\n" >>

    -- and to the output file:
    openFile ctc_out WriteMode >>= \h' ->
    hPutStr h' ("-- BEGIN COMPILER OUTPUT --\n\n"
                ++ out
                ++ "\n\n-- END OF COMPILER OUTPUT --") >>

    hClose h' >>
    hClose h >>

    putStrLn ("\noutput written to " ++ ctc_out ++ "\n\n") >>

    return obj

--
-- default compiler output file:
--
ctc_out :: FilePath
ctc_out = "./out.s"

--
-- default output file for the RSI intermediate:
--
rsi_out :: FilePath
rsi_out = "./rsi.out"


--
-- run the CT front-end (parser, typechecker, inliner)
-- (for debugging purposes):
--
ctfe :: String -> FilePath -> IO INProg
ctfe opt fp =
  openFile fp ReadMode >>= \h ->
  hGetContents h >>= \s ->
  preprocess s >>= \s' ->

  (
    case (runParser ctprog () fp s') of

      (Left _) -> error $ "parse error in " ++ fp

      -- if success, run it through the type-checker:
      (Right p) -> return $ cttc p

  ) >>= \as ->

  (
    case as of

      (Left _)  -> error $ "type error in " ++ fp

      (Right a) -> let toin   = \((x, y), (z, w)) ->
                                  (INFunDec ((x, y), (z, toinast w)))

                       unwrap = \(INFunDec x) -> x
                   in
                     case opt of

                     -- flagged for inline:
--                     "-i" -> let ast = inline $ scopevars $ toinprog a
                     "-i" -> let ast = inline $ scopevars $ noinline $ toinprog a
                                 s   = '\n':(ppt ast) ++ "\n"
                             in
                               putStrLn s >>
                               return ast

                     -- test case for the pattern unnester:
                     "-u" -> let ast = uncase $ scopevars $ noinline $ toinprog a
                                 s   = '\n':(ppt ast) ++ "\n"
                             in
                               putStrLn s >>
                               return ast

                     -- test case for the pattern unnester, scopevars bypassed (Adam):
                     "-us" -> let ast = uncase $ noinline $ toinprog a
                                  s   = '\n':(ppt ast) ++ "\n"
                              in
                                putStrLn s >>
                                return ast

                     -- ditto; the `t' means that the type checker is bypassed (that
                     -- aspect is handled above)  --Adam
                     "-ust" -> let ast = uncase $ noinline $ toinprog a
                                   s   = '\n':(ppt ast) ++ "\n"
                               in
                                 putStrLn s >>
                                 return ast

                     -- default pass:
                     _    -> let ast = scopevars $ noinline $ toinprog a
                                 s   = '\n':(ppt ast) ++ "\n"
                             in
                               putStrLn s >>
                               return ast

  ) >>= \ast ->

  hClose h >>

  return ast



--
-- run the defunctionalizer:
--
-- also takes a flag, as in 'ctc' above;
--
ctdfun :: String -> FilePath -> IO ()
ctdfun opt fp =
  openFile fp ReadMode >>= \h ->
  hGetContents h >>= \s ->
  preprocess s >>= \s' ->

  (
    case (runParser ctprog () fp s') of

      (Left _) -> error $ "parse error in " ++ fp

      -- if success, run it through the type-checker:
      (Right p) -> return $ cttc p

  ) >>= \as ->

  (
    case as of

      (Left _)  -> error $ "type error in " ++ fp

      -- if it passes the type-checker, inline the function applications:

      -- the order of transformations is a little hacky here,
      -- suggests a need for better organization at this level
      -- (2010.03.27) Schulz
      --
      (Right a) -> return $ inline $ scopevars $ noinline $ toinprog a

  ) >>= \is ->

  -- and then put it through the defunctionalizer:
  (

    let out = case opt of

                -- hit the FSM with our puny optimizations:
                "-o" -> let (((sigs, mems), chans), (d, ts)) = dfun is
                        in
                          writefsm (((sigs, mems), chans), (d, transtrans d ts))

                -- hit the FSM with our puny optimizations:
                _    -> writefsm $ dfun is
    in

    -- dump to the terminal:
    putStrLn out >>

    -- also write to the default output file:
    (openFile default_aout WriteMode) >>= \h' ->
    hPutStrLn h' out >>
    hClose h'

  ) >>

  hClose h >>
  return ()


--
-- test the first phase of code generation, i.e. CT -> RSI
--
-- (2010.08.23) Schulz
--
torsi :: String -> FilePath -> IO RSI
torsi opt fp = ctfe opt fp >>= \p ->
               let p' = rsi_gen p
               in
                 putStrLn (ppt p') >>
                 putStrLn "\n\n" >>
                 (openFile rsi_out WriteMode) >>= \h' ->
                 hPutStrLn h' (ppt p') >>
                 hClose h' >>
                 return p'


torsi_b :: String -> FilePath -> IO RSI_B
torsi_b opt fp = ctfe opt fp >>= \p ->
                 let p' = (imr_pass . rsi_gen) p
                 in
                   putStrLn (ppt p') >>
                   putStrLn "\n\n" >>
                   (openFile rsi_out WriteMode) >>= \h' ->
                   hPutStrLn h' (ppt p') >>
                   hClose h' >>
                   return p'


--
-- a default output file for the defunctionalizer:
--
default_aout :: String
default_aout = "out.des"


--
-- write out the AST as a legal Haskell declaration:
--
-- first argument is the option flag to 'ctc';
-- second argument is name of file to write;
-- third argument is path of the source file;
--
--
writeAST :: String -> String -> FilePath -> IO ()
writeAST opt tar fp =
  ctc opt fp >>= \s ->

  -- if program passes the type-checker, write the AST
  -- as Haskell syntax into the file named 'tar'
  -- in the current working directory:
  (openFile tar AppendMode) >>= \h' ->
  hFileSize h' >>= \n ->
  if (0 == n)
  then
    let tar' = map (\c -> if c == '.' then '_' else c) tar

        -- prettify the output string:
        s'   = pretdent 0 (show s)

    in
      (
        hPutStrLn h' ("ast__" ++ tar' ++ " = ") >> 
        hPutStrLn h' ('\n':s' ++ "\n") >>
        hClose h'
      )

  else error "Use an empty file!"


--
-- (slightly) prettify the output string
-- from 'writeAST':
--
pretdent :: Int -> String -> String

pretdent n ('(':s) = (replicate n ' ') ++
                     '(':'\n':
                     (pretdent (n + tabsize) s)

pretdent n (')':s) = (replicate (n - tabsize) ' ') ++
                     ')':'\n':
                     (pretdent (n - tabsize) s)

pretdent n (s:ss)  = let p = not . (\x -> elem x "()")
                     in
                       (replicate n ' ') ++
                       s:(takeWhile p ss) ++ '\n':(pretdent n (dropWhile p ss))

pretdent _ ""      = ""

tabsize :: Int
tabsize = 2




--
-- ETIC generation from front end
--
{-
gentest :: FilePath -> Cg ()
gentest fp =
  liftIOCg (openFile fp ReadMode) >>= \h ->
  liftIOCg (hGetContents h) >>= \s ->
  liftIOCg (preprocess s) >>= \s' ->

  (
    case (runParser ctprog () fp s') of

      (Left _) -> error $ "parse error in " ++ fp

      -- if success, run it through the type-checker:

      -- Updated for the new Data structures for cttc 02/05/10 --Ian
      --

      -- HEY IAN:
      --
      -- same story as last time, here;
      -- (slightly) new data structures,
      -- which you can use whenever or however you feel like;
      --

--      (Right p) -> return $ cttc p
      (Right p) -> return $ cttc_compat p
 
      -- 'main' is now at the head of the list.
      --
      -- 2010.02.08 Schulz
      --


  ) >>= \as ->

  (
    case as of

      (Left _)  -> error $ "type error in " ++ fp

      -- if it passes the type-checker, show the tree:
      (Right a) -> evalprog a
  ) >>

  liftIOCg (hClose h) >>
  return ()

------ run gentest
rungentest :: FilePath -> IO ()
rungentest a = runCg (gentest a) [] [] [] []
-}
--
-- test out the CT parser:
--
ctparse :: String -> IO ()
ctparse s = testParser ctprog s

--
-- clean the comments out of the input:
--
preprocess :: String -> IO String
preprocess s =
  let x = case (parse clean_input "" s) of
            (Left e)   -> error $ "What the hell, man: " ++ (show e) ++ "\n?!\n"
            (Right s') -> s'
  in
    return x


--
-- try out a given parser:
--
testParser :: (Show a,PPT a) => Parser a -> FilePath -> IO ()
testParser p fp =
  openFile fp ReadMode >>= \h ->
  hGetContents h >>= \s ->

  -- strip out the comments:
  preprocess s >>= \s' ->

  -- run the parser, dump the formatted output and raw AST:
  (return $ runParser p () fp s') >>= \t ->
  (
    case t of
      (Left _)   -> error $ "parse error in " ++ fp
      (Right t') -> putStrLn ('\n':(ppt t')) >> putStrLn ('\n':'\n':(show t'))
  ) >>

  hClose h >>
  return ()

--
-- this function is no longer in use;
-- compilation occurs through passes invoked in 'ctc' above
--
-- (2010.09.08) Schulz
--
{-
testCompiler :: String -> FilePath -> IO ()
testCompiler opt filename = ctfe opt filename >>= \ ctprog ->
                            let
                               eticprog = codegen ctprog
                            in
                                let 
                                    cprog_str = Deprecated.ETIC.GenC.runM (genC eticprog )
                                 in
                                    putStr ( "\n" ++ cprog_str)
                                
--                                putStr out >>

                               -- write the concrete output to a file,
                               -- as per Andrew's request:

--                               openFile etic_out WriteMode >>= \h ->
  ---                             hPutStr h out >>
     --                          hPutStr h ("\n\n****\n\n" ++(show eticprog)) >>
       --                        hClose h >>

         --                      putStr ((show eticprog) ++ "\n\n") >>
           --                    putStr ("concrete ETIC output written to "
             --                           ++ etic_out ++ "\n\n")
                                   
-}


{-
testUnroller :: String -> FilePath -> IO ()
testUnroller opt filename = ctfe opt filename >>= \ ctprog ->
                            putStr (ppt (doUnroll ctprog))
-}



--
-- default ETIC generator output file:
-- 
etic_out :: FilePath
etic_out = "./etic.out"


--
-- the untyped lambda calculus reifier,
-- hooked up so that CT output goes through the front-end,
-- to the ETIC interpreter:
--

-- also deprecated; this will go away eventually
-- but I like to leave things to posterity
--
-- 2011.02.14 Schulz
{-
ct_reify :: FilePath -> IO ()
ct_reify fp =

  openFile fp ReadMode >>= \h ->
  hGetContents h >>= \s ->

  -- reify lambda term to produce a CT-syntax string:
  (return $ (reify_term . ulparse) s) >>= \r ->

  openFile reify_header ReadMode >>= \h' ->
  hGetContents h' >>= \l -> -- get needed function declarations from the header
  openFile reify_out WriteMode >>= \out ->
  hPutStr out (l ++ "\n\nmain =" ++ r ++ "\n") >>
  hClose out >>

  ctfe "" reify_out >>= \ct ->           -- put program through the front-end
  return (codegen ct) >>= \etic ->      -- generate ETIC from the AST
--  return (etic_interp etic) >>= \v ->   -- interpret the ETIC program

  putStrLn ("\n***CT front-end accepted reifier-produced term:\n\n" ++ r) >>
--  putStrLn ("\n***ETIC interpreter returned " ++ (show v) ++ " in main\n\n") >>

  openFile etic_out WriteMode >>= \e_out ->
--  hPutStr e_out (ppt_etic etic) >>

  putStrLn ("\n\nETIC output written to " ++ etic_out) >>

  hClose h >>
  hClose h' >>
  hClose e_out >>
  return ()
-}

--
-- file containing declarations to include when passing the
-- reifier output to the front-end:
--
reify_header :: FilePath
reify_header = "./reify.ct"

--
-- default (temporary) output file for the complete CT program
-- produced by the reifier, before being passed to the front-end:
--
reify_out :: FilePath
reify_out = "./out.reify.ct"


--
-- short-hand for running the ETIC printer:
--
--ppt_etic = Control.Monad.Identity.runIdentity . Deprecated.ETIC.Print.pprint
                                            

--
-- our default Microblaze target:
--
default_target :: Target
default_target = ((MB, mb_regs), mb_base_map)

default_arch :: Arch
default_arch = MB


-- THIS IS THE END OF THE FILE --
