module Test where

import CT.Parser
import CT.Recursion
import CT.TypeChecker
import CT.PartialEvaluator
import CT.Compiler.Codegen
import CT.Compiler.ThreeAddressCode
import CT.Compiler.TacSemantics
import CT.Compiler.TACtoMBlaze
import CT.Syntax
import Data.List
import Data.Graph

dumpAST :: String -> IO ()
dumpAST filename = do
                      prog <- parse filename
                      print prog


dumpTC :: String -> IO ()
dumpTC filename = do
                     prog       <- parse filename
                     let progGD =  groupDecls prog
                     case (tc progGD) of
                        (Left e)       -> print e
                        (Right progTC) -> printProgDecls progTC

dumpTAC :: String -> IO ()
dumpTAC filename = do
                      prog       <- parse filename
                      let progGD =  groupDecls prog
                      case (tc progGD) of
                         (Left e)       -> print e
                         (Right progTC) -> let
                                              progPE = pe progTC
                                           in
                                              print (codegen progPE)
--Dump TAC without using the Type Checker
dumpTACnotc :: String -> IO ()
dumpTACnotc filename = do
                      prog       <- parse filename
                      let progGD =  groupDecls prog
                      print (codegen (pe progGD))

dumpMBnotc :: String -> IO ()
dumpMBnotc filename = do
                     prog       <- parse filename
                     let progGD =  groupDecls prog
                     let (TacProg cmds) = (codegen (pe (progGD)))
                     putStrLn (tacToMBlaze cmds)
--The type checker is broken as of the writing of runtac
--This guy runs with the compiler's unplugged typechecker  
runTAC :: String -> IO ()
runTAC filename = do
                      prog       <- parse filename
                      let progGD =  groupDecls prog
                      go (codegen (pe progGD))

saveTAC :: String -> String -> IO ()
saveTAC infile outfile = do
                            prog       <- parse infile
                            let progGD =  groupDecls prog
                            case (tc progGD) of
                               (Left e)       -> print e
                               (Right progTC) -> let
                                                    progPE = pe progTC
                                                 in
                                                    writeFile outfile (show $ codegen progPE)

dumpMB :: String -> IO ()
dumpMB filename = do
                     prog       <- parse filename
                     let progGD =  groupDecls prog
                     case (tc progGD) of
                        (Left e)       -> print e
                        (Right progTC) -> putStrLn $  tacToMBlaze cmds
                                            where (TacProg cmds) = codegen progTC

dumpCG :: String -> IO ()
dumpCG filename = do
                     prog <- parse filename
                     print (buildCallGraph prog)

dumpSCCs :: String -> IO ()
dumpSCCs filename = do
                       prog <- parse filename
                       let showSCC (AcyclicSCC v) = v
                           showSCC (CyclicSCC vs) = "(" ++ intercalate "," vs ++ ")"
                       print (map showSCC (sccs (buildCallGraph prog)))
                       
dumpGD :: String -> IO ()
dumpGD filename = do
                     prog                  <- parse filename
                     let progGD            =  groupDecls prog
                         (CtsProg declsGD) =  progGD
                     mapM_ print declsGD

printProgDecls :: CtsProg -> IO ()
printProgDecls (CtsProg ds) = mapM_ (putStrLn . pprDecl) ds
--printProgDecls (CtsProg ds) = mapM_ print ds

dumpPE :: String -> IO ()
dumpPE filename = do
                     prog       <- parse filename
                     let progGD =  groupDecls prog
                     case (tc progGD) of
                        (Left e)       -> print e
                        (Right progTC) -> let
                                             progPE = pe progTC
                                          in
                                             printProgDecls progPE
