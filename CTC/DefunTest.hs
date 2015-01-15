module DefunTest where

import CT.Parser
import CT.Syntax
import CT.Recursion
import CT.TypeChecker
import CT.Defunctionalizer.PreDefun
import CT.Defunctionalizer.DefunTypes
import CT.Defunctionalizer.DefunR
--import CT.Defunctionalizer.DFExec --temporarily shutoff while working 20.07.09
import CT.Defunctionalizer.WriteFSM

--
-- the type-checker is being temporarily circumvented
-- to expedite compiling of SecureQ
--
-- 06.07.09 Schulz
--
 
{-
--
-- temporarily shut off while working 20.07.09
--
runDFExec :: String -> IO ( )
runDFExec filename =
  do
    prog <- parse filename
--    case (tc (groupDecls prog)) of
    case ((\p -> Right p) (groupDecls prog)) of
--      (Left e)             -> print e
      (Right (CtsProg ds)) -> let rules = defun (CtsProg ds)
                                  ast = prepast $ CtsProg ds
                                  k = map cleanTypes $ mkState ast
                                  vreg = mkVReg k
                              in
                                dfexec vreg (PCL init_label, [ ]) rules
-}

-- temporarily shut off to prevent extraneous type errors 20.07.09 Schulz
writeFSMLang :: String -> IO ( )
writeFSMLang filename =
  do
    prog <- parse filename
    case (tc_ann (groupDecls prog)) of
--    case ((\p -> Right p) (groupDecls prog)) of
      (Left e)       -> print e
      (Right p@(CtsProg ds)) -> putStrLn $ writeFSMPlus $ defunTop p

{-
                              let rules = defunPlus (CtsProg ds)
                                  ast = prepast $ CtsProg ds
                                  k = mkStatePlus ast
                              in
                                putStrLn $ writeFSMPlus k rules
-}

runDefun :: String -> IO ()
runDefun filename = do
                       prog <- parse filename
                       case (tc_ann (groupDecls prog)) of
--                       case ((\p -> Right p) (groupDecls prog)) of
		         (Left e)       -> print e
			 (Right progTC) -> putStr $ pptRulesPlus (defunPlus progTC)
--			 (Right progTC) -> putStr $ pptRules (defun progTC)


runPrep :: String -> IO ()
runPrep filename = do
                     prog <- parse filename
                     case (tc_ann (groupDecls prog)) of
--                     case ((\p -> Right p) (groupDecls prog)) of
                       (Left e)       -> print e
	               (Right progTC) -> print (prepast progTC)
--	               (Right (CtsProg ds)) -> print (debugast ds)
