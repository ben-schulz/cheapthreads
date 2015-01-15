--
-- this is ~/cheapthreads/ctc/ct/defunctionalizer/builtins.hs
-- 
-- built-in function declarations used by the defunctionalizer's inliner
--
--  put here 01.03.09
--
--  Schulz

--
-- currently this contains: '+', '-', '*', '==', '!=', '&&', '||', 'not',
--                          '<', '>', '<=', '>=', '|||' (bit-wise OR),
--                          '&&&' (bit-wise AND), 'bwnot' (bit-wise NOT),
--                          '<<<' (bit-shift left), '>>>' (bit-shift right)
--
--
-- 
--

module CT.Defunctionalizer.DFBuiltIns where

import CT.Defunctionalizer.DefunTypes
import CT.Syntax

default_pos :: CtsSrcPos
default_pos = CtsSrcPos "builtin" 0 0

--
-- the master list of all built-ins:
--
builtindecs :: [CtsDecl]
builtindecs = [
               plusdec,
               minusdec,
               multdec,
               equalitydec,
               inequalitydec,
               ltdec,
               gtdec,
               ltedec,
               gtedec,
               anddec,
               ordec,
               notdec,
               bwanddec,
               bwordec,
               bwnotdec,
               shiftldec,
               shiftrdec,
               readdec,
               writedec]


--
-- it appears this is not being used anymore
--
-- 17.07.09 Schulz
--
{-
builtins :: [FunDec]
builtins = [ctsPlus, ctsMinus]
-}

--                                        --
--                                        --
-- built-in definitions and declarations: --
--                                        --
--                                        --

--
-- Addition:
-- 

plusdec :: CtsDecl
plusdec = CtsFunDecl default_pos "+" ["ctsPlus_x", "ctsPlus_y"] plusexpr

plusexpr :: CtsExpr
plusexpr =
  CtsTuple [(CtsVar "+" TyInt),
            (CtsVar "ctsPlus_x" TyInt),
            (CtsVar "ctsPlus_y" TyInt)] TyInt


--
-- Subtraction:
--
minusdec :: CtsDecl
minusdec = CtsFunDecl default_pos "-" ["ctsMinus_x", "ctsMinus_y"] minusexpr

minusexpr :: CtsExpr
minusexpr =
  CtsTuple [(CtsVar "-" TyInt),
            (CtsVar "ctsMinus_x" TyInt),
            (CtsVar "ctsMinus_y" TyInt)] TyInt

--
-- Multiplication:
-- 

multdec :: CtsDecl
multdec = CtsFunDecl default_pos "*" ["ctsMult_x", "ctsMult_y"] multexpr

multexpr :: CtsExpr
multexpr =
  CtsTuple [(CtsVar "*" TyInt),
            (CtsVar "ctsMult_x" TyInt),
            (CtsVar "ctsMult_y" TyInt)] TyInt



--
-- Equality test:
--
equalitydec :: CtsDecl
equalitydec = CtsFunDecl default_pos "==" ["ctsEquality_x", "ctsEquality_y"]
             equalityexpr

equalityexpr :: CtsExpr
equalityexpr =
  CtsTuple [(CtsVar "==" TyBool),
            (CtsVar "ctsEquality_x" TyInt),
            (CtsVar "ctsEquality_y" TyInt)] TyBool

--
-- Inequality test:
--
inequalitydec :: CtsDecl
inequalitydec = CtsFunDecl default_pos "!="
                  ["ctsInequality_x", "ctsInequality_y"]
                    inequalityexpr

inequalityexpr :: CtsExpr
inequalityexpr =
  CtsTuple [(CtsVar "!=" TyBool),
            (CtsVar "ctsInequality_x" TyInt),
            (CtsVar "ctsInequality_y" TyInt)] TyBool

--
-- less-than test:
--
ltdec :: CtsDecl
ltdec = CtsFunDecl default_pos "<" ["ctsLT_x", "ctsLT_y"] ltexpr
                    
ltexpr :: CtsExpr
ltexpr =
  CtsTuple [(CtsVar "<" TyBool),
            (CtsVar "ctsLT_x" TyInt),
            (CtsVar "ctsLT_y" TyInt)] TyBool

--
-- less-than-or-equal test:
--
ltedec :: CtsDecl
ltedec = CtsFunDecl default_pos "<=" ["ctsLTE_x", "ctsLTE_y"] lteexpr
                    
lteexpr :: CtsExpr
lteexpr =
  CtsTuple [(CtsVar "<=" TyBool),
            (CtsVar "ctsLTE_x" TyInt),
            (CtsVar "ctsLTE_y" TyInt)] TyBool

--
-- greater-than test:
--
gtdec :: CtsDecl
gtdec = CtsFunDecl default_pos ">" ["ctsGT_x", "ctsGT_y"] gtexpr
                    
gtexpr :: CtsExpr
gtexpr =
  CtsTuple [(CtsVar ">" TyBool),
            (CtsVar "ctsGT_x" TyInt),
            (CtsVar "ctsGT_y" TyInt)] TyBool

--
-- greater-than-or-equal test:
--
gtedec :: CtsDecl
gtedec = CtsFunDecl default_pos ">=" ["ctsGTE_x", "ctsGTE_y"] gteexpr
                    
gteexpr :: CtsExpr
gteexpr =
  CtsTuple [(CtsVar ">=" TyBool),
            (CtsVar "ctsGTE_x" TyInt),
            (CtsVar "ctsGTE_y" TyInt)] TyBool

--
-- logical conjunction:
--
anddec :: CtsDecl
anddec = CtsFunDecl default_pos "&&" ["ctsAnd_x", "ctsAnd_y"] andexpr
                    
andexpr :: CtsExpr
andexpr =
  CtsTuple [(CtsVar "&&" TyBool),
            (CtsVar "ctsAnd_x" TyBool),
            (CtsVar "ctsAnd_y" TyBool)] TyBool

--
-- logical disjunction:
--
ordec :: CtsDecl
ordec = CtsFunDecl default_pos "||" ["ctsOr_x", "ctsOr_y"] orexpr
                    
orexpr :: CtsExpr
orexpr =
  CtsTuple [(CtsVar "||" TyBool),
            (CtsVar "ctsOr_x" TyBool),
            (CtsVar "ctsOr_y" TyBool)] TyBool

--
-- logical negation:
--
notdec :: CtsDecl
notdec = CtsFunDecl default_pos "not" ["ctsNot_x"] notexpr

notexpr :: CtsExpr
notexpr =
  CtsTuple [(CtsVar "not" TyBool),
            (CtsVar "ctsNot_x" TyBool)] TyBool
--
-- bitwise AND:
--
bwanddec :: CtsDecl
bwanddec = CtsFunDecl default_pos "&&&" ["ctsbwand_x", "ctsbwand_y"] bwandexpr
                    
bwandexpr :: CtsExpr
bwandexpr =
  CtsTuple [(CtsVar "&&&" TyInt),
            (CtsVar "ctsbwand_x" TyInt),
            (CtsVar "ctsbwand_y" TyInt)] TyInt

--
-- bitwise OR:
--
bwordec :: CtsDecl
bwordec = CtsFunDecl default_pos "|||" ["ctsbwor_x", "ctsbwor_y"] bworexpr
                    
bworexpr :: CtsExpr
bworexpr =
  CtsTuple [(CtsVar "|||" TyInt),
            (CtsVar "ctsbwor_x" TyInt),
            (CtsVar "ctsbwor_y" TyInt)] TyInt

--
-- bitwise NOT:
--
bwnotdec :: CtsDecl
bwnotdec = CtsFunDecl default_pos "bwnot" ["ctsbwnot_x", "ctsbwnot_y"] bwnotexpr
                    
bwnotexpr :: CtsExpr
bwnotexpr =
  CtsTuple [(CtsVar "bwnot" TyInt),
            (CtsVar "ctsbwnot_x" TyInt),
            (CtsVar "ctsbwnot_y" TyInt)] TyInt

--
-- bit-shift left:
--
shiftldec :: CtsDecl
shiftldec = CtsFunDecl default_pos ">>>" ["ctsshiftl_x", "ctsshiftl_y"] shiftlexpr
                    
shiftlexpr :: CtsExpr
shiftlexpr =
  CtsTuple [(CtsVar ">>>" TyInt),
            (CtsVar "ctsshiftl_x" TyInt),
            (CtsVar "ctsshiftl_y" TyInt)] TyInt

--
-- bit-shift right:
--
shiftrdec :: CtsDecl
shiftrdec = CtsFunDecl default_pos "<<<" ["ctsshiftr_x", "ctsshiftr_y"] shiftrexpr
                    
shiftrexpr :: CtsExpr
shiftrexpr =
  CtsTuple [(CtsVar "<<<" TyInt),
            (CtsVar "ctsshiftr_x" TyInt),
            (CtsVar "ctsshiftr_y" TyInt)] TyInt



--
-- Memory Read:
--
readdec :: CtsDecl
readdec = CtsFunDecl default_pos "read" ["ctsRead_mem", "ctsRead_addr"] readexpr

readexpr :: CtsExpr
readexpr =
  CtsTuple [(CtsVar "read" TyUnit),
            (CtsVar "ctsRead_mem" TyUnit),
            (CtsVar "ctsRead_addr" TyUnit)] TyUnit

--
-- Memory Write:
--
writedec :: CtsDecl
writedec = CtsFunDecl default_pos "write"
             ["ctsWrite_mem", "ctsWrite_addr", "ctsWrite_val"] writeexpr

writeexpr :: CtsExpr
writeexpr =
  CtsTuple [(CtsVar "write" TyUnit),
            (CtsVar "ctsWrite_mem" TyUnit),
            (CtsVar "ctsWrite_addr" TyUnit),
            (CtsVar "ctsWrite_val" TyUnit)] TyUnit

--
-- it appears that what follows is no longer being used
--
-- 17.07.09 Schulz
--

{-
ctsPlus :: FunDec
--ctsPlus = ("+", (["x", "y"], CtsLitExpr (CtsLitInt 1) TyInt))
ctsPlus = ("+", (["ctsPlus_x", "ctsPlus_y"], plusexpr))


ctsMinus :: FunDec
--ctsMinus = ("+", (["x", "y"], CtsLitExpr (CtsLitInt 2) TyInt))
ctsMinus = ("-", (["ctsMinus_x", "ctsMinus_y"], minusexpr))
-}

