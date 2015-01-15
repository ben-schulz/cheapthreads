--
-- this is ~/cheapthreads/ctc_working/CT-1.0/CT/PrimitiveTySigs.hs
--
-- type signatures for built-in CT primitives;
--
-- these are used by the type inferencer on encountering a primitive
-- operation in the AST
--
-- put here 2010.01.17
--
-- Schulz
--

module CT.PrimitiveTySigs where

import CT.Syntax

--
-- top-level call for typing a prim-op
--
typeOfCTOp :: CTPrimOp -> CTTy
typeOfCTOp (Un u)  = typeOfUnOp u
typeOfCTOp (Bin b) = typeOfBinOp b
typeOfCTOp (Tri t) = typeOfTriOp t

--
-- type a unary primitive:
--
typeOfUnOp :: CTPrimUnOp -> CTTy
typeOfUnOp CTNeg = CTAbsTy CTIntTy CTIntTy
typeOfUnOp CTNot = CTAbsTy CTBoolTy CTBoolTy
typeOfUnOp Fst   = CTAbsTy (CTPairTy (CTTyVar $ primtyvar 1)
                                     (CTTyVar $ primtyvar 2))
                           (CTTyVar $ primtyvar 1)

typeOfUnOp Snd   = CTAbsTy (CTPairTy (CTTyVar $ primtyvar 1)
                                     (CTTyVar $ primtyvar 2))
                           (CTTyVar $ primtyvar 2)


--
-- type a binary primitive:
--
typeOfBinOp :: CTPrimBinOp -> CTTy

typeOfBinOp CTCons  = CTAbsTy (CTTyVar $ primtyvar 3)
                              (CTAbsTy 
                                (CTListTy (CTTyVar $ primtyvar 3))
                                (CTListTy (CTTyVar $ primtyvar 3))
                              )

typeOfBinOp CTPlus  = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTIntTy)
typeOfBinOp CTMinus = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTIntTy)
typeOfBinOp CTMult  = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTIntTy)
typeOfBinOp CTIDiv  = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTIntTy)
typeOfBinOp CTExpn  = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTIntTy)

typeOfBinOp CTBitCat  = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTIntTy)

typeOfBinOp CTAnd = CTAbsTy CTBoolTy (CTAbsTy CTBoolTy CTBoolTy)
typeOfBinOp CTOr  = CTAbsTy CTBoolTy (CTAbsTy CTBoolTy CTBoolTy)

typeOfBinOp CTLTTest  = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTBoolTy)
typeOfBinOp CTGTTest  = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTBoolTy)
typeOfBinOp CTLTETest = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTBoolTy)
typeOfBinOp CTGTETest = CTAbsTy CTIntTy (CTAbsTy CTIntTy CTBoolTy)

typeOfBinOp CTEqTest   = CTAbsTy (CTTyVar $ primtyvar 4)
                                 (CTAbsTy (CTTyVar $ primtyvar 4) CTBoolTy)

typeOfBinOp CTIneqTest = CTAbsTy (CTTyVar $ primtyvar 5)
                                 (CTAbsTy (CTTyVar $ primtyvar 5) CTBoolTy)


--
-- type of a ternary operator:
--
typeOfTriOp :: CTPrimTernOp -> CTTy
typeOfTriOp CTBitSlice = CTAbsTy CTIntTy
                         (CTAbsTy CTIntTy (CTAbsTy CTIntTy CTIntTy))

--
-- by convention we use '_' to generate a polymorphic
-- type variable in the signature for a built-in
--
-- IMPORTANT: the type variables for built-in signatures
-- must be made distinct; using the same variable for built-ins
-- with possibly different type signatures will create problems
-- for the unifier in TypeChecker.
--
--
-- Current number of distinct type variables used here: 5
--
-- 2010.05.06 Schulz
--
primtyvar :: Int -> String
primtyvar n = take n $ repeat '_'



-- THIS IS THE END OF THE FILE --
