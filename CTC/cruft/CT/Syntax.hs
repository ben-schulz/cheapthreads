module CT.Syntax where

import Data.List

data CtsProg = CtsProg [CtsDecl] deriving Show

data CtsSrcPos = CtsSrcPos String Int Int deriving Eq

instance Show CtsSrcPos where
     show (CtsSrcPos filename line col) = filename ++ ":" ++ show line ++ ":" ++ show col
     
instance Ord CtsSrcPos where
     compare (CtsSrcPos _ line1 col1) (CtsSrcPos _ line2 col2) | line1 /= line2 = compare line1 line2
                                                               | otherwise      = compare col1 col2

data CtsType = TyInt
             | TyBool
             | TyString
             | TyMemory  -- provisional, for defunctionalizer back-end; 24.07.09
             | TyInPort  | TyOutPort -- the port types (added 2009.12.14)
             | TyUnit
             | TyADT CtsIdent
             | TyTuple [CtsType]
             | TyList CtsType
             | TyMonadic CtsIdent CtsType
             deriving Show
             
showType :: CtsType -> String
showType TyInt           = "Int"
showType TyBool          = "Bool"
showType TyString        = "String"
showType TyMemory        = "Memory"
showType TyUnit          = "()"
showType (TyADT n)       = n
showType (TyTuple tys)   = "(" ++ intercalate "," (map showType tys) ++ ")"
showType (TyList t)      = "[" ++ showType t ++ "]"
showType (TyMonadic m t) = "(" ++ m ++ " " ++ showType t ++ ")"

--
-- added Eq for type synonyms;
-- though not strictly necessary,
-- it seems as if it should be useful elsewhere as well
--
-- 26.06.09 Schulz
--
instance Eq CtsType where
  TyInt == TyInt                     = True
  TyBool == TyBool                   = True
  TyString == TyString               = True
  TyUnit == TyUnit                   = True
  (TyADT x) == (TyADT y)             = (x == y)
  (TyTuple ss) == (TyTuple ts)       = foldr 
                                         ((&&) . (\(x, y) -> (x == y)))
                                         True
                                         (zip ss ts)
  (TyList x) == (TyList y)           = (x == y)
  (TyMonadic n t) == (TyMonadic m s) = (n == m) && (t == s)
  _ == _                             = False
  x /= y                             = not (x == y)



noType :: CtsType
--noType = error "Type checker has not been run yet"
noType = TyUnit

data CtsConDecl = CtsConDecl CtsIdent [CtsType] deriving Show

data CtsDecl = CtsMonadDecl CtsSrcPos CtsIdent [CtsMonadLayer]
             | CtsFunTySig CtsSrcPos CtsIdent [CtsType] CtsType 
             | CtsFunDecl CtsSrcPos CtsIdent [CtsIdent] CtsExpr
             | CtsRecDecl [CtsDecl]
             | CtsTypeDecl CtsSrcPos CtsIdent CtsType
             | CtsDataDecl CtsSrcPos CtsIdent [CtsConDecl]
             deriving Show

data CtsMonadLayer = CtsResumptionLayer CtsIdent
                   | CtsStateLayer CtsType CtsIdent
                   | CtsReactiveLayer CtsIdent CtsIdent CtsIdent
                   deriving Show

--
-- Added wildcard pattern for SecureQ example;
--
-- only corresponding accomodations of the wildcard
-- are in the parser, thus far
--
-- 03.07.09 Schulz
--

--
-- Also added the infix-app pattern;
-- the structure of this is a temporary kludge
--
-- 03.07.09 Schulz
--

data CtsPat = CtsPConstr CtsConstr [CtsIdent]
            | CtsPTuple [CtsIdent]
            | CtsPInfixApp CtsInfixPat CtsIdent CtsIdent
            | CtsPWildCard
            deriving Show

--
-- I've made the infix pattern operator
-- a constructed type just to keep it
-- better separated from its operands 
--
-- 03.07.09 Schulz
--

newtype CtsInfixPat = CtsInfixPat CtsIdent deriving Show

data CtsExpr = CtsApp CtsIdent [CtsExpr] CtsType
             | CtsFixApp [CtsIdent] CtsExpr [CtsExpr] CtsType

--
-- SemiFix is a conditional loop controlled by evaluating the first argument;
-- see '~/cheapthreads/ctc/ct/defunctionalizer/defun.log.txt' for details
--
             | CtsSemiFixApp CtsExpr [CtsIdent] CtsExpr [CtsExpr] CtsType
--

             | CtsInfixApp CtsExpr CtsIdent CtsExpr CtsType
             | CtsConstrApp CtsConstr [CtsExpr] CtsType
             
             | CtsLitExpr CtsLit CtsType
             | CtsVar CtsIdent CtsType
             | CtsNeg CtsExpr CtsType
             | CtsIfThenElse CtsExpr CtsExpr CtsExpr CtsType
             | CtsCase CtsExpr [CtsAlt] CtsType
             | CtsTuple [CtsExpr] CtsType
             | CtsList [CtsExpr] CtsType
             | CtsUnit CtsType
             | CtsEmptyList CtsType -- FIXME: To work around some silliness in the type checker this MUST be explicitly typed with ::. Sort of an ad hoc solution.
             | CtsLet [(CtsIdent,CtsExpr)] CtsExpr CtsType -- FIXME: I'm using this internally in the partial evaluator
             
             | CtsBind CtsExpr CtsIdent CtsExpr CtsType
             | CtsBindNull CtsExpr CtsExpr CtsType
             | CtsReturn CtsExpr CtsType
             | CtsSignalReq CtsSignal CtsType
             deriving Show

data CtsSignal = Cont | GetPorts deriving Show

typeOf :: CtsExpr -> CtsType
typeOf (CtsApp _ _ t)          = t
typeOf (CtsFixApp _ _ _ t)     = t
typeOf (CtsInfixApp _ _ _ t)   = t
typeOf (CtsConstrApp _ _ t)    = t
typeOf (CtsLitExpr _ t)        = t
typeOf (CtsVar _ t)            = t
typeOf (CtsNeg _ t)            = t
typeOf (CtsIfThenElse _ _ _ t) = t
typeOf (CtsCase _ _ t)         = t
typeOf (CtsTuple _ t)          = t
typeOf (CtsList _ t)           = t
typeOf (CtsUnit t)             = t
typeOf (CtsEmptyList t)        = t
typeOf (CtsLet _ _ t)          = t
typeOf (CtsBind _ _ _ t)       = t
typeOf (CtsBindNull _ _ t)     = t
typeOf (CtsReturn _ t)         = t

data CtsAlt = CtsAlt CtsPat CtsExpr deriving Show

data CtsLit = CtsLitInt Int | CtsLitBool Bool | CtsLitString String deriving Show

type CtsIdent = String

type CtsConstr = String

pprDecl :: CtsDecl -> String
pprDecl (CtsMonadDecl _ m layers) = "<<monad decl " ++ m ++ ">>"
pprDecl (CtsFunTySig _ f tys ty) = f ++ " :: " ++ intercalate " -> " (map showType (tys++[ty]))
pprDecl (CtsFunDecl _ f xs e) = f ++ concatMap (\x -> " " ++ x) xs ++ " = " ++ pprExpr e ++ "\n"
pprDecl (CtsRecDecl ds) = "[[[[[\n" ++ concatMap (\d -> pprDecl d ++ "\n") ds ++ "]]]]]"
pprDecl (CtsTypeDecl _ n ty) = "type " ++ n ++ " = " ++ showType ty
pprDecl (CtsDataDecl _ n _) = "<<data decl " ++ n ++ ">>"

pprAlt :: CtsAlt -> String
pprAlt (CtsAlt (CtsPConstr ctor xs) e) = "(" ++ ctor ++ concatMap (\x -> " " ++ x) xs ++ ") -> " ++ pprExpr e
pprAlt (CtsAlt (CtsPTuple xs) e)       = "(" ++ intercalate "," xs ++ ") -> " ++ pprExpr e

pprExpr :: CtsExpr -> String
pprExpr (CtsApp f es _) = "(" ++ f ++ concatMap (\e -> " " ++ pprExpr e) es ++ ")"
pprExpr (CtsFixApp xs b es _) = "((fix (\\" ++ concatMap (\x -> x ++ " ") xs ++ "-> " ++ pprExpr b ++ ")) " ++ concatMap pprExpr es ++ ")"
pprExpr (CtsInfixApp e1 op e2 _) = "(" ++ pprExpr e1 ++ " " ++ op ++ " " ++ pprExpr e2 ++ ")"
pprExpr (CtsConstrApp ctor es _) = "(" ++ ctor ++ concatMap (\e -> " " ++ pprExpr e) es ++ ")"
pprExpr (CtsLitExpr (CtsLitInt x) _) = show x
pprExpr (CtsLitExpr (CtsLitBool b) _) = show b
pprExpr (CtsLitExpr (CtsLitString s) _) = show s
pprExpr (CtsVar x _) = x
pprExpr (CtsNeg e _) = "(-" ++ pprExpr e ++ ")"
pprExpr (CtsIfThenElse b t f _) = "(if " ++ pprExpr b ++ " then " ++ pprExpr t ++ " else " ++ pprExpr f ++ ")"
pprExpr (CtsCase e alts _) = "(case " ++ pprExpr e ++ " of { " ++ intercalate " ; " (map pprAlt alts) ++ " })"
pprExpr (CtsTuple es _) = "(" ++ intercalate "," (map pprExpr es) ++ ")"
pprExpr (CtsList es _) = "[" ++ intercalate "," (map pprExpr es) ++ "]"
pprExpr (CtsUnit _) = "()"
pprExpr (CtsLet bindings e t) = "(let { " ++ intercalate " ; " (map (\(x,e) -> x ++ " = " ++ pprExpr e) bindings) ++ " } in { " ++ pprExpr e ++ " })"
pprExpr (CtsBind e1 x e2 _) = "(" ++ pprExpr e1 ++ " >>= \\ " ++ x ++ " -> " ++ pprExpr e2 ++ ")"
pprExpr (CtsBindNull e1 e2 _) = "(" ++ pprExpr e1 ++ " >> " ++ pprExpr e2 ++ ")"
pprExpr (CtsReturn e _) = "(return " ++ pprExpr e ++ ")"
