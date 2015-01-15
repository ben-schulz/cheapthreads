--
-- this is ~/cheapthreads/ctc_working/CT-1.0/CT/ANAST.hs
--
-- data structures for the annotation of the abstract syntax tree;
-- first used in module TypeChecker, and subsequently used by Inliner;
--
-- moved here from inside of ./TypeChecker.hs
--
-- 2010.02.15
--
-- Schulz
--

module CT.ANAST where

import CT.Syntax
import CT.PPT

import Data.Maybe

--
-- annotation of the expression tree:
--
-- these are only the data structures;
-- annotation is actually done during type inference
--

--
-- for now, we only annotate with types:
--
type AN = CTTy


--
-- first pair: the function identifier, and its type;
--
-- second pair: the list of free variables, together with
--              the body of the function
--

type ANFunDec = ((CTIdent, CTTy), ([CTIdent], ANAST))

--
-- first portion of the tuple is the declaration of 'main';
-- second portion is the list of all other functions
--

type ANProg   = (ANDec, ([DataDec], [MonadDec]))
type ANDec = (ANFunDec, [ANFunDec])


--
-- an annotated tree with a structure
-- isomorphic to CTExpr:
--

data ANAST = CTAppAN ANAST ANAST AN
           | CTLamAN CTIdent ANAST AN

           -- monadic expressions:
           | CTBindAN ANAST ANAST AN
           | CTNullBindAN ANAST ANAST AN
           | CTReturnAN ANAST AN

           -- stateful operators:
           | CTGetAN CTIdent AN
           | CTPutAN CTIdent ANAST AN
           | CTPopAN CTIdent AN
           | CTPushAN CTIdent ANAST AN
           | CTReadAN CTIdent ANAST AN
           | CTWriteAN CTIdent ANAST ANAST AN

           -- resumptive operators:
           | CTStepAN ANAST AN
           | CTResumeAN ANAST AN
           | CTResumeReAN ANAST ANAST AN
           | CTLoopAN ANAST AN
           | CTBreakAN ANAST AN
           | CTFixAN ANAST AN

           -- reactive-resumptive operators:
           | CTSignalAN ANAST AN
           | CTGetReqAN ANAST AN

           -- primitive operations:
           | CTPrim1aryAN CTPrimOp ANAST AN
           | CTPrim2aryAN CTPrimOp ANAST ANAST AN
           | CTPrim3aryAN CTPrimOp ANAST ANAST ANAST AN

           -- control flow:
           | CTBranchAN ANAST ANAST ANAST AN
           | CTCaseAN ANAST [(CTPat, ANAST)] AN

           -- tuples:
           | CTPairAN ANAST ANAST AN
           | CTListAN [ANAST] AN

           -- variables:
           | CTVarAN CTIdent AN
 
           -- constructed values, with possible arguments:
           | CTConAN CTIdent [ANAST] AN

           -- literals:
           | CTLitAN Literal AN
           | CTUnitAN AN
           deriving Show

instance PPT ANAST where

  ppt (CTAppAN e e' t)   = (ppt e) ++ ' ':(ppt e') ++ ':':':':(ppt t)
  ppt (CTLamAN x e t)    = "\\" ++ x ++ " ->\n" ++ (ppt e) ++ ':':':':(ppt t)

  ppt (CTBindAN e lam t)     = (ppt e) ++ " >>= " ++ (ppt lam)
                               ++ ':':':':(ppt t)
  ppt (CTNullBindAN e e' t)  = (ppt e) ++ " >>\n" ++ (ppt e') ++ ':':':':(ppt t)
  ppt (CTReturnAN e t)       = "return (" ++ (ppt e) ++ ")" ++ ':':':':(ppt t)

  ppt (CTGetAN x t)   = "get " ++ x ++ ':':':':(ppt t)
  ppt (CTPutAN x e t) = "put " ++ x ++ " (" ++ (ppt e) ++ ")" ++ ':':':':(ppt t)

  ppt (CTPopAN x t)    = "pop " ++ x ++ ':':':':(ppt t)
  ppt (CTPushAN x e t) = "push " ++ x ++
                         " (" ++ (ppt e) ++ ")" ++ ':':':':(ppt t)

  ppt (CTReadAN x i t)     = "get " ++ x ++ '[':(ppt i) ++ "]" ++
                             ':':':':(ppt t)
  ppt (CTWriteAN x i e t)  = "put " ++ x ++ '[':(ppt i) ++ "]" ++
                             " (" ++ (ppt e) ++ ")" ++ ':':':':(ppt t)

  ppt (CTStepAN e t)     = "step(" ++ (ppt e) ++ ")" ++ ':':':':(ppt t)

  ppt (CTResumeAN e t)   = "resume(" ++ (ppt e) ++ ")" ++ ':':':':(ppt t)

  ppt (CTResumeReAN e e' t) = "resume(" ++ (ppt e) ++ ")" ++
                              ' ':'(':(ppt e') ++ 
                              ')':':':':':(ppt t)

  ppt (CTLoopAN e t)     = "loop_R (" ++ (ppt e) ++ ")"
                            ++ ':':':':(ppt t)

  ppt (CTBreakAN e t)    = "break" ++ (ppt e) ++ ':':':':(ppt t)

  ppt (CTFixAN lam t)    = "(fix \n" ++ '(':(ppt lam) ++ "))"
                           ++ ':':':':(ppt t)

  ppt (CTSignalAN e t)     = "signal " ++ (ppt e) ++ ':':':':(ppt t)

  ppt (CTGetReqAN e t)     = "getreq " ++ (ppt e) ++ ':':':':(ppt t)

  ppt (CTPrim1aryAN op e t)    = ('(':(ppt op)) ++ "(" ++ (ppt e) ++ "))"
                                 ++ ':':':':(ppt t)

  ppt (CTPrim2aryAN op e e' t) = (ppt e) ++ ' ':(ppt op) ++ ' ':(ppt e')
                                 ++ ':':':':(ppt t)

  ppt (CTPrim3aryAN op e e' e'' t) = ('(':(ppt op))
                                    ++ "(" ++ (ppt e) ++ ")"
                                    ++ "(" ++ (ppt e') ++ ")"
                                    ++ "(" ++ (ppt e'') ++ "))"
                                    ++ ':':':':(ppt t)

  ppt (CTBranchAN b e e' t) = "if " ++ (ppt b) ++ "\nthen " ++ (ppt e) ++
                              "\nelse " ++ (ppt e') ++ ':':':':(ppt t)

  ppt (CTCaseAN e as t) = "case " ++ (ppt e) ++ " of\n" ++
                          (foldr (\(p, e) -> \s -> '\t':(ppt p) ++ " -> "
                                                   ++ (ppt e)
                                                   ++ ('\n':s)) "" as)
                                                   ++ ':':':':(ppt t)

  ppt (CTPairAN e e' t) = '(':(ppt e) ++ " , " ++ (ppt e') ++ ")"
                          ++ ':':':':(ppt t)

  ppt (CTListAN es t)   = '[':(foldr (\x -> \s -> (ppt x) ++ ',':s) "" es)
                          ++ "]" ++ ':':':':(ppt t)

  ppt (CTLitAN l t)     = (ppt l) ++ ':':':':(ppt t)

  ppt (CTVarAN v t)     = v ++ ':':':':(ppt t)
  ppt (CTConAN c vs t)  = c ++ ' ':(foldr (\x -> \s -> (ppt x) ++ ' ':s) "" vs)
                          ++ ':':':':(ppt t)

  ppt (CTUnitAN t)      = "()" ++ ':':':':(ppt t)


--
-- type annotation of an expression:
--
typeofex :: ANAST -> CTTy
typeofex (CTAppAN _ _ t)          = t
typeofex (CTLamAN _ _ t)          = t
typeofex (CTBindAN _ _ t)         = t
typeofex (CTNullBindAN _ _ t)     = t
typeofex (CTReturnAN _ t)         = t
typeofex (CTGetAN _ t)            = t
typeofex (CTPutAN _ _ t)          = t
typeofex (CTStepAN _ t)           = t
typeofex (CTResumeAN _ t)         = t
typeofex (CTResumeReAN _ _ t)     = t
typeofex (CTFixAN _ t)            = t
typeofex (CTSignalAN _ t)         = t
typeofex (CTGetReqAN _ t)         = t
typeofex (CTPrim1aryAN _ _ t)     = t
typeofex (CTPrim2aryAN _ _ _ t)   = t
typeofex (CTPrim3aryAN _ _ _ _ t) = t
typeofex (CTBranchAN _ _ _ t)     = t
typeofex (CTCaseAN _ _ t)         = t
typeofex (CTPairAN _ _ t)         = t
typeofex (CTListAN _ t)           = t
typeofex (CTVarAN _ t)            = t
typeofex (CTConAN _ _ t)          = t
typeofex (CTLitAN _ t)            = t
typeofex (CTUnitAN t)             = t

progToAN :: CTProg -> ANProg
progToAN (CTProg (tysigs, fundecs, datadecs, typedecs, monaddecs)) =
    let
      fundecs'           = promote_main fundecs
      (anMain:anFundecs) = map (fundecToAN tysigs) fundecs'
    in
      ((anMain,anFundecs),(datadecs,monaddecs))

lookupBy :: (Eq b) => (a -> b) -> b -> [a] -> Maybe a
lookupBy f k xs = lookup k (zip (map f xs) xs)

fundecToAN :: [TySig] -> FunDec -> ANFunDec
fundecToAN tysigs (FunDec name argNames body) =
    let
       anBody      = exprToAN body
       (TySig _ t) = case lookupBy (\(TySig n _) -> n) name tysigs of
                        (Just tysig) -> tysig
                        Nothing      -> error $ "Can't find tysig for: " ++ name
    in
       ((name,t),(argNames,anBody))

noType = CTUnitTy

exprToAN :: CTExpr -> ANAST
exprToAN (CTApp e1 e2)                = CTAppAN (exprToAN e1) (exprToAN e2) noType
exprToAN (CTLam x e)                  = CTLamAN x (exprToAN e) noType
exprToAN (CTBind e1 e2)               = CTBindAN (exprToAN e1) (exprToAN e2) noType
exprToAN (CTNullBind e1 e2)           = CTNullBindAN (exprToAN e1) (exprToAN e2) noType
exprToAN (CTReturn e)                 = CTReturnAN (exprToAN e) noType
exprToAN (CTGet x)                    = CTGetAN x noType
exprToAN (CTPut x e)                  = CTPutAN x (exprToAN e) noType
exprToAN (CTRead x e)                 = CTReadAN x (exprToAN e) noType
exprToAN (CTWrite x e1 e2)            = CTWriteAN x (exprToAN e1) (exprToAN e2) noType
exprToAN (CTStepRes e)                = CTStepAN (exprToAN e) noType
exprToAN (CTFix e)                    = CTFixAN (exprToAN e) noType
exprToAN (CTStepReact e)              = CTStepAN (exprToAN e) noType
exprToAN (CTSignal e)                 = CTSignalAN (exprToAN e) noType
exprToAN (CTPrim1ary op e)            = CTPrim1aryAN op (exprToAN e) noType
exprToAN (CTPrim2ary op e1 e2)        = CTPrim2aryAN op (exprToAN e1) (exprToAN e2) noType
exprToAN (CTPrim3ary op e1 e2 e3)     = CTPrim3aryAN op (exprToAN e1) (exprToAN e2) (exprToAN e3) noType
exprToAN (CTBranch (CTGuard g) e1 e2) = CTBranchAN (exprToAN g) (exprToAN e1) (exprToAN e2) noType
exprToAN (CTCase e alts)              = CTCaseAN (exprToAN e) (map (\(p,ex) -> (p,exprToAN ex)) alts) noType
exprToAN (CTPair e1 e2)               = CTPairAN (exprToAN e1) (exprToAN e2) noType
exprToAN (CTList es)                  = CTListAN (map exprToAN es) noType
exprToAN (CTCon ctor es)              = CTConAN ctor (map exprToAN es) noType
exprToAN (CTVar v)                    = CTVarAN v noType
exprToAN (CTLit l)                    = CTLitAN l noType
exprToAN CTUnit                       = CTUnitAN noType
