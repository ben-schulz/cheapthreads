--
-- this is ~/cheapthreads/ctc_working/CT-1.0/CT/INAST.hs
--
-- the intermediate representation first used in the inliner,
-- and used in all subsequent modules
--
-- moved here from inside of ./Inliner.hs
--
-- 2010.02.15
--
-- Schulz
--

module CT.INAST where

import CT.Syntax
import CT.ANAST
import CT.PPT

--
-- we introduce another intermediate representation
-- so that 'fix' no longer looks like a regular lambda
-- application, which is really not the sense in which
-- it is being used;
--
-- the only difference between this new AST and the
-- preceding one ('INAST') is that 'CTFix' is folded
-- into a structure including a list of initial arguments
-- corresponding to the arguments of an application
--
--


--
-- analogous to 'ANFunDec':
--
newtype INFunDec = INFunDec ((CTIdent, CTTy), ([CTIdent], INAST))
                   deriving Show

--
-- as in ANProg, first component is 'main'; second
-- is a list of all other declared functions
--
newtype INProg = INProg ((INFunDec, [INFunDec]), ([DataDec], [MonadDec]))
                 deriving Show

--
-- conversion between the two:
--

toinprog :: ANProg -> INProg
toinprog ((d, ds), (dats, mons)) =

   let (mn:fs) = map
                   (\((x, y), (z, w)) ->
                     (INFunDec ((x, y), (z, toinast w))))
                       (d:ds)
   in
     INProg ((mn, fs), (dats, mons))
                        


--
-- some useful accessors:
--

--
-- get a list of declared function names:
--
funnames :: INProg -> [CTIdent]
funnames (INProg ((mn, fs), (_, _))) =

  foldr
    (\(INFunDec ((f, _), (_, _))) -> \xs -> f:xs)
      [] (mn:fs)



data INAST = CTAppIN INAST INAST AN
           | CTRecAppIN INAST INAST AN    -- tail-call in scope of a 'fix'
           | CTFixAppIN INAST [INAST] AN  -- application of loop
           | CTLamIN CTIdent INAST AN

           -- monadic expressions:
           | CTBindIN INAST INAST AN
           | CTNullBindIN INAST INAST AN
           | CTReturnIN INAST AN

           -- stateful operators:
           | CTGetIN CTIdent AN
           | CTPutIN CTIdent INAST AN
           | CTPopIN CTIdent AN
           | CTPushIN CTIdent INAST AN
           | CTReadIN CTIdent INAST AN
           | CTWriteIN CTIdent INAST INAST AN

           -- resumptive operators:
           | CTStepIN INAST AN
           | CTResumeIN INAST AN
           | CTResumeReIN INAST INAST AN

           | CTLoopIN INAST AN
           | CTLoopAppIN INAST [INAST] AN
           | CTBreakIN INAST AN

           | CTFixIN INAST AN

           -- reactive-resumptive operators:
           | CTSignalIN INAST AN
           | CTGetReqIN INAST AN

           -- primitive operations:
           | CTPrim1aryIN CTPrimOp INAST AN
           | CTPrim2aryIN CTPrimOp INAST INAST AN
           | CTPrim3aryIN CTPrimOp INAST INAST INAST AN

           -- control flow:
           | CTBranchIN INAST INAST INAST AN
           | CTCaseIN INAST [(CTPat, INAST)] AN

           -- tuples:
           | CTPairIN INAST INAST AN
           | CTListIN [INAST] AN

           -- variables:
           | CTVarIN CTIdent AN
           | CTConIN CTIdent [INAST] AN

           -- literals:
           | CTLitIN Literal AN
           | CTUnitIN AN
           deriving Show

instance PPT INProg where
  ppt (INProg ((mn, fs), (mons, dats))) = (ppt mn) ++ '\n':'\n':
                                          (
                                            foldr
                                            (\x -> \s -> (ppt x) ++ '\n':'\n':s)
                                              "" fs
                                          )

instance PPT INFunDec where
  ppt (INFunDec ((f, t), (xs, e))) = f ++ " :: " ++ (ppt t) ++
                                     '\n':f ++
                                     ' ':(foldr (\x -> \s -> x ++ ' ':s) "" xs)
                                     ++ " =\n" ++
                                     (ppt e) ++ "\n"


instance PPT INAST where

  ppt (CTAppIN e e' t)      = '(':(ppt e) ++ ' ':(ppt e') ++
                              ':':':':(ppt t) ++ ")"

  ppt (CTRecAppIN e e' t)   = '(':(ppt e) ++ ' ':(ppt e') ++
                              ':':':':(ppt t) ++ ")"

  ppt (CTFixAppIN e is t)   = (ppt e)
                              ++ (foldr (\x -> \s -> (ppt x) ++ ' ':s) "" is)
                              ++ ':':':':(ppt t)


  ppt (CTLamIN x e t)       = '(':"\\" ++ x ++ " ->\n" ++ (ppt e)
                              ++ ':':':':(ppt t) ++ ")"

  ppt (CTBindIN e lam t)    = '(':(ppt e) ++ " >>= " ++ (ppt lam)
                               ++ ':':':':(ppt t) ++ ")"

  ppt (CTNullBindIN e e' t)  = '(':(ppt e) ++ " >>\n" ++ (ppt e')
                               ++ ':':':':(ppt t) ++ ")"

  ppt (CTReturnIN e t)       = '(':"return (" ++ (ppt e) ++ ")"
                               ++ ':':':':(ppt t) ++ ")"

  ppt (CTGetIN x t)   = '(':"get " ++ x ++ ':':':':(ppt t) ++ ")"
  ppt (CTPutIN x e t) = '(':"put " ++ x ++ " (" ++ (ppt e) ++ ")"
                        ++ ':':':':(ppt t) ++ ")"

  ppt (CTPopIN x t)    = '(':"pop " ++ x ++ ':':':':(ppt t) ++ ")"
  ppt (CTPushIN x e t) = '(':"push " ++ x ++ " (" ++ (ppt e) ++ ")"
                         ++ ':':':':(ppt t) ++ ")"

  ppt (CTReadIN x i t)   = '(':"get " ++ x ++ '[':(ppt i) ++ "]"
                           ++ ':':':':(ppt t)

  ppt (CTWriteIN x i e t) = '(':"put " ++ x ++ '[':(ppt i) ++ "]"
                            ++ (ppt e) ++ ':':':':(ppt t)

  ppt (CTStepIN e t)    = '(':"step(" ++ (ppt e) ++ ")" ++ ':':':':(ppt t)
                          ++ ")"

  ppt (CTResumeIN e t)  = '(':"resume_R(" ++ (ppt e) ++ ")" ++ ':':':':(ppt t)
                          ++ ")"

  ppt (CTResumeReIN e e' t)  = '(':"resume_Re(" ++ (ppt e) ++ ")" ++
                               ' ':'(':(ppt e') ++
                               ')':':':':':(ppt t)
                               ++ ")"

  ppt (CTLoopIN e t)    = "loop_R (" ++ (ppt e) ++ ")" ++ ':':':':(ppt t)

  ppt (CTLoopAppIN e e' t) = '(':(ppt e) ++ ") "
                             ++ (foldr (\s -> \ss -> (ppt s) ++ ' ':ss) "" e')
                             ++ ':':':':(ppt t)

  ppt (CTBreakIN e t)   = "break" ++ (ppt e) ++ ':':':':(ppt t)

  ppt (CTFixIN lam t)   = "(fix \n" ++ '(':(ppt lam) ++ ") "
                          ++ ")"
                          ++ ':':':':(ppt t)

{-
  ppt (CTFixIN lam as t)   = "(fix \n" ++ '(':(ppt lam) ++ ") "
                             ++ (foldr (\x -> \s -> (ppt x) ++ ' ':s) "" as)
                             ++ ")"
                             ++ ':':':':(ppt t)
-}

  ppt (CTSignalIN e t)     = '(':"signal " ++ (ppt e) ++ ':':':':(ppt t) ++ ")"

  ppt (CTGetReqIN e t)     = '(':"getreq " ++ (ppt e) ++ ':':':':(ppt t) ++ ")"

  ppt (CTPrim1aryIN op e t)    = '(':('(':(ppt op)) ++ "(" ++ (ppt e) ++ "))"
                                 ++ ':':':':(ppt t) ++ ")"

  ppt (CTPrim2aryIN op e e' t) = '(':(ppt e) ++ ' ':(ppt op) ++ ' ':(ppt e')
                                 ++ ':':':':(ppt t) ++ ")"

  ppt (CTPrim3aryIN op e e' e'' t) = '(':('(':(ppt op))
                                     ++ "(" ++ (ppt e) ++ ")"
                                     ++ "(" ++ (ppt e') ++ ")"
                                     ++ "(" ++ (ppt e'') ++ "))"
                                     ++ ':':':':(ppt t) ++ ")"

  ppt (CTBranchIN b e e' t) = '(':"if " ++ (ppt b) ++ "\nthen " ++ (ppt e) ++
                              "\nelse " ++ (ppt e') ++ ':':':':(ppt t) ++ ")"

  ppt (CTCaseIN e as t) = '(':"case " ++ (ppt e) ++ " of\n" ++
                          (foldr (\(p, e) -> \s -> '\t':(ppt p) ++ " -> "
                                                   ++ (ppt e)
                                                   ++ ('\n':s)) "" as)

                          ++ ':':':':(ppt t) ++ ")\n\n"

  ppt (CTPairIN e e' t) = '(':'(':(ppt e) ++ " , " ++ (ppt e') ++ ")"
                          ++ ':':':':(ppt t) ++ ")"

  ppt (CTListIN es t)   = '(':'[':(foldr (\x -> \s -> (ppt x) ++ ',':s) "" es)
                          ++ "]" ++ ':':':':(ppt t) ++ ")"

  ppt (CTLitIN l t)     = '(':(ppt l) ++ ':':':':(ppt t) ++ ")"

  ppt (CTVarIN v t)     = '(':v ++ ':':':':(ppt t) ++ ")"
  ppt (CTConIN c vs t)  = '(':c
                          ++ ' ':(foldr (\x -> \s -> (ppt x) ++ ' ':s) "" vs)
                          ++ ':':':':(ppt t) ++ ")"

  ppt (CTUnitIN t)      = '(':"()" ++ ':':':':(ppt t) ++ ")"


--
-- convert between the above and 'ANAST':
--
-- this is a trivial conversion;
-- the important stuff happens in 'beta_rx'
--
toinast :: ANAST -> INAST
toinast (CTAppAN (CTLoopAN a t) a' t') = let f = CTLoopIN (toinast a) t
                                             b = toinast a'
                                         in
                                           CTLoopAppIN f [b] t'

toinast (CTAppAN (CTFixAN a t) a' t') = let f = CTFixIN (toinast a) t
                                            b = toinast a'
                                        in
                                          CTFixAppIN f [b] t'


toinast (CTAppAN a a' t)  =  let b' = toinast a'
                             in
                             case (toinast a) of

                               (CTLoopAppIN b bs _) -> CTLoopAppIN b
                                                         (bs ++ [b']) t


                               (CTFixAppIN b bs _)  -> CTFixAppIN b
                                                         (bs ++ [b']) t

                               b                    -> CTAppIN b b' t

toinast (CTLamAN x a t)   = CTLamIN x (toinast a) t

toinast (CTBindAN a a' t)     = CTBindIN (toinast a) (toinast a') t
toinast (CTNullBindAN a a' t) = CTNullBindIN (toinast a) (toinast a') t
toinast (CTReturnAN a t)      = CTReturnIN (toinast a) t

toinast (CTGetAN x t)   = CTGetIN x t
toinast (CTPutAN x a t) = CTPutIN x (toinast a) t

toinast (CTPopAN x t)    = CTPopIN x t
toinast (CTPushAN x a t) = CTPushIN x (toinast a) t

toinast (CTReadAN x i t)    = CTReadIN x (toinast i) t
toinast (CTWriteAN x i e t) = CTWriteIN x (toinast i) (toinast e) t

toinast (CTStepAN a t)        = CTStepIN (toinast a) t
toinast (CTResumeAN a t)      = CTResumeIN (toinast a) t
toinast (CTResumeReAN a a' t) = CTResumeReIN (toinast a) (toinast a') t
toinast (CTLoopAN a t)        = CTLoopIN (toinast a) t
toinast (CTBreakAN a t)       = CTBreakIN (toinast a) t
toinast (CTFixAN a t)         = CTFixIN (toinast a) t

toinast (CTSignalAN a t) = CTSignalIN (toinast a) t
toinast (CTGetReqAN a t) = CTGetReqIN (toinast a) t

toinast (CTPrim1aryAN op a t)    = CTPrim1aryIN op (toinast a) t
toinast (CTPrim2aryAN op a a' t) = CTPrim2aryIN op (toinast a) (toinast a') t
toinast (CTPrim3aryAN op a a' a'' t) = CTPrim3aryIN op (toinast a)
                                                   (toinast a')
                                                   (toinast a'') t

toinast (CTBranchAN g a a' t) = CTBranchIN (toinast g)
                                           (toinast a) (toinast a') t

toinast (CTCaseAN a as t) = CTCaseIN (toinast a)
                                     (map (\(x, y) -> (x, toinast y)) as) t

toinast (CTPairAN a a' t) = CTPairIN (toinast a) (toinast a') t
toinast (CTListAN as t)   = CTListIN (map toinast as) t

toinast (CTVarAN x t)    = CTVarIN x t
toinast (CTConAN x as t) = CTConIN x (map toinast as) t

toinast (CTLitAN l t) = CTLitIN l t
toinast (CTUnitAN t)  = CTUnitIN t


--
-- type annotation of an expression:
--
typeofinast :: INAST -> CTTy
typeofinast (CTAppIN _ _ t)        = t
typeofinast (CTRecAppIN _ _ t)     = t
typeofinast (CTFixAppIN _ _ t)     = t
typeofinast (CTLamIN _ _ t)        = t
typeofinast (CTBindIN _ _ t)       = t
typeofinast (CTNullBindIN _ _ t)   = t
typeofinast (CTReturnIN _ t)       = t
typeofinast (CTGetIN _ t)          = t
typeofinast (CTPutIN _ _ t)        = t
typeofinast (CTPopIN _ t)          = t
typeofinast (CTPushIN _ _ t)       = t
typeofinast (CTReadIN _ _ t)       = t
typeofinast (CTWriteIN _ _ _ t)    = t
typeofinast (CTStepIN _ t)         = t
typeofinast (CTResumeIN _ t)       = t
typeofinast (CTResumeReIN _ _ t)   = t
typeofinast (CTLoopIN _ t)         = t
typeofinast (CTLoopAppIN _ _ t)    = t
typeofinast (CTFixIN _ t)          = t
typeofinast (CTSignalIN _ t)       = t
typeofinast (CTGetReqIN _ t)       = t
typeofinast (CTPrim1aryIN _ _ t)   = t
typeofinast (CTPrim2aryIN _ _ _ t) = t
typeofinast (CTBranchIN _ _ _ t)   = t
typeofinast (CTCaseIN _ _ t)       = t
typeofinast (CTPairIN _ _ t)       = t
typeofinast (CTListIN _ t)         = t
typeofinast (CTVarIN _ t)          = t
typeofinast (CTConIN _ _ t)        = t
typeofinast (CTLitIN _ t)          = t
typeofinast (CTUnitIN t)           = t


--
-- a simple accessors for lambdas and fixpoints:
--

--
-- get the first parameter:
--
lampof :: INAST -> String
lampof (CTLamIN x _ _) = x

--
-- drop the first parameter:
--
lampsnd :: INAST -> INAST
lampsnd (CTLamIN _ e _) = e

--
-- get the body following a succession of parameters:
--
lambof :: INAST -> INAST
lambof (CTLamIN _ e _) = lambof e
lambof b               = b

--
-- get a sequence of parameters from contiguous-nested lambdas:
--
lampsof :: INAST -> [String]
lampsof (CTLamIN x e _) = x:(lampsof e)
lampsof _               = []

--
-- unfold an series of applications into a list:
--
unfoldapp :: INAST -> [INAST]
unfoldapp (CTAppIN a a' _)    = (unfoldapp a) ++ [a']
unfoldapp (CTRecAppIN a a' _) = (unfoldapp a) ++ [a']
unfoldapp x                   = [x]

--
-- extract the string from a variable:
--
nameofvar :: INAST -> String
nameofvar (CTVarIN x _) = x
nameofvar y = error $ "\nunexpected case in: CT.DFun.INAST.nameofvar:\n" ++
                      (show y) ++ "\n\n"

-- THIS IS THE END OF THE FILE --
