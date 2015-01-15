--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Compile/Syntax.hs
--
-- Simplified abstract syntax for the reactive terms produced by the RPS
-- transformation interpreter, i.e. Interpreters.InterpRe.interp
--
-- put here (2010.12.14)
--
-- Schulz
--

module Compile.ReSyntax where

import PPT

import PCF.Syntax

--
-- environment expressions;
--
-- environment is always accessed implicitly
-- through 'rdEnv' and 'inEnv'; new environment
-- are only constructed using 'xEnv'
--
--
{-
data Env = ENV Name
         | XEnv Env Name RVal 
         deriving (Show, Eq)
-}

type Env = Name

data RVal = Wrong
          | Num Int
          | Bol Bool
          | Cl Name Name TermRe
          | RecCl Name Name TermRe
--          | Cl Name Env TermRe
--          | RecCl Name Env TermRe
          deriving (Show, Eq)

data RExpr = IncX RExpr
           | DecX RExpr

           | EqTest RExpr RExpr
           | IsNum RExpr
           | IsBool RExpr
           | IsCl RExpr
           | IsRecCl RExpr

           | Lit RVal
           | Ref Name
           deriving (Show, Eq)

data Req = MkCl Name TermRe
         | MkRecCl Name TermRe
         | Apply RExpr RExpr
         | Lkp Name
         deriving (Show, Eq)


data TermRe = Bind Name TermRe TermRe
            | BindNull TermRe TermRe
            | Signal Req
            | Eta RExpr
            | ITE RExpr TermRe TermRe
            | RVar Name
            deriving (Show, Eq)


isBind :: TermRe -> Bool
isBind (Bind _ _ _)   = True
isBind (BindNull _ _) = True
isBind _              = False


data TermR = RBind Name TermR TermR
           | RBindNull TermR TermR
           | RetWith RVal
           | REta RVal
           | RITE HExpr TermR TermR
           | RCase HExpr Alts
           | RLet Name HExpr TermR



data HExpr = ReqOf HExpr
           | CodeOf HExpr
           | IsDone HExpr
           | HRef Name
           | RX RExpr

data Alts = None
          | Pat TermR Alts

data Pat = PCon [Pat]
         | PVar Name
         | PP Pat         -- reactive pause pattern
         | PD Pat         -- reactive 'done' pattern


instance PPT TermRe where
  ppt (Bind x r r')     = (ppt r) ++ " >>= \\" ++ x ++ "->\n" ++ (ppt r')
  ppt (BindNull  r r')  = (ppt r) ++ " >>\n" ++ (ppt r')
  ppt (Signal q)        = "signal " ++ (ppt q)
  ppt (Eta x)           = "return " ++ (ppt x)

  ppt (ITE x r r')      = "if " ++ (ppt x) ++ " then " ++ (indent (ppt r))
                          ++ " else " ++ (indent (ppt r'))


instance PPT RExpr where
  ppt (IncX r)      = "inc " ++ (ppt r)
  ppt (DecX r)      = "dec " ++ (ppt r)

  ppt (EqTest r r') = (ppt r) ++ " == " ++ (ppt r')
  ppt (IsNum r)     = "isnum " ++ (ppt r)
  ppt (IsBool r)    = "isbool " ++ (ppt r)
  ppt (IsCl r)      = "iscl " ++ (ppt r)
  ppt (IsRecCl r)   = "isreccl " ++ (ppt r)

  ppt (Lit v)       = ppt v
  ppt (Ref x)       = x


instance PPT RVal where
  ppt Wrong         = "WRONG"
  ppt (Num n)       = show n
  ppt (Bol False)   = "FALSE"
  ppt (Bol True)    = "TRUE"
  ppt (Cl x _ _)    = "<closure " ++ x ++ ">"
  ppt (RecCl x _ _) = "<recclosure " ++ x ++ ">"


instance PPT Req where
  ppt (MkCl x r)    = "MKCL <" ++ x ++ ',':(ppt r) ++ ">"
  ppt (MkRecCl x r) = "MKRECCL <" ++ x ++ ',':(ppt r) ++ ">"
  ppt (Apply v v')  = "APPLY <" ++ (ppt v) ++ ',':(ppt v') ++ ">"
  ppt (Lkp x)       = "LKP " ++ x


-- THIS IS THE END OF THE FILE --
