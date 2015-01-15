--
-- this is ~/cheapthreads/CTC/CT-1.0/RPSLam/Targets/Syntax.hs
--
-- Syntax for a simple imperative target language for the
-- RPS demonstration compiler
--
-- put here (2010.12.13)
--
-- Schulz
--

module Targets.Syntax where

import PPT

import Compile.ReSyntax
import Compile.RSyntax
import Compile.Constants


type Name = String

type Label = String


type TEnv = [(Ref, TVal)]

-- resumption value:
data RCon = RDone | RPause deriving (Show, Eq)
data TRes = TRes RCon TReq Label TVal deriving (Show, Eq)

newtype RER = RER Label deriving (Show, Eq)

data TVal = Nil         -- the value of the uninitialized variables
          | WrongT
          | NumT Int
          | BolT Bool
          | ClT Name Name RER
          | RecClT Name Name RER
          | EnvT TEnv
          | LabelT Label
          | NameT Label
          | ConV String [(String, TVal)]
          | SymConstant String
          | Error String        -- used for debugging the interpreter
          deriving (Show, Eq)

data TReq = TMkCl Name RER
          | TMkRecCl Name RER
          | TApply TExpr TExpr
          | TLkp Name
          deriving (Show, Eq)


data Ref = Var String            -- reference to a scalar variable

         | RR Label              -- reference to a resumption

         | StructFld Ref String  -- reference to a struct field
         | UnionFld Ref String

         -- distinguished registers:
         | R_Req
         | R_Rsp
         | R_Ret
         | R_Nxt
         | R_Done
         | R_Env
         deriving (Show, Eq)

data TExpr = RERX RER          -- reference to a resumption
           | Inc TExpr
           | Dec TExpr

           | And TExpr TExpr
           | Or TExpr TExpr
           | EqTst TExpr TExpr
           | IsNumT TExpr
           | IsBoolT TExpr
           | IsClT TExpr
           | IsRecClT TExpr

           | DeRef Ref
           | TxEnv TExpr TExpr TExpr
           | TopEnv
           | VX TVal
           | ConX String [(String, TExpr)]
           | QCon TReq
           deriving (Show, Eq)


data Stmt = Assign Ref TExpr
          | JSR Ref           -- jump to address in variable and push PC
          | JSRI Label        -- jump to label and push current PC
          | Return            -- pop top of the PC stack and jump to it
          | Jmp Ref           -- unconditional jump
          | JmpI Label        -- immediate-argument unconditional jump
          | BZ TExpr Label    -- branch-on-zero
          | Throw             -- unconditional jump to THE handler
          | Push TExpr        -- push a variable onto the variable stack
          | Pop Ref           -- pop a variable 
          | PushEnv TExpr     -- push an environment
          | PopEnv            -- pop an environment
          | LkpV String
          | Halt TExpr        -- stop execution right here, with this value
          | Nop
          deriving Show


data Code = Labeled Label Code
          | Seq Stmt Code
          | End
          deriving Show

data Act = Act Label Code deriving Show

labelof :: Act -> Label
labelof (Act l _) = l

newtype Prog = Prog [Act]

codecat :: Code -> Code -> Code
codecat (Labeled l s) s'     = Labeled l (codecat s s')
codecat (Seq s s') s''       = Seq s (codecat s' s'')
codecat End s''              = s''


instance PPT Prog where
  ppt (Prog bs) = foldr (\b -> \s -> ppt b ++ '\n':'\n':s) "" bs

instance PPT Act where
  ppt (Act l b) = l ++ ':':((indent . ppt) b)

instance PPT Code where
  ppt (Labeled l s)   = '\n':l ++ ':':'\n':(ppt s)

  ppt (Seq s p)       = (ppt s) ++ ';':'\n':(ppt p)

  ppt End             = "\n"

instance PPT Stmt where
  ppt (Assign r x)  = (ppt r) ++ ' ':':':'=':' ':(ppt x)
  ppt (JSR r)       = "jsr " ++ (ppt r)
  ppt (JSRI r)      = "jsri " ++ r
  ppt Return        = "return"
  ppt (Jmp r)       = "jmp " ++ (ppt r)
  ppt (JmpI l)      = "jmpi " ++ l
  ppt (BZ x l)      = "bz " ++ (ppt x) ++ ' ':l
  ppt Throw         = "throw"
  ppt (Push r)      = "push " ++ (ppt r)
  ppt (Pop r)       = "pop " ++ (ppt r)
  ppt (PushEnv x)   = "pushenv " ++ (ppt x)
  ppt PopEnv        = "popenv"

  ppt (LkpV x)      = "lkp " ++ x
  ppt (Halt x)      = "halt " ++ (ppt x)
  ppt Nop           = "nop"


instance PPT TExpr where
  ppt (Inc x)       = "inc " ++ (ppt x)
  ppt (Dec x)       = "dec " ++ (ppt x)
  ppt (And x x')    = (ppt x) ++ " && " ++ (ppt x')
  ppt (Or x x')     = (ppt x) ++ " || " ++ (ppt x')
  ppt (EqTst x x')  = (ppt x) ++ " == " ++ (ppt x')
  ppt (IsNumT x)    = "isnum " ++ (ppt x)
  ppt (IsBoolT x)   = "isbool " ++ (ppt x)
  ppt (IsClT x)     = "iscl " ++ (ppt x)
  ppt (IsRecClT x)  = "isreccl " ++ (ppt x)
  ppt (TxEnv h x v) = "(xEnv " ++ (ppt h) ++ ' ':(ppt x) ++ ' ':(ppt v) ++ ")"
  ppt TopEnv        = "topenv"
  ppt (DeRef r)     = ppt r
  ppt (VX v)        = ppt v

  ppt (ConX c ((_,v):vs)) = c ++ '<':(ppt v) ++
                          (foldr (\(_, v) -> \s -> ',':(ppt v) ++ s) "" vs)
                          ++ ">"

  ppt (ConX c [])     = c

  ppt (QCon q)          = ppt q


instance PPT Ref where
  ppt (Var x) = x
  ppt (RR r)  = r
  ppt R_Req   = "r_req"
  ppt R_Rsp   = "r_rsp"
  ppt R_Ret   = "r_ret"
  ppt R_Nxt   = "r_nxt"
  ppt R_Env   = "r_env"
  ppt R_Done  = "r_done"

  ppt (StructFld r x)  = (ppt r) ++ '.':x
  ppt (UnionFld r x)   = (ppt r) ++ '.':x


instance PPT RCon where
  ppt RPause = "P"
  ppt RDone  = "D"

instance PPT TRes where
  ppt (TRes c q l v) = (ppt c) ++ '<':(ppt q) ++ ',':l ++ (ppt v) ++ ">"

instance PPT RER where
  ppt (RER l) = l

instance PPT TVal where
  ppt WrongT          = "WRONG"
  ppt Nil             = "<uninitialized>"
  ppt (NumT n)        = show n
  ppt (BolT False)    = "FALSE"
  ppt (BolT True)     = "TRUE"
  ppt (ClT x e p)     = "<closure: " ++ x ++ ';':(ppt p) ++ ">"
  ppt (RecClT x e p)  = "<recclosure: " ++ x ++ ';':(ppt p) ++ ">"
  ppt (ConV x as)     = x ++ '<':
                        (foldr (\(_,v) -> \s -> ppt v ++ ',':s) "" as)
                        ++ ">"

  ppt (EnvT _)        = "<ENV>"

  ppt (LabelT l)      = l
  ppt (NameT l)       = l

  ppt (SymConstant x) = x

  ppt (Error x)       = "error: " ++ x


instance PPT TReq where
  ppt (TMkCl x l)    = "MkCl <" ++ x ++ ',':(ppt l) ++ ">"
  ppt (TMkRecCl x l) = "MkRecCl <" ++ x ++ ',':(ppt l) ++ ">"
  ppt (TApply v v')  = "Apply <" ++ (ppt v) ++ ',':(ppt v') ++ ">"
  ppt (TLkp x)       = "Lkp " ++ x

-- THIS IS THE END OF THE FILE --
