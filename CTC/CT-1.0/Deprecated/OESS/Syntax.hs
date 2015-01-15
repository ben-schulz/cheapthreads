--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/OESS/Syntax.hs
--
-- The OESS intermediate representation abstract syntax;
--
-- An execution-stream specification syntax,
-- layered over a simple C-like syntax;
--
-- Maintaining the K-T boundary!
--
-- put here 2010.06.23
--
-- Schulz
-- 

module Deprecated.OESS.Syntax where

import CT.PPT


type Label = String

--
-- output of this phase is organized in labeled blocks of code
-- which may reference one another:
--
data Block = StrmBlock Label Stream
           | ThrdBlock Label TCode
           | ImprBlock Label STCode
           | ExprBlock Label Expr

bl_label :: Block -> Label
bl_label (StrmBlock l _) = l
bl_label (ThrdBlock l _) = l
bl_label (ImprBlock l _) = l
bl_label (ExprBlock l _) = l

--
-- at its top level an OESS program is an execution stream of atomic actions:
--
data Stream = FBy KAct Stream             -- simple sequencing
            | SBZ Stream Stream Stream    -- convergent branch sequencing
            | SJSR Label Stream           -- jump to subroutine
            | Loop Stream Stream          -- sequenced loop
            | Halt                        -- done
            deriving Show



--
-- an action from the global perspective;
-- continue executing some part of a stored program,
-- or interrupt the stream, switching context to a (user) thread:
--
data KAct = Atom STCode     -- run stored code
          | KCreate KThread -- create a kernel thread
          | TCreate UThread -- create a new user thread
          | Kill TID        -- kill a thread, remove from pool
          | Catch TID       -- catch a system call
          | SwitchA TID     -- unconditional context-switch 
          | SwitchZ TID     -- switch-on-zero
          | Break           -- break out of current top-level loop
          deriving Show

--
-- a kernel thread, which may be referenced mid-execution stream:
--
data KThread = KThread TID Label deriving Show



--
-- a user thread:
--
data UThread = UThread TID Label deriving Show

data TCode = TSeq TAct TCode        -- act sequencing in a thread
           | TLoop TCode TCode      -- loop in the user thread
           | TBZ TCode TCode TCode  -- branch-on-zero in user thread
           | TJSR Label TCode       -- break in the user thread
           | TBreak                 -- break in the user thread
           | TDone                  -- exit thread with return value in 'R_Ret'
           deriving Show


--
-- a thread-unique ID:
--
type TID = Expr


--
-- an action from a thread-local perspective;
-- continue executing a stored program, or make a system call:
--
data TAct = Cont STCode   -- run stored program
          | Throw Expr    -- system call
          deriving Show


--
-- stored imperative code:
--
data STCode = Seq Stmt STCode           -- simple sequencing
            | BZ STCode STCode STCode   -- 'diamond' sequencing
            | JSR Label STCode          -- jump to subroutine, and back
            | Stmt Stmt                 -- single statement
            deriving Show

--
-- labeled 'basic block' of imperative code:
--
data STBlock = STBlock STCode Label deriving Show

labelof :: STBlock -> Label
labelof (STBlock _ l) = l

codeof :: STBlock -> STCode
codeof (STBlock p _) = p

--
-- an imperative statement:
--
data Stmt = Assign Ref Expr  -- imperative assignment
          | TestZ Expr       -- set 'zero' bit
          | NOP              -- 'skip'
          deriving Show

--
-- a mutable reference, which may be a scalar variable or an array element:
--
data Ref = Var String         -- a variable
         | Array String Expr  -- an array element

         | R_Ret              -- a distinguished register for monadic return
         | R_PC               -- program counter of the running thread
         | R_Sig              -- a distinguished virtual register for signals
         | R_TCT              -- counter for generating thread ids
         
         deriving Show

--
-- an expression, involving only primitive operators:
--
data Expr = DeRef Ref      -- variable dereference

          | LabelRef Label -- reference to a label in the stored code

          -- arithmetic:
          | Neg Expr       -- arithmetic negation
          | Add Expr Expr  -- addition
          | Sub Expr Expr  -- subtraction
          | Mul Expr Expr  -- multiplication
          | Div Expr Expr  -- integer division

          -- logic:
          | Not Expr       -- logical negation
          | And Expr Expr  -- conjunction
          | Or Expr Expr   -- disjunction

          -- literals:
          | SInt Int       -- integer literal
          | SBool Bool     -- boolean literal
          | Clear          -- the unit-element equivalent

          deriving Show



--
-- formatted output for the OESS syntax:
--

instance PPT Stream where
  ppt (FBy k s)      = (ppt k) ++ "; " ++ (ppt s)

  ppt (SBZ s s' s'') = "ifzero{\n " ++ (ppt s) ++ "}\n" ++
                       "else {\n"  ++ (ppt s') ++ "}\n" ++ (ppt s'')

  ppt (SJSR l s)     = "jsr " ++ l ++ ';':(ppt s)

  ppt (Loop s s')    = "loop {\n" ++ (ppt s) ++ "}\n" ++ (ppt s')

  ppt Halt           = "halt"


instance PPT KAct where
  ppt (Atom k)    = "atom {\n" ++ (ppt k) ++ "}"

  ppt (KCreate t) = "kthread_create " ++ (ppt t)

  ppt (TCreate u) = "kthread_create" ++ (ppt u)

  ppt (Kill t)    = "kill(" ++ (ppt t) ++ ")"

  ppt (Catch t)   = "catch(" ++ (ppt t) ++ ")"

  ppt (SwitchA t) = "switch_a(" ++ (ppt t) ++ ")"

  ppt (SwitchZ t) = "switch_z(" ++ (ppt t) ++ ")"

  ppt Break       = "break"


instance PPT KThread where
  ppt (KThread t l) = '(':(ppt t) ++ ", " ++ l ++ ")"


instance PPT UThread where
  ppt (UThread t l) = '(':(ppt t) ++ ", " ++ l ++ ")"


instance PPT TCode where
  ppt (TSeq t t')    = (ppt t) ++ ';':(ppt t')

  ppt (TLoop t t')   = "loop {\n" ++ (ppt t') ++ "}\n"

  ppt (TBZ s s' s'') = "ifzero{\n " ++ (ppt s) ++ "}\n" ++
                       "else {\n"  ++ (ppt s') ++ "}\n" ++ (ppt s'')

  ppt (TJSR l t)     = "jsr " ++ l ++ ';':(ppt t)

  ppt TBreak         = "break"
  ppt TDone          = "exit"


instance PPT TAct where
  ppt (Cont s)  = "atom{\n" ++ (ppt s) ++ "}"
  ppt (Throw e) = "throw(" ++ (ppt e) ++ ")"


instance PPT STCode where
  ppt (Seq s s')    = (ppt s) ++ ';':(ppt s')

  ppt (BZ s s' s'') = "ifzero {\n" ++ (ppt s) ++ "}\n" ++
                      "else {\n" ++ (ppt s') ++ "}\n" ++ (ppt s'')

  ppt (JSR l s)     = "jsr " ++ l ++ ';':(ppt s)

  ppt (Stmt s)      = ppt s


instance PPT Stmt where
  ppt (Assign r e) = (ppt r) ++ " := " ++ (ppt e)
  ppt (TestZ e)    = "test(" ++ (ppt e) ++ ")"
  ppt NOP          = "nop"


instance PPT Ref where
  ppt (Var x)     = x
  ppt (Array x i) = x ++ '[':(ppt i) ++ "]"

  ppt R_Ret       = "r_ret"
  ppt R_PC        = "r_pc"
  ppt R_Sig       = "r_signal"
  ppt R_TCT       = "r_tidct"


instance PPT Expr where
  ppt (DeRef r)    = ppt r
  ppt (LabelRef l) = l

  ppt (Neg e)      = "-(" ++ (ppt e) ++ ")"
  ppt (Add e e')   = (ppt e) ++ " + " ++ (ppt e')
  ppt (Sub e e')   = (ppt e) ++ " - " ++ (ppt e')
  ppt (Mul e e')   = (ppt e) ++ " * " ++ (ppt e')
  ppt (Div e e')   = (ppt e) ++ " / " ++ (ppt e')

  ppt (Not e)      = "!(" ++ (ppt e) ++ ")"
  ppt (And e e')   = (ppt e) ++ " && " ++ (ppt e')
  ppt (Or e e')    = (ppt e) ++ " || " ++ (ppt e')

  ppt (SInt n)     = show n
  ppt (SBool b)    = show b
  ppt Clear        = "void"

-- THIS IS THE END OF THE FILE --
