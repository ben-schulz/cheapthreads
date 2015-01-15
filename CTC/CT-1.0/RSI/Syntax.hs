--
-- this is ~/cheapthreads/CTC/CT-1.0/RSI/Syntax.hs
--
-- Syntax definitions for the RSI intermediate form
--
-- put here 2010.08.16
--
-- Schulz
--

module RSI.Syntax where

import CT.PPT
import CT.Syntax

import Data.Char

type Label = String

class Addressable a where
{
  startof :: a -> Label
}


--
-- an RSI program consists of a collection of labeled blocks, chains,
-- and an entry point for execution:
--
data Code = R Label Chain | K Label Block deriving Show
type CodeSect = [Code]
type DataSect = [DDec]
newtype RSI = RSI (DataSect, (Label, CodeSect)) deriving Show

instance PPT RSI where
  ppt (RSI (ds, (l, cs))) = data_sect_header ++ '\n':'\n':
                            (foldr (\d -> \s -> (ppt d) ++ '\n':s) "\n\n" ds) ++
                            code_sect_header ++ '\n':
                            init_label ++ ':':(ppt (init_code))
                            ++ '\n':'\t':"jmp " ++ l ++ '\n':'\n':
                            (foldr (\c -> \s -> (ppt c) ++ '\n':s) "" cs)

instance Addressable Code where
  startof (R l _) = l
  startof (K l _) = l

instance PPT Code where
  ppt (R l r) = if (l /= startof r)
                then
                  '\n':'\n':l ++ ':':'\n':(ppt r) ++ '\n':'\t':"done"
                else
                  '\n':'\n':(ppt r) ++ '\n':'\t':"done"

  ppt (K l k) = if (l /= startof k)
                then
                  '\n':'\n':l ++ ':':'\n':(ppt k) ++
                  '\n':'\t':"jmp " ++ (rtsreg l)
                else
                  '\n':'\n':(ppt k) ++
                  '\n':'\t':"jmp " ++ (rtsreg l)



--
-- basic unit of RSI is a labeled block
-- of imperative code; exit point of the code block
-- is determined by situating the block within
-- a 'Chain' of such blocks, i.e. a resumption
--
-- first label: entry point
-- second arg: imperative code
--
data Block = Block Label ASM deriving Show

--
-- labeling convention for blocks exit points:
--
rtsreg ('_':'_':l) = (map toLower l) ++ "__back"
rtsreg l           = (map toLower l) ++ "__back"


instance Addressable Block where
  startof (Block l _ ) = l

instance PPT Block where
  ppt (Block l p) = l ++ ':':'\n':(ppt p)


--
-- a labeled block of code to be executed under presumption of atomicity:
--
-- first arg: location label
-- second arg: code to atomically execute
--
data Atom = Atom Label ASM
          | Throw Label ASM
          deriving Show

codeof :: Atom -> ASM
codeof (Atom _ k)  = k
codeof (Throw _ k) = k

instance Addressable Atom where
  startof (Atom l _) = l
  startof (Throw l _) = l

instance PPT Atom where
  ppt (Atom l p)  = l ++ ':':'\n':(
                    indent
                      ("\natom{\n" ++ (ppt p) ++ "\n};"))
  ppt (Throw l p) = l ++ ':':'\n':(
                    indent
                      ("\nthrow{\n" ++ (ppt p) ++ "\n};"))



--
-- programs consist of blocks chained by a network of explicit jumps:
--
data Chain = Seq Atom Chain                    -- simple sequencing, i.e. bind
           | BZ_R Label Expr Chain Chain Chain -- diamond branching
           | Loop Label Chain Chain            -- tail recursion
           | Break Label Expr                  -- loop termination
           | Swr Label Ref Chain               -- resumption switching
           | Swt Label Ref Chain               -- reactive resumption switching
           | Catch Label Ref Chain             -- application of the Re body
           | Jmp Label Ref Chain               -- indirect execution
           | LabelPt Label Chain               -- label synonym
           | Halt Label                        -- done
           deriving Show

instance Addressable Chain where
  startof (Seq a _)           = startof a
  startof (BZ_R l _ _ _ _)    = l
  startof (Loop l _ _)        = l
  startof (Break l _)         = l
  startof (Swr l _ _)         = l
  startof (Swt l _ _)         = l
  startof (Catch l _ _)       = l
  startof (Jmp l _ _)         = l
  startof (LabelPt l _)       = l
  startof (Halt l)            = l


instance PPT Chain where
  ppt (Seq b c)         = (ppt b ++ '\n':(ppt c))

  ppt (BZ_R l x c c' c'') = l ++ ':':'\n':
                            '\t':"bzr " ++ (ppt x) ++

                            (

                            indent $

                            '\n':'{':'\n':'\t':"NOT_ZERO" ++ '{':
                               (indent ('\n':(ppt c) ++
                                 "\njmp " ++ (startof c'') ++ "\n}")) ++
                            '\n':'\n':'\t':"ZERO"++ '{':
                               (indent ('\n':(ppt c') ++
                                 "\njmp " ++ (startof c'') ++ "\n}"))

                            ) ++

                            '\n':'\t':'}':';':'\n':(ppt c'')


  ppt (Loop l c c')       = l ++ ':':'\n':
                            (ppt c) ++
                            '\n':'\t':"jmp " ++ l ++
                            '\n':(ppt c')

  ppt (Break l v)         = let ret = Assign R_Ret v
                            in
                              (ppt ret) ++
                              '\t':"jmp " ++ l

  ppt (Swr l r c)         = l ++ ':':'\n':
                            '\t':"swr " ++ (ppt r) ++
                            ';':'\n':(ppt c)

  ppt (Swt l r c)         = l ++ ':':'\n':
                            '\t':"swt " ++ (ppt r) ++
                            ';':'\n':(ppt c)

  ppt (Catch l r c)       = l ++ ':':
                            (indent ("\ncatch " ++ (ppt r))) ++
                            "\n" ++ (ppt c)

  ppt (Jmp l r c)         = l ++ ':':'\n':
                            '\t':"jmp " ++ (ppt r) ++
                            '\n':(ppt c)

  ppt (LabelPt l c)       = l ++ ':':'\n':(ppt c)

  ppt (Halt l)            = l ++ ":"

--
-- simple imperative code:
--
data ASM = End
         | FBy Stmt ASM
         | BZ_K Expr Block Block Block
         | JSR Label Ref ASM           -- second argument is used for jump-back
         deriving Show


data Stmt = Assign Ref Expr
          | Set Ref
          | Clr Ref
          | Tst Expr
          | SysCall
          | NOP
          deriving Show

instance PPT ASM where
  ppt (FBy s r)        = (ppt s) ++
                         '\n':(ppt r)

  ppt (BZ_K x k k' k'') = '\n':
                          '\t':"bz " ++ (ppt x) ++ ' ':(startof k') ++
                          '\n':(ppt k) ++
                          '\n':'\t':"jmp " ++ (startof k'') ++
                          '\n':(ppt k') ++
                          '\n':'\t':"jmp " ++ (startof k'') ++
                          '\n':(ppt k'')

  ppt (JSR l t k) = '\t':"jmp " ++ (ppt t) ++
                    '\n':l ++
                    ':':'\n':(ppt k)

  ppt End       = ""


instance PPT Stmt where
  ppt (Assign r x) = '\t':(ppt r) ++ " := " ++ (ppt x)
  ppt (Set r)      = '\t':"set " ++ (ppt r)
  ppt (Clr r)      = '\t':"clr " ++ (ppt r)
  ppt (Tst x)      = '\t':"tst " ++ (ppt x)
  ppt SysCall      = '\t':"syscall"
  ppt NOP          = '\t':"nop"


--
-- mutable references:
--
data Ref = Var String           -- ordinary scalar variable
         | LabelRef Label       -- reference to a label in the code
         | Array String Expr    -- flat array
         | StructFld Ref String -- C-like 'struct' field
         | UnionFld Ref String  -- C-like 'union' field

         | R_Ret                -- the distinguished monadic 'return' reference
         | R_Rti                -- the distinguished forward-jump register for R
         | R_Nxt                -- next-action save register
         | R_Pro                -- a status bit used to control assigns to Rti
         | R_Req                -- reactive request register
         | R_Z                  -- the machine-status zero-bit

         | R_Spill              -- kludge used later for register allocation

         | IMR                  -- the interrupt mask register
         | INR                  -- the waiting interrupt register

         | DecConstant String   -- declared constant

         | SysConstant String   -- predefined system constant
         deriving Show


--
-- Equality here is used only indirectly by the data flow analyses,
-- which keep the 'R_*' constructors as distinguished registers;
-- other types of references should not, in general be tested for equality.
--
-- (2010.11.07) Schulz
--
instance Eq Ref where
  R_Ret   == R_Ret    = True
  R_Rti   == R_Rti    = True
  R_Nxt   == R_Nxt    = True
  R_Pro   == R_Pro    = True
  R_Req   == R_Req    = True
  R_Z     == R_Z      = True
  IMR     == IMR      = True
  INR     == INR      = True
  _       == _        = False

instance PPT Ref where
  ppt (Var x)         = x
  ppt (LabelRef l)    = l
  ppt (Array v x)     = v ++ '[':(ppt x) ++ "]"
  ppt (StructFld s f) = '(':(ppt s) ++ '.':f ++ ")"
  ppt (UnionFld s f)  = '(':(ppt s) ++ '.':f ++ ")"
  ppt R_Ret           = "r_ret"
  ppt R_Rti           = "r_rti"
  ppt R_Nxt           = "r_nxt"
  ppt R_Pro           = "r_pro"
  ppt R_Req           = "r_req"
  ppt R_Z             = "r_z"
  ppt IMR             = "imr"
  ppt INR             = "inr"
  ppt (DecConstant c) = c
  ppt (SysConstant x) = x

--
-- primitive expressions:
--
data Expr = DeRef Ref

          -- resumption references:
          | IsDone Ref     -- predicate corresponding to 'Pause' and 'Done'

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

          -- equality / inequality:
          | EqTest Expr Expr
          | IneqTest Expr Expr
          | LTTest Expr Expr
          | GTTest Expr Expr
          | LTETest Expr Expr
          | GTETest Expr Expr

          -- literals:
          | SInt Int       -- integer literal
          | SBool Bool     -- boolean literal
          | Clear          -- the unit-element equivalent

          deriving Show

instance PPT Expr where
  ppt (DeRef r)       = ppt r

  ppt (IsDone r)      = "isdone " ++ (ppt r)

  ppt (Neg x)         = '-':'(':(ppt x) ++ ")"
  ppt (Add x x')      = (ppt x) ++ " + " ++ (ppt x')
  ppt (Sub x x')      = (ppt x) ++ " - " ++ (ppt x')
  ppt (Mul x x')      = (ppt x) ++ " * " ++ (ppt x')
  ppt (Div x x')      = (ppt x) ++ " / " ++ (ppt x')

  ppt (Not x)         = '!':(ppt x)
  ppt (And x x')      = (ppt x) ++ " && " ++ (ppt x')
  ppt (Or x x')       = (ppt x) ++ " || " ++ (ppt x')

  ppt (EqTest x x')   = '(':(ppt x) ++ " == " ++ (ppt x') ++ ")"
  ppt (IneqTest x x') = '(':(ppt x) ++ " != " ++ (ppt x') ++ ")"
  ppt (GTTest x x')   = '(':(ppt x) ++ " < " ++ (ppt x') ++ ")"
  ppt (LTTest x x')   = '(':(ppt x) ++ " > " ++ (ppt x') ++ ")"
  ppt (GTETest x x')  = '(':(ppt x) ++ " <= " ++ (ppt x') ++ ")"
  ppt (LTETest x x')  = '(':(ppt x) ++ " >= " ++ (ppt x') ++ ")"

  ppt (SInt n)        = show n
  ppt (SBool False)   = "FALSE"
  ppt (SBool True)    = "TRUE"
  ppt Clear           = "CLEAR"


--
-- declaration constructs:
--
data DDec = VDec String RSITy   -- variable declaration
          | SDec String [DDec]  -- structure declaration
          | UDec String [DDec]  -- union declaration
          deriving Show

instance PPT DDec where
  ppt (VDec x t)  = (ppt t) ++ ' ':x
  ppt (SDec s ds) = "struct {" ++
                    (foldr (\d -> \s -> (ppt d) ++ '\n':s) ("\n} " ++ s) ds)

data RSITy = TInt
           | TBool
           | TLabel
           | TStruct String
           | TUnion String
           | TVoid          -- this, at present, is a dummy type (2010.10.19)
           deriving Show

instance PPT RSITy where
  ppt TInt        = "int"
  ppt TBool       = "bool"
  ppt TLabel      = "label"
  ppt (TStruct s) = "struct " ++ s
  ppt (TUnion u)  = "union " ++ u
  ppt TVoid       = "void"

torsity :: CTTy -> RSITy
torsity CTIntTy               = TInt
torsity CTBoolTy              = TBool
torsity (CTMTy _ _)           = TLabel
torsity (CTConTy (TyCon c) _) = TStruct c
torsity (CTPairTy _ _)        = TStruct tuplestruct


--
-- control flow used by the RSI sub-phases, where 'Atom' and 'Throw'
-- are compiled away;
--
-- the Imr variant of RSI uses all the same control structures
-- and imperative constructs, but dispenses with 'Atom' and 'Throw':
--
--
data Code_B     = R_B Label Chain_B | K_B Label Block deriving Show
type CodeSect_B = [Code_B]
newtype RSI_B   = RSI_B (DataSect, (Label, CodeSect_B)) deriving Show

instance PPT RSI_B where
  ppt (RSI_B (ds, (l, cs))) = data_sect_header ++ '\n':
                              (foldr (\d -> \s -> (ppt d) ++ "\n" ++ s) "" ds) ++
                              code_sect_header ++ '\n':
                              init_label ++ ':':(ppt (init_code))
                              ++ '\n':'\t':"jmp " ++ l ++ '\n':'\n':
                              (foldr (\c -> \s -> (ppt c) ++ '\n':s) "" cs)


instance Addressable Code_B where
  startof (R_B l _) = l
  startof (K_B l _) = l

instance PPT Code_B where
  ppt (R_B l r) = if (l /= startof r)
                    then
                      '\n':'\n':l ++ ':':'\n':(ppt r) ++ '\n':'\t':"done"
                    else
                      '\n':'\n':(ppt r) ++ '\n':'\t':"done"

  ppt (K_B l k) = if (l /= startof k)
                    then
                      '\n':'\n':l ++ ':':'\n':(ppt k) ++
                      '\n':'\t':"jmp " ++ (rtsreg l)
                    else
                      '\n':'\n':(ppt k) ++
                      '\n':'\t':"jmp " ++ (rtsreg l)


--
-- basic unit in the Imr variant is a simple, labeled
-- block, with no implied atomicity; the presumably
-- atomic behavior is produced by the compiler;
--
-- programs consist of simple blocks chained;
--
-- note that both 'swt' and 'catch' are compiled away by this phase,
-- and so do not appear in this variant of 'Chain';
--
-- (2010.10.09) Schulz
--
data Chain_B = Seq_B Block Chain_B
             | BZ_B Label Expr Chain_B Chain_B Chain_B
             | Loop_B Label Chain_B Chain_B
             | Break_B Label Expr
             | Swr_B Label Ref Chain_B
             | Jmp_B Label Ref Chain_B
             | LabelPt_B Label Chain_B
             | Halt_B Label
             deriving Show

instance Addressable Chain_B where
  startof (Seq_B a _)           = startof a
  startof (BZ_B l _ _ _ _)      = l
  startof (Loop_B l _ _)        = l
  startof (Break_B l _)         = l
  startof (Swr_B l _ _)         = l
  startof (Jmp_B l _ _)         = l
  startof (LabelPt_B l _)       = l
  startof (Halt_B l)            = l


instance PPT Chain_B where
  ppt (Seq_B b c)           = (ppt b ++ '\n':(ppt c))

  ppt (BZ_B l x c c' c'')   = l ++ ':':'\n':
                                '\t':"bzr " ++ (ppt x) ++

                                (

                                indent $

                                '\n':'{':'\n':'\t':"NOT_ZERO" ++ '{':
                                   (indent ('\n':(ppt c) ++
                                     "\njmp " ++ (startof c'') ++ "\n}")) ++
                                '\n':'\n':'\t':"ZERO"++ '{':
                                   (indent ('\n':(ppt c') ++
                                     "\njmp " ++ (startof c'') ++ "\n}"))

                                ) ++

                                '\n':'\t':'}':';':'\n':(ppt c'')


  ppt (Loop_B l c c')       = l ++ ':':'\n':
                                (ppt c) ++
                                '\n':'\t':"jmp " ++ l ++
                                '\n':(ppt c')

  ppt (Break_B l v)         = let ret = Assign R_Ret v
                                in
                                  (ppt ret) ++
                                  '\t':"jmp " ++ l

  ppt (Swr_B l r c)         = l ++ ':':'\n':
                                '\t':"swr " ++ (ppt r) ++
                                ';':'\n':(ppt c)

  ppt (Jmp_B l r c)         = l ++ ':':'\n':
                                '\t':"jmp " ++ (ppt r) ++
                                '\n':(ppt c)

  ppt (LabelPt_B l c)       = l ++ ':':'\n':(ppt c)

  ppt (Halt_B l)            = l ++ ":"




--                     --
-- BASIC STRUCTURE OPS --
--                     --

asmcat :: ASM -> ASM -> ASM
asmcat (FBy s k) k'           = FBy s (asmcat k k')

asmcat (BZ_K x k k' (Block l k'')) k''' =
  BZ_K x k k' (Block l (asmcat  k'' k'''))

asmcat (JSR l t k) k'         = JSR l t (asmcat k k')
asmcat End k'                 = k'



--
-- a block of simple initializations that should begin any program:
--
init_label :: Label
init_label = "__init"

init_code :: ASM
init_code = FBy (Assign R_Pro (SBool True)) End

data_sect_header :: String
data_sect_header = ".DATA"

code_sect_header :: String
code_sect_header = ".CODE"

tuplestruct :: String
tuplestruct = "Tuple"


-- THIS IS THE END OF THE FILE --
