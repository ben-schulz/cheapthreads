module Deprecated.ETIC.Syntax where

data Prog = Prog [TopDecl] deriving Show

type Address = Integer

data TopDecl = TopVarDecl VarDecl
             | IODecl Type String Address
             | ImageDecl String String
             | FunDecl (Maybe Type) String [(Type,String)] [VarDecl] [Stmt]
             | HandlerDecl HandlerSpec [VarDecl] [Stmt]

             -- "union type_name {alt_type alt_name; [alt_type alt_name;]}"
             | UnionDec String [(String, Type)]

             --  "struct type_name
             --     {member_type field_name; [member_type field_name;]}"
             | StructDec String [(String, Type)]

             -- C-like enumerations:
             | EnumDec [String]

--
-- old unions; retired because they conflate 'union' and 'struct';
--
-- to be phased out in favor of 'UnionDec' above
--
-- (2010.05.23) Schulz
--
             | UnionDecl String [(String,[Type])]

             deriving Show

data HandlerSpec = Interrupt Integer
                 | Trap
                 | Init
                 | Exc
                 deriving Show --what about exceptions?

data Expr = Var String

          | VarIX String Expr  -- indexed variable, i.e. array access
                               -- (2010.05.19) Schulz
          | LitInt Integer
          | LitBool Bool
          | LitChar Char
          | LitString String
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | Div Expr Expr
          | Modulus Expr Expr
          | Neg Expr
          | AndLogic Expr Expr
          | OrLogic Expr Expr
          | Not Expr
          | IsLT Expr Expr
          | IsGT Expr Expr
          | IsLTE Expr Expr
          | IsGTE Expr Expr
          | IsEq Expr Expr
          | NotEq Expr Expr
          | AndBit Expr Expr
          | OrBit Expr Expr
          | XorBit Expr Expr
          | ShiftL Expr Expr
          | ShiftR Expr Expr
          | NotBit Expr
          | FunCall String [Expr]
          | TCBAccess Expr String
          | MemAccess Expr Expr
          | ImageSegCount String
          | ImageSegVAddr String Expr
          | ImageSegPAddr String Expr
          | ImageSegAlign String Expr
          | ImageSegSize String Expr

          -- aggregate structure operations:
          | CtorApp String [Expr]
          | StructMember Expr String  -- as in C: "<expr>.field_name"
          | UnionMember Expr String   -- as in C: "<expr>.field_name"
          | MkPair Expr Expr
          | EmptyStack                -- If you have stacks, you need this
          | IsEmpty Expr              -- If you have stacks, you need this
          | Top Expr                  -- non-destructive stack pop
          | SRest Expr                -- non-destructive reference to stack tail
          | Pop Expr                  -- primitive stack pop
          | Push Expr Expr            -- primitive stack push, as: <val> <stack>

          -- thread operations:
          | MkThread [Stmt]     -- instantiate a thread
          | RunThread Expr      -- run a thread referenced from an expr
          | Slice Expr          -- make a time slice from a thread reference
          | IsDone Expr         -- test whether a thread has terminated
          | TRetOf Expr         -- get the return value from a terminated thread
          | TTail Expr          -- get to-execute remainder of the given thread
          | SigOf Expr          -- get current signal from the given thread
          deriving Show

data LHS = LHSVar String
         | LHSVarIX String Expr  -- array element on the LHS
                                 -- (2010.05.19) Schulz
         | LHSTCB Expr String
         | LHSMEM Expr String
         deriving Show

data Type = TyInt
          | TyByte
          | TyBool
          | TyChar
          | TyString
          | TyPair Type Type
          | TyArray Int Type  -- fixed-length array; (2010.05.19) Schulz
          | TyQueue Type
          | TyStack Type

          | TyStruct String   -- a declared C-like 'struct' (2010.05.23) Schulz
          | TyUnion String    -- a declared C-like 'union' (2010.05.23) Schulz

          | TyTCB             -- thread control blocks are important
                              -- enough to merit their own type
          | TyUserDef String
          | TyVoid            -- 'unit' or 'no-return value'
          deriving (Eq,Show)


data CaseSelector = Default
                  | CaseExpr Expr
                  deriving Show

data PatBinder = VarBinder String
               | ConstBinder Integer
               | CtorBinder          -- workaround (2010.05.19) Schulz
               | PairBinder          -- workaround (2010.05.19) Schulz
               | WildcardBinder
               deriving Show

data Pat = PatMatch String [PatBinder]
         | PatTuple [PatBinder]
         | PatVar String
         | PatDefault
         deriving Show

data Stmt = ExprStmt Expr
          | DeclStmt VarDecl
          | Assign LHS Expr

          | SysCall Expr       -- jump to the handler, argument is request
          | IOStmt String Expr
          | Case Expr [(CaseSelector,[Stmt])]
          | MatchUnion Expr [(Pat,[Stmt])]
          | IfThenElse Expr [Stmt] (Maybe [Stmt])
          | While Expr [Stmt]   -- why do we have a 'while'? (2010.05.22) Schulz
          | Loop String [Stmt]
          | Break              -- break out of current loop (2010.05.22) Schulz
          | Jump String
          | Return Expr
          | Skip
          deriving Show

data Modifier = Const deriving (Eq,Show)

data VarDecl = VarDecl [Modifier] Type String (Maybe Expr) deriving Show
