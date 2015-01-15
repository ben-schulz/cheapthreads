--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/DFun/FSM.hs
--
-- specification of the (abstract) finite state machine
-- produced by defunctionalization
--
-- this representation is used as an intermediate representation
-- to be passed to some hardware specific back-end that will
-- produce FSMLang with the appropriate low-level details
--
-- put here 2010.02.12
--
-- Schulz
--

module CT.DFun.FSM where


import CT.Syntax
import CT.INAST
import CT.PPT


--
-- this is the abstract Mealy machine output by the transformation:
--
type FSMealy = ((([FSMSignal], [FSMMem]), [CommSig]), (TransD, [Trans]))


--
-- a program counter, used to index
-- the states of the machine
--
data PC = PCI Int | PCL String


instance Show PC where
  show (PCI n) = "PC_" ++ (show n)
  show (PCL s) = "LABEL_" ++ s

instance Eq PC where
  (PCI n) == (PCI m)  =  m == n
  (PCL s) == (PCL t)  =  s == t
  _       == _        =  False
  x       /= y        = not (x == y)

--
-- a transition of the machine is
-- equivalent to a change in the state
-- of the program counter, which may be
-- conditional or unconditional:
--
type Trans = Either (PC, PC) (BoolExpr, (PC, PC))

transof :: Trans -> (PC, PC)
transof (Left x)  = x
transof (Right x) = snd x

initof :: Trans -> PC
initof = fst . transof

termof :: Trans -> PC
termof = snd . transof

--
-- each program counter value corresponds
-- to exactly one set of changes to the global state,
-- whence we use a function here in order to economize
-- on whole states being passed around in transitions:
--

type STMod = [(STEL, ModExpr)]

type TransD = Trans -> STMod

-- the default transduction is no change to the signals
inittransd :: TransD
inittransd = \_ -> []

data STEL = Sig String         -- reference plain signal
          | Mem String FSMExpr -- name and address in a memory
          | PortIn String      -- reference to an input port
          | PortOut String     -- reference to an ouput port
          | Chan String        -- reference to a channel
          deriving Eq


nameofstel :: STEL -> String
nameofstel (Sig x)     = x
nameofstel (Mem m _)   = m
nameofstel (PortIn p)  = p
nameofstel (PortOut p) = p
nameofstel (Chan c)    = c

instance Show STEL where
  show (Sig x)     = x
  show (Mem m n)   = m ++ '[':(show n) ++ "]"
  show (PortIn p)  = p
  show (PortOut p) = p
  show (Chan c)    = '#':c



--
-- declared signals in the FSM:
--
type FSMTy = CTTy

type FSMSignal = (CTIdent, FSMTy)

type FSMMem = (String, (Int, FSMTy))


--
-- a simple association of types to some default sizes:
--
sizeof :: FSMTy -> Int
sizeof CTIntTy = 32

--
-- converting between type schemes:
-- (trivial at this time -- 2010.03.27)
--
toFSMTy :: CTTy -> FSMTy
toFSMTy = id

--
-- expression form for modifying the global state;
-- this encompasses simple expressions, as below,
-- as well as memory and port accesses, which we
-- segregate because FSMLang must treat them differently
--

data ModExpr = MX FSMExpr
             | MRef String FSMExpr 
             | ChanRef String
             | MUnOp  FSMOp ModExpr
             | MBinOp FSMOp ModExpr ModExpr
             deriving Eq

 
instance Show ModExpr where
  show (MX e)           = show e
  show (MRef m i)       = m ++ '[':(show i) ++ "]"
  show (ChanRef c)        = '#':c
  show (MUnOp op e)     = (show op) ++ ' ':(show e)
  show (MBinOp op e e') = (show e) ++ ' ':(show op) ++ ' ':(show e')


--
-- promote an identifier and a simple expression into signal assignment
--
mksigassgn :: (String, FSMExpr) -> (STEL, ModExpr)
mksigassgn (x, e) = (Sig x, MX e)

--
-- promote an identifier and a simple expression into a channel write:
--
mkchanwrite :: (String, FSMExpr) -> (STEL, ModExpr)
mkchanwrite (x, e) = (Chan x, MX e)

--
-- promote two identifiers to a read from a channel into a signal:
--
mkchanread :: (String, String) -> (STEL, ModExpr)
mkchanread (x, y) = (Sig x, ChanRef y)


--
-- a stream-lined expression grammar, corresponding
-- to simple expressions manipulating signals in
-- FSMLang; this is more or less just a surjection of the
-- higher-level CT syntax, removing all the moandic
-- operations.  The one exception is array/memory accesses,
-- which are implicit in CT, but must be made explicit here
--

data FSMExpr = FSMLit Literal                  -- literal
             | FSMSig String                   -- signal variable reference
             | FSMSlice FSMExpr FSMExpr FSMExpr -- bit-slice of a signal
             | FSMUnOp FSMOp FSMExpr           -- unary primitive
             | FSMBinOp FSMOp FSMExpr FSMExpr  -- binary primitive
             | FSMUnit                         -- a default "clear" value

              -- Eq used only indirectly for BoolExpr
             deriving Eq

instance Show FSMExpr where
  show (FSMLit x)          = (ppt x)
  show (FSMSig v)          = v
  show (FSMSlice e e' e'') = (show e)
                             ++ '(':(show e')
                             ++ " to "
                             ++ (show e'') ++ ")"

  show (FSMUnOp op e)      = (show op) ++ ' ':(show e)
  show (FSMBinOp op e e')  = (show e) ++ ' ':(show op) ++ ' ':(show e')
  show FSMUnit             = "ALL_ZEROS"

--
-- FSMLang primitives, which differ only slightly
-- from the CT primitives:
--
data FSMOp = FSMNot   -- logical negation
           | FSMAnd   -- logical conjunction
           | FSMOr    -- logical disjunction

           | FSMNeg   -- arithmetic negation
           | FSMPlus  -- addition
           | FSMMinus -- subtraction
           | FSMMult  -- multiplication
           | FSMDiv   -- division
           | FSMExpn  -- exponentiation

           | FSMEq    -- equality test
           | FSMIneq  -- inequality test
           | FSMLT    -- less-than
           | FSMGT    -- greater-than
           | FSMLTE   -- less-or-equal
           | FSMGTE   -- greater-or-equal

           | FSMBitCat -- bit-wise concatenation

           -- Eq used only indirectly for BoolExpr
           deriving Eq

--
-- 'Show' corresponds to FSMLang concrete syntax:
--
instance Show FSMOp where
  show FSMNot    = "not"
  show FSMAnd    = "and"
  show FSMOr     = "or"
  show FSMNeg    = "-"
  show FSMPlus   = "+"
  show FSMMinus  = "-"
  show FSMMult   = "*"
  show FSMDiv    = "/"
  show FSMExpn   = "**"
  show FSMEq     = "="
  show FSMIneq   = "/="
  show FSMLT     = "<"
  show FSMGT     = ">"
  show FSMLTE    = "<="
  show FSMGTE    = ">="
  show FSMBitCat = "&"


--
-- boolean expressions, which are distinguished from
-- ordinary expressions in order to avoid conflicts
-- with HDL conventions
--
-- we impose the restriction that boolean expressions
-- never incorporate memory or channel accesses
--

data BoolExpr = BoolVar String
              | BNot BoolExpr 
              | BAnd BoolExpr BoolExpr
              | BOr BoolExpr BoolExpr
              | BEq FSMExpr FSMExpr
              | BIneq FSMExpr FSMExpr
              | BLT FSMExpr FSMExpr
              | BGT FSMExpr FSMExpr
              | BLTE FSMExpr FSMExpr
              | BGTE FSMExpr FSMExpr


--
-- 'Show' also reflect FSMLang concrete syntax here:
--
instance Show BoolExpr where
  show (BoolVar x)  = "(\'1\' == " ++ x ++ ")"
  show (BNot e)     = "not " ++ (show e)
  show (BAnd e e')  = (show e) ++ " and " ++ (show e')
  show (BOr e e')   = (show e) ++ " or "  ++ (show e')
  show (BEq e e')   = (show e) ++ " = "   ++ (show e')
  show (BIneq e e') = (show e) ++ " /= "  ++ (show e')
  show (BLT e e')   = (show e) ++ " < "   ++ (show e')
  show (BGT e e')   = (show e) ++ " > "   ++ (show e')
  show (BLTE e e')  = (show e) ++ " <= "  ++ (show e')
  show (BGTE e e')  = (show e) ++ " >= "  ++ (show e')


--
-- here we use syntactic equivalence (as opposed to truth-table equivalence),
-- which is used for identifying transitions; in general, we should be able
-- to trust a competent programmer not to use syntactically different but
-- truth-value equivalent boolean expressions, and even if they do, 
-- it will only result in a redundant guarded transition
--

instance Eq BoolExpr where
  (BoolVar b)   == (BoolVar b')  =  b == b'
  (BNot b)      == (BNot b')     =  b == b'
  (BAnd x y)    == (BAnd x' y')  =  (x == x') && (y == y')
  (BOr x y)     == (BOr x' y')   =  (x == x') && (y == y')
  (BEq x y)     == (BEq x' y')   =  (x == x') && (y == y')
  (BIneq x y)   == (BIneq x' y') =  (x == x') && (y == y')
  (BLT x y)     == (BLT x' y')   =  (x == x') && (y == y')
  (BGT x y)     == (BGT x' y')   =  (x == x') && (y == y')
  (BLTE x y)    == (BLTE x' y')  =  (x == x') && (y == y')
  (BGTE x y)    == (BGTE x' y')  =  (x == x') && (y == y')
  _             == _             = False
  x             /= y             = not (x == y)



--
-- projecting simple expressions onto the restricted
-- FSMLang expression syntax:
--

toFSMExpr :: INAST -> FSMExpr
toFSMExpr (CTPrim1aryIN op  e _)   = FSMUnOp (toFSMOp op) (toFSMExpr e)
toFSMExpr (CTPrim2aryIN op e e' _) = FSMBinOp (toFSMOp op)
                                              (toFSMExpr e) (toFSMExpr e')

toFSMExpr (CTPrim3aryIN (Tri CTBitSlice) e e' e'' _) = FSMSlice
                                                        (toFSMExpr e)
                                                        (toFSMExpr e')
                                                        (toFSMExpr e'')
                                                 
toFSMExpr (CTVarIN x _)  = FSMSig x
toFSMExpr (CTLitIN l _)  = FSMLit l
toFSMExpr (CTUnitIN _)   = FSMUnit
-- another stub 2011.07.22
toFSMExpr (CTConIN "Read1" [] _) = FSMLit (LitInt 1)
toFSMExpr (CTConIN "Read2" [] _) = FSMLit (LitInt 2)
toFSMExpr (CTConIN "Write1" [] _) = FSMLit (LitInt 3)
toFSMExpr (CTConIN "Write2" [] _) = FSMLit (LitInt 4)
toFSMExpr x = error $ "no pattern in \'toFSMExpr\' for " ++ (show x)


toBoolExpr :: INAST -> BoolExpr

toBoolExpr (CTPrim1aryIN (Un op) e _) =
  case op of
    CTNot -> BNot (toBoolExpr e)

toBoolExpr (CTPrim2aryIN (Bin op) e e' _) = 
  case op of
    CTAnd      -> BAnd (toBoolExpr e) (toBoolExpr e')
    CTOr       -> BOr  (toBoolExpr e) (toBoolExpr e')

    CTEqTest   -> BEq   (toFSMExpr e) (toFSMExpr e')
    CTIneqTest -> BIneq (toFSMExpr e) (toFSMExpr e')

    CTLTTest   -> BLT  (toFSMExpr e) (toFSMExpr e')
    CTGTTest   -> BGT  (toFSMExpr e) (toFSMExpr e')
    CTLTETest  -> BLTE (toFSMExpr e) (toFSMExpr e')
    CTGTETest  -> BLTE (toFSMExpr e) (toFSMExpr e')

toBoolExpr (CTVarIN x _) = BoolVar x



toFSMOp :: CTPrimOp -> FSMOp

toFSMOp (Un op) =
  case op of
    CTNeg -> FSMNeg
    CTNot -> FSMNot

toFSMOp (Bin op) =
  case op of
    CTPlus      -> FSMPlus
    CTMinus     -> FSMMinus
    CTMult      -> FSMMult
    CTIDiv      -> FSMDiv
    CTExpn      -> FSMExpn
    CTEqTest    -> FSMEq
    CTIneqTest  -> FSMIneq
    CTLTTest    -> FSMLT
    CTGTTest    -> FSMGT
    CTLTETest   -> FSMLTE
    CTGTETest   -> FSMGTE
    CTBitCat    -> FSMBitCat



--
-- a simple optimization to remove states that are completely
--
{-
condense_fsm :: (TransD, [Trans]) -> (TransD, [Trans])
condense_fsm (d, ds) =
  
  foldr
  (\t -> \(d', ts) ->
    case t of
      (Left _) -> let x = initof t
                      y = termof t
                  in
                   case (lkpinit y ts) of
                     (Just t') -> if (d' t == d' t')
                                  then let t'' = (initof t, termof t')
                                           d'' = \s -> if s == t'' then (d' t)
                                                       else (d s)
                                       in (d'', t'':ts)
                                  else (d', ts)
                     
                     Nothing -> (d', t:ts)
                     
      (Right _) -> (d', t:ts)  
  
  ) (d, []) (d, ds)

-}
--
-- DEFAULTS AND CONSTANTS
--

--
-- default integer width:
--
default_int_width :: Int
default_int_width = 32

--
-- the data width label used in forming declarations
--
data_width_label :: String
data_width_label = "DATA_WIDTH"


--
-- identifier of the return value slot:
--
retval :: String
retval = "__retval"

--
-- the default (two-way) channel to/from which
-- all signals are written/read, unless specified
-- otherwise in the translation to FSMLang:
--
default_chan :: String
default_chan = "__default_channel"

--
-- default prefix for channel names:
--
chan_prefix :: String
chan_prefix = "__chan_"


--
-- a default label for the initial state of the FSM:
--
global_init :: PC
global_init = PCL "___GLOBAL_INIT"


--
-- program counter start value:
--
initpc :: Int
initpc = 0

inittrans :: Trans
inittrans = Left (global_init, PCI initpc)



-- THIS IS THE END OF THE FILE --
