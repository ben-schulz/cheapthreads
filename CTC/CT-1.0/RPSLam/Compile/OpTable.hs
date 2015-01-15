--
-- this is ~/cheapthreads/ctc_working/CT-1.0/CT/OpTable.hs
--
-- a table of the CT primitive operations, their fixity,
-- asssociativity, and precedence
--
-- put here 2010.09.2010
-- 
-- Schulz
--

module Compile.OpTable where


--            --
-- DATA TYPES --
--            --

--
-- operation fixity:
--
data CTFixity = Prefix | Infix | Postfix deriving Show

instance Eq CTFixity where
  Prefix  == Prefix   = True
  Infix   == Infix    = True
  Postfix == Postfix  = True
  _       == _        = False



--
-- operation associativity:
--
data CTAssoc = LHAssoc | RHAssoc | NonAssoc deriving Show

instance Eq CTAssoc where
  LHAssoc  == LHAssoc   = True
  RHAssoc  == RHAssoc   = True
  NonAssoc == NonAssoc  = True
  _        == _         = False


--
-- precedence, where a higher value indicates
-- higher precedence:
--
type Precedence = Int

--
-- the basic operation type:
--
type CTOp = (String, (Precedence, (CTFixity, CTAssoc)))

--
-- some boilerplate:
--

opSymbol :: CTOp -> String
opSymbol = fst

opPrec :: CTOp -> Precedence
opPrec = fst . snd

opFixity :: CTOp -> CTFixity
opFixity = fst . snd . snd

opAssoc :: CTOp -> CTAssoc
opAssoc = snd . snd. snd



--          --
-- OP TABLE --
--          --

--
-- the main table:
--
-- By convention, we use the same precedence, associativity,
-- and fixity as used in Haskell 98
--
--
optable :: [CTOp]
optable =
  [
     (":",   (9, (Infix,  RHAssoc)))   -- cons
   , ("fst", (9, (Prefix, LHAssoc)))   -- cartesian projection 1
   , ("snd", (9, (Prefix, LHAssoc)))   -- cartesian projection 2

--   , ("slice", (9, (Prefix, LHAssoc))) -- bit slicing
   , ("&", (9, (Infix, LHAssoc)))        -- bit-cat

   , ("^",   (8, (Infix,  RHAssoc)))   -- exponentiation

   , ("*",   (7, (Infix, LHAssoc)))    -- multiplication
   , ("/",   (7, (Infix, LHAssoc)))    -- division

   , ("-", (7, (Prefix, LHAssoc)))     -- arithmetic negation

   , ("+",   (6, (Infix, LHAssoc)))    -- addition
   , ("-",   (6, (Infix, LHAssoc)))    -- subtraction

   , ("not", (5, (Prefix, LHAssoc)))   -- logical negation

   , ("==",  (4, (Infix, NonAssoc)))   -- equality test
   , ("/=",  (4, (Infix, NonAssoc)))   -- inequality test
   , ("<",   (4, (Infix, NonAssoc)))   -- less than
   , (">",   (4, (Infix, NonAssoc)))   -- greater than
   , ("<=",  (4, (Infix, NonAssoc)))   -- less-or-equal
   , (">=",  (4, (Infix, NonAssoc)))   -- greater-or-equal

   , ("&&",  (3, (Infix, RHAssoc)))    -- logical conjunction
   , ("||",  (2, (Infix, RHAssoc)))    -- logical disjunction

   -- it's very idiosyncratic, but bind
   -- should appear before null-bind here, for the purposes of parsing
   , (">>=", (1, (Infix, LHAssoc)))    -- monadic bind
   , (">>",  (1, (Infix, LHAssoc)))    -- monadic null-bind
  ]


--
-- get all operands of a given precedence:
--
getOpsPrec :: Precedence -> [CTOp] -> [CTOp]
getOpsPrec n = filter (\x -> (opPrec x) == n)


--
-- get all operands of a given fixity:
--
getOpsFix :: CTFixity -> [CTOp] -> [CTOp]
getOpsFix f = filter (\x -> (opFixity x) == f)


--
-- get all operands of a given associativity:
--
getOpsAssoc :: CTAssoc -> [CTOp] -> [CTOp]
getOpsAssoc a = filter (\x -> (opAssoc x) == a)


--
-- get the opstring of all operators with a particular
-- precedence, associativity, and fixity:
--
getOps :: Precedence -> CTFixity -> CTAssoc -> [String]
getOps n f a =
  map opSymbol $ (getOpsAssoc a) $ (getOpsFix f) $ (getOpsPrec n) optable



-- THIS IS THE END OF THE FILE --
