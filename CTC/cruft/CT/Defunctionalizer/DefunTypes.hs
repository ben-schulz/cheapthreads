--
-- this is ~/cheapthreads/ctc/ct/defunctionalizer/DefunTypes.hs
--
-- types and constants used by the defunctionalizer(s)
--
-- put here 11.02.09 Schulz
--

module CT.Defunctionalizer.DefunTypes where

import CT.Syntax
import Data.Char
import CT.Defunctionalizer.BMonad

--                                    --
-- TYPES USED BY THE DEFUNCTIONALIZER --
--                                    --

-- K --

--
-- state and rule types of the abstract machine
-- resulting from defunctionalization
--

type KState = [(CtsIdent, DefunVal)]
type KRule = KState -> KState
type FunDec = (CtsIdent, ([CtsIdent], CtsExpr)) -- function declarations
type FEnv = [FunDec]

--
-- separate external memories from other state components; they need
-- to be written out separately by the code generator
--
-- 2009.11.16 Schulz
--
newtype Mem = Mem CtsIdent

--
-- these are the improved K-types; temporarily using
-- different names to delay type inconsistencies higher-up in the
-- until the lower-level evaluator functions have been overhauled
--
-- 13.07.09 Schulz
--

type KStatePlus = [(CtsIdent, RHVal)]
type KRulePlus = KStatePlus -> KStatePlus

--
-- specification of a K-state, as component labels and their types
--
type KSpec = [(CtsIdent, CtsType)]

--
-- K-State pretty printer
--
pptKState :: KState -> String
pptKState ks = "\n{\n" ++ (foldr f "" ks) ++ "\n}\n"
               where
                 f (x, v) s = (x ++ " := " ++ (show v) ++ "\n") ++ s


-- R --

data PC = PCI Int | PCL String

instance Show PC where
  show (PCI n) = "PC : " ++ show n
  show (PCL s) = "PC : <label> " ++ s

instance Eq PC where
  (==) (PCI n) (PCI m) =  n == m
  (==) (PCL s) (PCL t) =  s == t
  (==) _  _            = False
  (/=) x               = not . ((==) x)

--
-- writing the program counter as a state label:
--
writePC :: PC -> String
writePC (PCI n) = "PCI__" ++ (show n)
writePC (PCL l) = "PCL__" ++ l

type RState = (PC, KState)
type RRule = (RState, RState)

--
-- see above notes on K-types
--
-- 13.07.09 Schulz
--

type RStatePlus = (PC, KStatePlus)
type RRulePlus  = (RStatePlus, RStatePlus)

--
-- transitions may be conditional or unconditional;
-- this saves some passing around of needless boolean constants
--
type Transition = Either RRulePlus (BoolGuard, RRulePlus)

--
-- this, hopefully, will become the top-level type for the configuration
-- passed to the code generator:
--
-- 2009.11.16 Schulz
--

type SysConfig = (KStatePlus, [Mem], [Transition])

--
-- pretty-printer for the transition rules
--
pptRules :: [RRule] -> String
pptRules = foldr ((++) . pptRRule) "\n\n"

pptRulesPlus :: [Transition] -> String
pptRulesPlus = foldr ((++) . pptRRulePlus) "\n\n"

--
-- pretty-printer for a transition rule
--
pptRRule :: RRule -> String
pptRRule ((pc1, k1), (pc2, k2)) = 
  let pc = "\n" ++ (show pc1) ++ " ==> " ++ (show pc2) ++ "\n"
      ids1 = (map fst k1)
      ids2 = (map fst k2)
      ids = if (ids1 == ids2)
            then ids1
            else ["\n*** bad rule: unmatched identifiers"]
      z = zip ids $ zip (map snd k1) (map snd k2)
      ts = foldr
           ((++) . (\ (x, (u, v)) -> (if u == v then "" else "* ") ++
                                     x ++ ": " ++ (show u) ++ " ==> " ++
                                     (show v) ++"\n"))
           "" z
  in
    pc ++ ts ++ "\n"

pptRRulePlus :: Transition -> String
pptRRulePlus (Left ((pc1, k1), (pc2, k2))) = 
  let pc = "\n" ++ (show pc1) ++ " ==> " ++ (show pc2) ++ "\n"
      ids1 = (map fst k1)
      ids2 = (map fst k2)
      ids = if (ids1 == ids2)
            then ids1
            else ["\n*** bad rule: unmatched identifiers"]
      z = zip ids $ zip (map snd k1) (map snd k2)
      ts = foldr
           ((++) . (\ (x, (u, v)) -> (if (runB u) == (runB v)
                                       then "" else "* ")
                                     ++
                                     x ++ ": " ++ (show u) ++ " ==> " ++
                                     (show v) ++"\n"))
           "" z
  in
    pc ++ ts ++ "\n"

pptRRulePlus (Right (_, ((pc1, k1), (pc2, k2)))) = "Conditional here!\n"

--
-- pretty-printer for an R-State
--
pptRState :: RState -> String
pptRState (pc, k) = (show pc) ++ "\n" ++ (pptKState k) ++ "\n"


-- VALUES --

--
-- value type for evaluating expressions
-- to be written to states
--

--
-- suggest restructuring DefunVal to reflect exactly those
-- objects that evaluatable in FSMLang, i.e.
-- can occur as the components or boolean guards of
-- a transition rule
--
-- 09.07.09 Schulz
--

--
-- we now have a somewhat of a hierarchy for producing the
-- 'values'  expected from the evaluator:
--
--  RHVal
--    ^
--    |
--  FSMOp
--    ^
--    |
-- DefunVal
--
-- 'DefunVal' is a primitive value that can be expressed
-- as a literal or parameter; 'FSMOp' is any well-formed expression
-- obtained from 'DefunVal' and the recognized primitive
-- operations as permitted in a transition rule; RHVal extends
-- DefunVal to account for conditional values, i.e. values
-- obtained from branching behavior that will not be known until
-- run-time
--
-- Note, however, that RHVal and FSMOp are mutually recursive.
-- This feature has been retained to slightly expedite adding
-- new primitive operations in the future
--
-- 20.07.09 Schulz
--

--
-- these types added to permit writes to memory;
--
-- they may be later changed or extended to accept
-- more general values (read: to allow for translation of 'DefunVal'
-- into machine representable values)
--
-- 24.07.09 Schulz
--

--
-- have to use a really awful kludge here to get mixed symbolic-literal
-- expressions into the fields of memory reads / writes
--
-- God damn it.
--
-- 2009.12.29 Schulz
--

data Op = Plus | Minus | Mult

instance Show Op where
  show Plus  = "+"
  show Minus = "-"
  show Mult  = "*"

data MemVal = LitMVal Int | SymMVal String 
            | MValExpr Op MemVal MemVal

instance Show MemVal where
  show (LitMVal n) = show n
  show (SymMVal s) = s
  show (MValExpr op m m') = "(" ++ (show m) ++ (show op) ++ (show m') ++ ")"

type Addr = MemVal

{-
data Addr = LitAddr Int | SymAddr String

instance Show Addr where
  show (LitAddr n) = show n
  show (SymAddr s) = s
-}


--
-- base-values that can occur on the rhs of a state transition:
--
data DefunVal = DFInt Int
              | DFBool Bool
              | DFUnit
              | DFParam String  -- formal parameter used in transition rules
              | DFPOp FSMOp
              | DFContReq   -- added for Re 06.07.09
              | DFPortsReq  -- added for Re 06.07.09
              | DFAckRsp    -- added for Re 07.07.09
              | DFPortsRsp  -- added for Re 07.07.09; args TBD
              | DFConstrVal String [DefunVal]  -- constructed types; 08.07.09
              | DFMemRead String DefunVal         -- mem accesses 24.07.09
              | DFMemWrite String Addr MemVal -- mem accesses 24.07.09

              -- was going to use this for 'return codes' over ports, but it
              -- may not be necessary any longer (2009.12.10)
              | DFRetSig CtsIdent
              --

              | DFNil     -- nilval corresponds to initial state

instance Show DefunVal where
  show (DFInt i)  = show i
  show (DFBool b) = show b
--  show (DFParam s) = "<" ++ s ++ ">"
  show (DFParam s) = foldr f "" s
                       where f x y = if (isSpace x) then '_':y else x:y
  show (DFPOp p)   = show p
  show DFUnit      = "-1" 
  show DFContReq   = "cont"
  show DFPortsReq  = "getports"
  show DFAckRsp    = "ack"
  show DFPortsRsp  = "ports"
--  show (DFConstrVal c args) = "(" ++ c ++ (show args) ++ ")"
  show (DFConstrVal c args) = "(" ++ c ++ ")"
  show (DFMemWrite m x v) = (show x) ++ "|->" ++ m ++ "[" ++ (show v) ++ "]"
  show (DFMemRead s a) = s ++ "[" ++ (show a) ++ "]"
  show (DFRetSig x) = x
--  show DFNil       = "nilval"
  show DFNil       = "-1"

instance Eq DefunVal where
  (==) (DFInt x) (DFInt y) =  x == y
  (==) (DFBool x) (DFBool y) =  x == y
  (==) (DFParam x) (DFParam y) =  x == y
  (==) (DFPOp x) (DFPOp y) = x == y
  (==) DFUnit DFUnit = True
  (==) DFNil DFNil = True
  (==) _ _ = False
  (/=) x = not . (== x)

--
-- primitive operations to be evaluated
-- at run-time of the resulting FSM
--
-- note that this structure is mutually recursive
-- with 'DefunVal'

data FSMOp = FSMNop DefunVal

           -- arithmetic:
           | FSMPlus DefunVal DefunVal
           | FSMMinus DefunVal DefunVal
           | FSMMult DefunVal DefunVal

           -- equalities, inequalities:
           | FSMEquality DefunVal DefunVal
           | FSMInequality DefunVal DefunVal
           | FSMLTTest DefunVal DefunVal
           | FSMGTTest DefunVal DefunVal
           | FSMLTETest DefunVal DefunVal
           | FSMGTETest DefunVal DefunVal
 
           -- simple boolean connectives:
           | FSMAnd DefunVal DefunVal
           | FSMOr DefunVal DefunVal
           | FSMNot DefunVal
     
           -- bit-wise logical operations:
           | FSMBWAnd DefunVal DefunVal
           | FSMBWOr  DefunVal DefunVal
           | FSMBWNot DefunVal

           -- bit-shifts:
           | FSMShiftL DefunVal DefunVal
           | FSMShiftR DefunVal DefunVal
  
           deriving Eq
-- hey, this could be a monad too (...?)


instance Show FSMOp where

  -- right now, mostly use the conventions from C (2009.12.28)
  show (FSMPlus u v) =  "(" ++ show u ++ " + " ++ show v ++ ")"
  show (FSMMinus u v) = "(" ++ show u ++ " - " ++ show v ++ ")"
  show (FSMMult u v) = "(" ++ show u ++ " * " ++ show v ++ ")"
  show (FSMEquality u v) = "(" ++ show u ++ " = " ++ show v ++ ")"
  show (FSMInequality u v) = "(" ++ show u ++ " /= " ++ show v ++ ")"
  show (FSMLTTest u v) = "(" ++ show u ++ " < " ++ show v ++ ")"
  show (FSMGTTest u v) = "(" ++ show u ++ " > " ++ show v ++ ")"
  show (FSMLTETest u v) = "(" ++ show u ++ " <= " ++ show v ++ ")"
  show (FSMGTETest u v) = "(" ++ show u ++ " >= " ++ show v ++ ")"
  show (FSMAnd u v) = "(" ++ show u ++ " && " ++ show v ++ ")"
  show (FSMOr u v) = "(" ++ show u ++ " || " ++ show v ++ ")"
  show (FSMNot u) = "(" ++ " ! " ++ show u ++ ")"
  show (FSMBWAnd u v) = "(" ++ show u ++ " & " ++ show v ++ ")"
  show (FSMBWOr u v) = "(" ++ show u ++ " | " ++ show v ++ ")"
  show (FSMBWNot u) = "(" ++ " ~ " ++ show u ++ ")"
  show (FSMShiftL u v) = "(" ++ show u ++ " <<< " ++ show v ++ ")"
  show (FSMShiftR u v) = "(" ++ show u ++ " >>> " ++ show v ++ ")"
  show (FSMNop v)    = "(" ++ show v ++ ")"


--
-- primitive values extended to conditional values,
-- in order to handle static if-then-else expresssions
-- (see log)
--
-- 13.07.09 Schulz
--

data BoolGuard = BGEquality DefunVal DefunVal
               | BGInequality DefunVal DefunVal
               | BGLT DefunVal DefunVal
               | BGGT DefunVal DefunVal
               | BGLTE DefunVal DefunVal
               | BGGTE DefunVal DefunVal
               | BGConjunct BoolGuard BoolGuard
               | BGDisjunct BoolGuard BoolGuard
               | BGNegate BoolGuard
               | BGVar CtsIdent
               | BGConstant Bool

instance Condition BoolGuard where
  evalCond     = \_ -> True  -- Kludge city!  (2009.11.17)
--  evalCond     = error "\'BoolGuard\' should not be evaluated by the compiler"
  negateCond   = bgNegate
  conjunctCond = BGConjunct
  disjunctCond = BGDisjunct

instance Show BoolGuard where
  show (BGEquality u v)   = (show u) ++ " == " ++ (show v)
  show (BGInequality u v) = (show u) ++ " != " ++ (show v)
  show (BGLT u v)         = (show u) ++ " < " ++ (show v)
  show (BGGT u v)         = (show u) ++ " > " ++ (show v)
  show (BGLTE u v)        = (show u) ++ " <= " ++ (show v)
  show (BGGTE u v)        = (show u) ++ " >= " ++ (show v)
  show (BGConjunct u v)   = (show u) ++ " && " ++ (show v)
  show (BGDisjunct u v)   = (show u) ++ " || " ++ (show v)
  show (BGConstant v)     = show v
  show (BGNegate u)       = "!(" ++ (show u) ++ ")"
  show (BGVar x)          = x
--  show _ = "another case for BoolGuard"

instance Eq BoolGuard where
  (BGEquality x y) == (BGEquality x' y')     = (x == x') && (y == y')
  (BGInequality x y) == (BGInequality x' y') = (x == x') && (y == y')
  (BGConjunct x y) == (BGConjunct x' y') =  (x == x') && (y == y')
  (BGDisjunct x y) == (BGConjunct x' y') =  (x == x') && (y == y')
  (BGConstant x) == (BGConstant x')      =  (x == x')
  (BGLT x y) == (BGLT x' y')  = (x == x') && (y == y')
  (BGGT x y) == (BGGT x' y')  = (x == x') && (y == y')
  (BGLTE x y) == (BGLTE x' y')  = (x == x') && (y == y')
  (BGGTE x y) == (BGGTE x' y')  = (x == x') && (y == y')
  _ == _  = False
  x /= y = not (x == y)



--
-- we use the convention that 'not (u < v)' = 'u >= v';
-- "not less than" is not strictly equivalent to "greater than"
--
-- 2009.11.16 Schulz
--
bgNegate :: BoolGuard -> BoolGuard
bgNegate (BGEquality u v) = BGInequality u v
bgNegate (BGInequality u v) = BGEquality u v

bgNegate (BGLT u v)  = BGGTE u v
bgNegate (BGGT u v)  = BGLTE u v
bgNegate (BGLTE u v) = BGGT u v
bgNegate (BGGTE u v) = BGLT u v

bgNegate (BGConjunct u v) = BGDisjunct (bgNegate u) (bgNegate v)
bgNegate (BGDisjunct u v) = BGConjunct (bgNegate u) (bgNegate v)
bgNegate (BGConstant b) = BGConstant $ not b

bgNegate (BGNegate u) = u
bgNegate (BGVar u)    = BGNegate (BGVar u)

--
-- separating formal parameters on the left-hand side
-- of a rule from those used on the right-hand side:
--

newtype LHVal = LH CtsIdent

instance Show LHVal where
  show (LH v) = v

--
-- right-hand side values: these are conditional values
-- realized using the B-monad
--

type RHVal = B BoolGuard DefunVal

instance (Show c, Show a, Condition c) => Show (B c a) where
  show (V x)       = show x
  show (C p b1 b2) = "(" ++ "if " ++ (show p) ++ " then " ++ (show b1)
                     ++ " else "
                     ++ (show b2) ++ ")"

{-
data RHVal = RHS DefunVal | RHC BoolGuard RHVal RHVal

instance Show RHVal where
  show (RHS v)       = show v
  show (RHC b r1 r2) = (show b) ++ " ==> " ++ (show r1) ++ " | " ++ (show r2)
-}


-- END TYPES -- 

--                  --
-- GLOBAL CONSTANTS --
--                  --

--
-- label of the initial state for every machine
--
init_label :: String
init_label = "__GLOBAL__INIT"

--
-- label of the final state in every machine
--
exit_label :: String
exit_label = "__GLOBAL__EXIT"

--
-- tag prefix for a fixpoint initial state
--
fix_init_label :: String
fix_init_label = "__INIT"

--
-- tag suffix for a fixpoint exit state
--
fix_exit_label :: String
fix_exit_label = "__LOOP_EXIT"

--
-- label identifying the handler routine used by Re
--
handlerL :: String
handlerL = "__HANDLER"

--
-- an FSM fragment implementing the secureQ handler:
--
handler_routine :: [RRulePlus]
handler_routine =
 let cont_init = [(vIdent, V $ DFParam vIdent),
                  (reqIdent, V $ DFContReq),
                  (rspIdent, V $ DFParam rspIdent),
                  (portIdent, V $ DFParam portIdent),
                  (rtsIdent, V $ DFParam rtsIdent)]

     ports_init = [(vIdent, V $ DFParam vIdent),
                   (reqIdent, V $ DFPortsReq),
                   (rspIdent, V $ DFParam rspIdent),
                   (portIdent, V $ DFParam portIdent),
                   (rtsIdent, V $ DFParam rtsIdent)]

     -- CONT in the request slot produces ACK
     -- in the response slot:
     cont_trans = [(vIdent, V $ DFParam vIdent),
                   (reqIdent, V $ DFParam reqIdent),
                   (rspIdent, V $ DFAckRsp),
                   (portIdent, V $ DFParam portIdent),
                   (rtsIdent, V $ DFParam rtsIdent)]

     -- GETPORTS in the reqest slot produces PORTS (value)
     -- in the response slot:
     ports_trans = [(vIdent, V $ DFRetSig vIdent),
                    (reqIdent, V $ DFParam reqIdent),
                    (rspIdent, V $ DFPortsRsp),
                    (portIdent, V $ DFParam portIdent),
                    (rtsIdent, V $ DFParam rtsIdent)]

     --
     -- use reserved labels for transitioning through the handler:
     --
     portsL = handlerL ++ "_GETPORTS"
     contL = handlerL ++ "_CONT"
     exitL = handlerL ++ "_EXIT"
 in

   -- i.e. for both case, place the proper response in the rsp slot
   -- and jump back to the address in rts
   [
    ((PCL handlerL, cont_init), (PCL contL, cont_trans)),
    ((PCL contL, cont_trans), (PCL exitL, cont_trans)),
    ((PCL exitL, cont_trans), (PCL rtsIdent, cont_trans)),

    ((PCL handlerL, ports_init), (PCL portsL, ports_trans)),
    ((PCL portsL, ports_trans), (PCL exitL, ports_trans)),
    ((PCL exitL, ports_trans), (PCL rtsIdent, ports_trans))
   ]

--
-- the reserved keyword identifying the K monad
-- in the abstract syntax
--
kIdent :: CtsIdent
kIdent = "K"

--
-- token for separating 'type portion'
-- of register identifiers; that is, we use
-- a string suffix to pass type annotations
-- from the preprocessor to the initialization
-- of states
--

typetoken :: String
typetoken = "  "

--
-- identifier for keying the return value component of state
--
vIdent :: CtsIdent
vIdent = "__retval"

--
-- identifier for keying "request" used for IPC
--
reqIdent :: CtsIdent
reqIdent = "__req"

--
-- identifier for keying "reponse" used for IPC
--
rspIdent :: CtsIdent
rspIdent = "__rsp"

--
-- identifier for keying "port" used for IPC
--
portIdent :: CtsIdent
portIdent = "__ports"

--
-- identifier for keying "return to" register used for IPC
--
rtsIdent :: CtsIdent
rtsIdent = "__rts"

--
-- identifier for the 'signal' funciton used in Re
--
signalRe :: CtsIdent
signalRe = "signal"

--
-- default members of any K-state:
--
defaultK :: KState
defaultK = [(vIdent, DFNil),
            (reqIdent, DFNil),
            (rspIdent, DFNil),
            (portIdent, DFNil),
            (rtsIdent, DFNil)]

--                                   --
-- identifier for 'step' application --
--                                   --
stepPrefix :: CtsIdent
stepPrefix = "step"


--                                        --
-- suffix for tagging a 'fix' application --
--                                        --
fixfix :: CtsIdent
fixfix = " fix"

--
-- a default type for identifiers written to FSM concrete syntax;
-- provisional, and should be superceded by type annotations
-- produced by the CT front-end
--
default_fsm_type_label :: String
default_fsm_type_label = "std_logic_vector(0 to INT_WIDTH - 1)"

--
-- write a CTS primitive type as a VHDL type (string)
--
showtype_vhdl :: CtsType -> String
showtype_vhdl TyInt = "integer"
showtype_vhdl TyBool = "boolean"
showtype_vhdl TyUnit = "bit"  -- this is a temporary kludge;
showtype_vhdl _      = "not_supported"  -- this is a temporary kludge;

-- THIS IS THE END OF THE FILE --
