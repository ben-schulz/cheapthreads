--
-- this is ~/cheapthreads/CTC/CT-1.0/RSI/SAL/Syntax.hs
--
-- abstract syntax for a generic, simplified assembly language (SAL)
-- i.e. three-address code target to follow the RSI phase of the compiler
--
-- put here (2010.10.14)
--
-- Schulz
--

module RSI.SAL.Syntax where

import CT.PPT

import RSI.Syntax

data VReg = VReg Int  -- general-purpose virtual register
          | SReg Ref  -- a special register, e.g. r_ret
          | MR MReg   -- an actual machine register, assigned by the compiler
          | Phi       -- the phi function, used for data flow analyses
          deriving (Show, Eq)


--
-- expressible values are allowed for immediate
-- addressing; these are restricted only to
-- simple integers, address labels (resolved to integers by the assembler),
-- and the 'sizeof' macros, used to resolve offsets for data structures
-- (also resolved by the assembler, or some pass immediately before it)
--
data SVal = Num Int
          | Adr Label       -- location label resolved by the assembler
          | Symbol String   -- declared constant
          | SizeOf RSITy    -- 'sizeof' macro for laying out memory
          | SOffSet String  -- offset of a struct field
          deriving Show

--
-- variables map either to a machine register,
-- or to a spill to be handled:
--
data MReg = MReg Int
          | Spill VReg         -- spill is marked with its virtual register
          deriving (Show, Eq)

isspill :: MReg -> Bool
isspill (Spill _) = True
isspill _         = False

spillvarof :: MReg -> VReg
spillvarof (Spill v) = v



instance PPT SVal where
  ppt (Num n)     = show n
  ppt (Adr l)     = l
  ppt (Symbol x)  = x
  ppt (SizeOf t)  = "sizeof(" ++ (ppt t) ++ ")"
  ppt (SOffSet f) = "offset(" ++ f ++ ")"


instance PPT VReg where
  ppt (VReg n) = 'r':(show n)
  ppt (SReg r) = ppt r
  ppt (MR r)   = ppt r
  ppt Phi      = "PHI"


instance PPT MReg where
  ppt (MReg n)  = 'r':(show n)
  ppt (Spill v) = "SPILL " ++ (ppt v)

-- output of this compile pass
newtype SAL = SAL (DataSect, (Label, [InsSeq])) deriving Show

instance PPT SAL where
  ppt (SAL (ds, (l, as))) = data_sect_header ++ '\n':'\n':
                            (foldr (\d -> \s -> (ppt d) ++ '\n':s) "\n\n" ds) ++
                            code_sect_header ++ '\n':
                            init_label ++ ':':(ppt (init_code))
                            ++ '\n':'\t':"jmp " ++ l ++ '\n':'\n':
                            (foldr (\c -> \s -> (ppt c) ++ '\n':s) "" as)

                           

data InsSeq = Semi Ins InsSeq
            | Labeled Label InsSeq
            | Nil
            deriving Show

instance PPT InsSeq where
  ppt (Semi i p)    = ppt i ++ '\n':(ppt p)
  ppt (Labeled l p) = l ++ ':':'\n':(ppt p)
  ppt Nil           = "\n"

inscat :: InsSeq -> InsSeq -> InsSeq
inscat (Semi i p) p'    = Semi i (inscat p p')
inscat (Labeled l p) p' = Labeled l (inscat p p')
inscat Nil p'           = p'


-- only use this basic blocks:
lastins :: InsSeq -> Ins
lastins (Semi i Nil)   = i
lastins (Semi i is)    = lastins is

-- drop the last instruction from a sequence:
initins :: InsSeq -> InsSeq
initins (Semi i (Semi _ Nil)) = Semi i Nil
initins (Semi i is)           = Semi i (initins is)
initins (Labeled l is)        = Labeled l (initins is)
initins Nil                   = Nil

-- right-fold on instruction sequences, ignoring labels:
foldinsseq :: (Ins -> a -> a) -> a -> InsSeq -> a
foldinsseq f t (Semi i p)    = foldinsseq f (f i t) p
foldinsseq f t (Labeled l p) = foldinsseq f t p
foldinsseq _ t Nil           = t


--
-- simplified assembly language instruction set;
--
-- by convention, the first argument is the destination register;
-- all binary operations occur left-to-right;
--
--
data Ins = Load VReg VReg VReg      -- load from address r2 + r3 to r1
         | LoadI VReg VReg SVal     -- load from address r2 + L to r1
         | Mov VReg VReg            -- move r2 to r1
         | MovI VReg SVal           -- direct assignment to r1
         | Store VReg VReg VReg     -- store contents of r1 at address r2 + r3
         | StoreI VReg VReg SVal    -- store contents of r1 at address r2 + L

         -- asynchronous control flow:
         | Interrupt
         | IMR_Set
         | IMR_Clr

         -- basic control flow:
         | MBZ VReg SVal        -- if rA == 0 then branch to immediate address
         | MTst VReg VReg       -- rD := if rA == 0 then 1 else 0
         | MJmp VReg
         | MJmpI SVal

         -- arithmetic:
         | MAdd  VReg VReg VReg  -- rD := rA + rB
         | MAddI VReg VReg SVal  -- rD := rA + n
         | MSub  VReg VReg VReg  -- rD := rA - rB
         | MSubI VReg VReg SVal  -- rD := rA - n
         | MMul  VReg VReg VReg  -- rD := rA * rB
         | MDiv  VReg VReg VReg  -- rD := rA / rB

         -- logic:
         | MCmp VReg VReg VReg   -- rD := sgn(rA - rB)
         | MCmpI VReg VReg SVal  -- rD := sgn(rA - n)
         | MAnd VReg VReg VReg
         | MAndI VReg VReg SVal
         | MOr VReg VReg VReg
         | MOrI VReg VReg SVal

         | Nop
         deriving Show

instance PPT Ins where
  ppt (Load r r' r'')   = "ld   " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (LoadI r r' r'')  = "ldi  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (Mov r r')        = "mv   " ++ (ppt r) ++ ',':(ppt r')
  ppt (MovI r r')       = "mvi  " ++ (ppt r) ++ ',':(ppt r')
  ppt (Store r r' r'')  = "st   " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (StoreI r r' r'') = "sti  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')

  ppt Interrupt         = "interrupt"
  ppt IMR_Set           = "seti"
  ppt IMR_Clr           = "mski"

  ppt (MBZ r r')        = "bz   " ++ (ppt r) ++ ',':(ppt r')
  ppt (MTst r r')       = "tst  " ++ (ppt r) ++ ',':(ppt r')
  ppt (MJmp r)          = "jmp  " ++ (ppt r)
  ppt (MJmpI v)         = "jmpi " ++ (ppt v)

  ppt (MAdd r r' r'')   = "add  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MAddI r r' r'')  = "addi " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MSub r r' r'')   = "sub  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MSubI r r' r'')  = "subi " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MMul r r' r'')   = "mul  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MDiv r r' r'')   = "div  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')

  ppt (MCmp r r' r'')   = "cmp  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MCmpI r r' r'')  = "cmp  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MAnd r r' r'')   = "and  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MAndI r r' r'')  = "andi " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MOr r r' r'')    = "or   " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')
  ppt (MOrI r r' r'')   = "ori  " ++ (ppt r) ++ ',':(ppt r') ++ ',':(ppt r'')

  ppt Nop               = "nop"


--
-- some useful accessors for computing dataflow from 'Ins':
--

dst :: Ins -> Maybe VReg

dst (Load r _ _)   = Just r
dst (LoadI r _ _ ) = Just r
dst (Mov r _)      = Just r
dst (MovI r _)     = Just r
dst (Store r _ _ ) = Just r
dst (StoreI r _ _) = Just r

dst (MBZ _ _)      = Nothing
dst (MTst r _)     = Just r
dst (MJmp _)       = Nothing
dst (MJmpI _)      = Nothing

dst Interrupt      = Nothing
dst IMR_Clr        = Nothing
dst IMR_Set        = Nothing

dst (MAdd r _ _)   = Just r
dst (MAddI r _ _)  = Just r
dst (MSub r _ _)   = Just r
dst (MSubI r _ _)  = Just r
dst (MMul r _ _)   = Just r
dst (MDiv r _ _)   = Just r

dst (MCmp r _ _)   = Just r
dst (MCmpI r _ _)  = Just r
dst (MAnd r _ _)   = Just r
dst (MAndI r _ _)  = Just r
dst (MOr r _ _)    = Just r
dst (MOrI r _ _)   = Just r

dst Nop            = Nothing


src :: Ins -> [VReg]

src (Load _ r r')    = [r, r']
src (LoadI _ r _)    = [r]
src (Mov _ r)        = [r]
src (MovI _ _)       = []
src (Store r r' r'') = [r, r', r'']  -- NOTE: stores use first reg to det loc!
src (StoreI r r' _)  = [r, r']

src (MBZ _ _)       = []
src (MTst _ r)      = [r]
src (MJmp r)        = [r]
src (MJmpI _)       = []

src Interrupt       = []
src IMR_Set         = []
src IMR_Clr         = []

src (MAdd _ r r')   = [r, r']
src (MAddI _ r _)   = [r]
src (MSub _ r r')   = [r, r']
src (MSubI _ r _)   = [r]
src (MMul _ r r')   = [r, r']
src (MDiv _ r r')   = [r, r']

src (MCmp _ r r')   = [r, r']
src (MCmpI _ r _)   = [r]
src (MAnd _ r r')   = [r, r']
src (MAndI _ r _)   = [r]
src (MOr _ r r')    = [r, r']
src (MOrI _ r _)    = [r]

src Nop             = []

--
-- get the jump target of a control flow instruction:
--
jtar :: Ins -> Either VReg SVal
jtar (MBZ _ v) = Right v
jtar (MJmp r)  = Left r
jtar (MJmpI v) = Right v


-- get the variables used in an instruction:
varsof :: Ins -> [VReg]
varsof i = case (dst i) of
             (Just r) -> let vs = src i
                         in
                           if (elem r vs) then vs else (r:vs)

             Nothing  -> src i

--
-- determine whether a virtual register is used in an instruction:
--
usedby :: VReg -> Ins -> Bool
usedby v (Load r r' r'')   = (v == r) || (v == r') || (v == r'')
usedby v (LoadI r r' _)    = (v == r) || (v == r')
usedby v (Mov r r')        = (v == r) || (v == r')
usedby v (MovI r _)        = v == r
usedby v (Store r r' r'')  = (v == r) || (v == r') || (v == r'')
usedby v (StoreI r r' _)   = (v == r) || (v == r')

usedby _ Interrupt         = False
usedby _ IMR_Set           = False
usedby _ IMR_Clr           = False

usedby v (MBZ r _)         = v == r
usedby v (MTst r r')       = (v == r) || (v == r') 
usedby v (MJmp r)          = v == r
usedby _ (MJmpI _)         = False

usedby v (MAdd r r' r'')   = (v == r) || (v == r') || (v == r'')
usedby v (MAddI r r' _)    = (v == r) || (v == r')
usedby v (MSub r r' r'')   = (v == r) || (v == r') || (v == r'')
usedby v (MSubI r r' _)    = (v == r) || (v == r')
usedby v (MMul r r' r'')   = (v == r) || (v == r') || (v == r'')
usedby v (MDiv r r' r'')   = (v == r) || (v == r') || (v == r'')

usedby v (MCmp r r' r'')   = (v == r) || (v == r') || (v == r'')
usedby v (MCmpI r r' _)    = (v == r) || (v == r')
usedby v (MAnd r r' r'')   = (v == r) || (v == r') || (v == r'')
usedby v (MAndI r r' _)    = (v == r) || (v == r')
usedby v (MOr r r' r'')    = (v == r) || (v == r') || (v == r'')
usedby v (MOrI r r' _)     = (v == r) || (v == r')

usedby _ Nop               = False


--
-- make variable substitutions in a given instruction:
--
-- ... is there really no better way to do this?
--
alpha :: [(VReg, MReg)] -> Ins -> Ins

alpha rs (Load v v' v'')   = let r   = mrlookup v rs
                                 r'  = mrlookup v' rs
                                 r'' = mrlookup v'' rs
                             in
                               Load r r' r''

alpha rs (LoadI v v' v'')      = let r   = mrlookup v rs
                                     r'  = mrlookup v' rs
                                 in
                                   LoadI r r' v''

alpha rs (Mov v v')            = let r   = mrlookup v rs
                                     r'  = mrlookup v' rs
                                 in
                                   Mov r r'

alpha rs (MovI v v')           = let r   = mrlookup v rs
                                 in
                                   MovI r v'

alpha rs (Store v v' v'')      = let r   = mrlookup v rs
                                     r'  = mrlookup v' rs
                                     r'' = mrlookup v'' rs
                                 in
                                   Store r r' r''

alpha rs (StoreI v v' v'')     = let r   = mrlookup v rs
                                     r'  = mrlookup v' rs
                                 in
                                   StoreI r r' v''

alpha rs Interrupt             = Interrupt
alpha rs IMR_Set               = IMR_Set
alpha rs IMR_Clr               = IMR_Clr

alpha rs (MBZ v v')            = let r = mrlookup v rs
                                 in
                                   MBZ r v'

alpha rs (MTst v v')           = let r  = mrlookup v rs
                                     r' = mrlookup v' rs
                                  in
                                    MTst r r'

alpha rs (MJmp v)             = let r  = mrlookup v rs
                                in
                                  MJmp r

alpha _ (MJmpI v)             = MJmpI v


alpha rs (MAdd v v' v'')      = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                    r'' = mrlookup v' rs
                                in
                                  MAdd r r' r''

alpha rs (MAddI v v' v'')     = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                in
                                  MAddI r r' v''

alpha rs (MSub v v' v'')      = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                    r'' = mrlookup v' rs
                                in
                                  MSub r r' r''

alpha rs (MSubI v v' v'')     = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                in
                                  MSubI r r' v''

alpha rs (MMul v v' v'')      = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                    r'' = mrlookup v' rs
                                in
                                  MMul r r' r''

alpha rs (MDiv v v' v'')      = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                    r'' = mrlookup v' rs
                                in
                                  MDiv r r' r''

alpha rs (MCmp v v' v'')      = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                    r'' = mrlookup v' rs
                                in
                                  MCmp r r' r''

alpha rs (MCmpI v v' v'')     = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                in
                                  MCmpI r r' v''

alpha rs (MAnd v v' v'')      = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                    r'' = mrlookup v' rs
                                in
                                  MAnd r r' r''

alpha rs (MAndI v v' v'')     = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                in
                                  MAndI r r' v''

alpha rs (MOr v v' v'')       = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                    r'' = mrlookup v' rs
                                in
                                  MOr r r' r''

alpha rs (MOrI v v' v'')      = let r   = mrlookup v rs
                                    r'  = mrlookup v' rs
                                in
                                  MOrI r r' v''

alpha _ Nop                = Nop



mrlookup :: VReg -> [(VReg, MReg)] -> VReg
mrlookup v rs =
  case (lookup v rs) of
    (Just m) -> MR m
    Nothing  -> v


--                          --
-- FLOW ANALYSIS STRUCTURES --
--                          --

-- basic block:
data BBlock = BB [Label] InsSeq

instance Show BBlock where
 show (BB ls is) = '{':'\n':
                   (foldr (\x -> \s -> x ++ ':':'\n':s) "" ls) ++
                   (ppt is) ++ "\n}\n"

--
-- use the assumption that labels are unique;
-- this simplifies the identification of vertices
--
-- NOTE: this also makes the tacit, simplifying assumption,
-- that label synonyms  will always appear in the same order;
--
instance Eq BBlock where
  b == b'  = (labelsof b) == (labelsof b')

labelsof :: BBlock -> [Label]
labelsof (BB ls _) = ls

blklen :: BBlock -> Int
blklen (BB _ is) = foldinsseq (\_ -> \n -> n + 1) 0 is



--
-- control flow edge;
--
-- this is something more than an edge in your usual directed graph;
-- in accordance with the semantics of SAL, and the manner in which
-- basic blocks are constructed, exactly one of the following should hold
-- for any block B:
--
--   (1) there is exactly one outgoing edge from B;
--   (2) there are exactly two outgoing edges from B (conditional branch);
--   (3) B ends in a register-targeted jump;
-- 
-- the edges in the graph are constructed to reflect these exhaustive
-- and mutually exclusive possibilities, which somewhat simplifies
-- the construction and analysis of flow graphs.
--
-- (2010.11.11) Schulz
-- 
-- 'CSW' (context switch), corresponds to a jump with a register 
-- argument.  Rather than construct all possible jump destinations
-- (which, in general, will be very numerous), the special 'CSW' edge
-- will, for now, signal the register allocator to spill most or all registers.
--
-- (2010.11.04) Schulz
--
data CFEdge = CFE BBlock BBlock        -- sequential edge
            | CFB BBlock BBlock BBlock -- conditional branch to blk in third arg
            | CSW BBlock BBlock        -- context switch, with implicit return
            deriving (Show, Eq)

-- unannotated control flow graph of an instruction sequence:
type CFG = ([BBlock], [CFEdge])

--
-- control flow graph, annotated with live registers;
-- first list of registers indicates live-in registers;
-- second list of regsiters indicates live-out registers;
--
type CFG_L = ([(BBlock, ([VReg], [VReg]))], [CFEdge])


-- output of the SAL phase, analyzed and annotated:
newtype SAL_AN = SAL_AN (DataSect, (Label, [(Label, CFG_L)])) deriving Show


instance PPT SAL_AN where
  ppt (SAL_AN (ds, (l, gs))) = data_sect_header ++
                               '\n':'\n':
                               (foldr
                                 (\d -> \s -> (ppt d) ++ '\n':s) "\n\n" ds) ++
                               code_sect_header ++ '\n':
                               init_label ++ ':':(ppt (init_code))
                               ++ '\n':'\t':"jmp " ++ l ++ '\n':'\n':
                               (foldr (\g -> \s -> (show g) ++ '\n':s) "" gs)


  

-- THIS IS THE END OF THE FILE --
