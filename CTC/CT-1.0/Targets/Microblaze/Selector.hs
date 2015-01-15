--
-- this is ~/cheapthreads/ctc_working/CT-1.0/Targets/Microblaze/Selector.hs
--
-- Instruction selector for transliterating the SAL intermediate representation
-- into native Microblaze assembly.
--
-- put here (2010.11.18)
--
-- Schulz
--

module Targets.Microblaze.Selector where

import Targets.Microblaze.InsSet
import RSI.SAL.Syntax

import Data.Int

mb_select :: InsSeq -> MB_ASM
mb_select (Semi i is)    = (mbinscat (mb_ins_map i) (mb_select is))
mb_select (Labeled l is) = MBL l (mb_select is)
mb_select Nil            = MBNil


mb_ins_map :: Ins -> MB_ASM

mb_ins_map i@(Load r r' r'') =

  let rD = tombreg r
      rA = tombreg r'
      rB = tombreg r''
  in

  case (isize i) of

    ByteSize     -> MBS (MB_lbu rD rA rB) MBNil

    HalfWordSize -> MBS (MB_lhu rD rA rB) MBNil

    WordSize     -> MBS (MB_lw rD rA rB) MBNil


mb_ins_map i@(LoadI r r' r'') =

  let rD  = tombreg r
      rA  = tombreg r'
      imm = tombval r''
  in

  case (isize i) of

    ByteSize     -> MBS (MB_lbui rD rA imm) MBNil

    HalfWordSize -> MBS (MB_lhui rD rA imm) MBNil

    WordSize     -> MBS (MB_lwi rD rA imm) MBNil

mb_ins_map i@(Mov r r') =

  let rD = tombreg r
      rA = tombreg r'
  in

  case (isize i) of

    ByteSize     -> MBS (MB_add rD rA rzer0) MBNil

    HalfWordSize -> MBS (MB_add rD rA rzer0) MBNil

    WordSize     -> MBS (MB_add rD rA rzer0) MBNil

mb_ins_map i@(MovI r v) =

  let rD  = tombreg r
      imm = tombval v
  in

  case (isize i) of

    ByteSize     -> MBS (MB_addi rD rzer0 imm) MBNil

    HalfWordSize -> MBS (MB_addi rD rzer0 imm) MBNil

    WordSize     -> MBS (MB_addi rD rzer0 imm) MBNil

mb_ins_map i@(Store r r' r'') =

  let rD = tombreg r
      rA = tombreg r'
      rB = tombreg r''
  in

  case (isize i) of

    ByteSize     -> MBS (MB_sb rD rA rB) MBNil

    HalfWordSize -> MBS (MB_sh rD rA rB) MBNil

    WordSize     -> MBS (MB_sw rD rA rB) MBNil

mb_ins_map i@(StoreI r r' v) =

  let rD  = tombreg r
      rA  = tombreg r'
      imm = tombval v
  in

  case (isize i) of

    ByteSize     -> MBS (MB_sbi rD rA imm) MBNil

    HalfWordSize -> MBS (MB_shi rD rA imm) MBNil

    WordSize     -> MBS (MB_swi rD rA imm) MBNil

-- STUBBED --
mb_ins_map Interrupt = MBS (MB_msrclr rzer0 zerow) MBNil
mb_ins_map IMR_Set   = MBS (MB_msrclr rzer0 zerow) MBNil
mb_ins_map IMR_Clr   = MBS (MB_msrclr rzer0 zerow) MBNil

mb_ins_map i@(MBZ r v) =

  let rA  = tombreg r
      imm = tombval v
  in
    MBS (MB_beqi rA imm) MBNil

-- STUBBED --
mb_ins_map i@(MTst r r') =

  let rD  = tombreg r
      rA  = tombreg r'
      cmp = MB_cmp rD rA rzer0
  in
    MBS cmp MBNil

mb_ins_map i@(MJmp r) =

  let rB  = tombreg r
  in
    MBS (MB_br rB) MBNil


-- STUBBED --
mb_ins_map i@(MJmpI v) =

  let imm = tombval v
  in
    MBS (MB_bri imm) MBNil


mb_ins_map i@(MAdd r r' r'') =

  let rD = tombreg r
      rA = tombreg r'
      rB = tombreg r''
  in
    MBS (MB_add rD rA rB) MBNil


mb_ins_map i@(MAddI r r' v) =

  let rD  = tombreg r
      rA  = tombreg r'
      imm = tombval v
  in
    MBS (MB_addi rD rA imm) MBNil


mb_ins_map (MSub r r' r'') =

  let rD  = tombreg r
      rA  = tombreg r'
      rB  = tombreg r''
  in
    MBS (MB_rsub rD rB rA) MBNil


mb_ins_map (MSubI r r' v) =

  let rD  = tombreg r
      rA  = tombreg r'
      imm = tombval v
      ng  = MB_cmp rD rD rzer0
      sb  = MB_rsubi rD rA imm
  in
    MBS sb (MBS ng MBNil)

mb_ins_map (MMul r r' r'') =

  let rD  = tombreg r
      rA  = tombreg r'
      rB  = tombreg r''
  in
    MBS (MB_mul rD rA rB) MBNil

mb_ins_map (MDiv r r' r'') =

  let rD  = tombreg r
      rA  = tombreg r'
      rB  = tombreg r''
  in
    MBS (MB_idiv rD rA rB) MBNil

mb_ins_map (MCmp r r' r'') =

  let rD  = tombreg r
      rA  = tombreg r'
      rB  = tombreg r''
  in
    MBS (MB_cmp rD rA rB) MBNil

mb_ins_map (MCmpI r r' v) =

  let rD  = tombreg r
      rA  = tombreg r'
      imm = tombval v
  in
    MBS (MB_rsubi rD rA imm) MBNil

mb_ins_map (MAnd r r' r'') =

  let rD  = tombreg r
      rA  = tombreg r'
      rB  = tombreg r''
  in
    MBS (MB_and rD rA rB) MBNil

mb_ins_map (MAndI r r' v) =

  let rD  = tombreg r
      rA  = tombreg r'
      imm = tombval v
  in
    MBS (MB_andi rD rA imm) MBNil

mb_ins_map (MOr r r' r'') =

  let rD  = tombreg r
      rA  = tombreg r'
      rB  = tombreg r''
  in
    MBS (MB_or rD rA rB) MBNil

mb_ins_map (MOrI r r' v) =

  let rD  = tombreg r
      rA  = tombreg r'
      imm = tombval v
  in
    MBS (MB_ori rD rA imm) MBNil


mb_ins_map Nop = MBS (MB_bne rzer0 rzer0) MBNil


--
-- THIS IS A STUB
--
-- for use while I lay down a scaffolding for code generation,
-- and work out all the details of mapping high-level types to
-- the correct sizes, etc.
--

isize :: Ins -> MBSize
isize _ = WordSize


-- THIS IS ALSO A STUB --
-- (for above reasons) --
tombval :: SVal -> MBVal
tombval (Num n) = MB_Word ((fromInteger . toInteger) n)
tombval (Adr l) = MB_Label l

tombreg :: VReg -> MBReg
tombreg (MR (MReg n)) =

  case n of
    0  -> MB_r0
    1  -> MB_r1
    2  -> MB_r2
    3  -> MB_r3
    4  -> MB_r4
    5  -> MB_r5
    6  -> MB_r6
    7  -> MB_r7
    8  -> MB_r8
    9  -> MB_r9
    10 -> MB_r10
    11 -> MB_r11
    12 -> MB_r12
    13 -> MB_r13
    14 -> MB_r14
    15 -> MB_r15
    16 -> MB_r16
    17 -> MB_r17
    18 -> MB_r18
    19 -> MB_r19
    20 -> MB_r20
    21 -> MB_r21
    22 -> MB_r22
    23 -> MB_r23
    24 -> MB_r24
    25 -> MB_r25
    26 -> MB_r26
    27 -> MB_r27
    28 -> MB_r28
    29 -> MB_r29
    30 -> MB_r30
    31 -> MB_r31

tombreg x = MB_fake (show x)

-- THIS IS THE END OF THE FILE --
