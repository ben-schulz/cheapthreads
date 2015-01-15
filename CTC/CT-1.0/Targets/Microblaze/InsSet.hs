--
-- this is ~/cheapthreads/ctc_working/CT-1.0/Targets/Microblaze/InsSet.hs
--
-- abstract syntax and utilities for the Microblaze assembly language
--
-- put here (2010.11.18)
--
-- Schulz
--

module Targets.Microblaze.InsSet where


import CT.PPT

import Data.Int

type MB_Label = String

data MB_ASM = MBS MB_Ins MB_ASM
            | MBL MB_Label MB_ASM
            | MBNil
            deriving Show

instance PPT MB_ASM where
  ppt (MBS i is) = ppt i ++ '\n':(ppt is)
  ppt (MBL l is) = l ++ ':':'\n':(ppt is)
  ppt MBNil      = ""


mbinscat :: MB_ASM -> MB_ASM -> MB_ASM
mbinscat (MBS i is) is' = MBS i (mbinscat is is')
mbinscat (MBL l is) is' = MBL l (mbinscat is is')
mbinscat MBNil is'      = is'



--
-- Microblaze words:
--
data MBVal = MB_Byte Int8
           | MB_HalfWord Int16
           | MB_Word Int32
           | MB_Label MB_Label
           deriving Show


zerow :: MBVal
zerow = MB_Word 0

onew :: MBVal
onew = MB_Word 1

instance PPT MBVal where
  ppt (MB_Byte n)     = show n
  ppt (MB_HalfWord n) = show n
  ppt (MB_Word n)     = show n
  ppt (MB_Label l)    = l

data MBSize = ByteSize
            | HalfWordSize
            | WordSize
            deriving Show

instance PPT MBSize where
  ppt ByteSize     = "byte"
  ppt HalfWordSize = "halfword"
  ppt WordSize     = "word"


--
-- Microblaze registers:
--
data MBReg = PC
           | MB_fake String -- dummy register, for debugging
           | MB_r0
           | MB_r1
           | MB_r2
           | MB_r3
           | MB_r4
           | MB_r5
           | MB_r6
           | MB_r7
           | MB_r8
           | MB_r9
           | MB_r10
           | MB_r11
           | MB_r12
           | MB_r13
           | MB_r14
           | MB_r15
           | MB_r16
           | MB_r17
           | MB_r18
           | MB_r19
           | MB_r20
           | MB_r21
           | MB_r22
           | MB_r23
           | MB_r24
           | MB_r25
           | MB_r26
           | MB_r27
           | MB_r28
           | MB_r29
           | MB_r30
           | MB_r31
           deriving Show

rzer0 :: MBReg
rzer0 = MB_r0

instance PPT MBReg where
  ppt r = drop 3 (show r)



--
-- the Microblaze instruction set;
--
-- register arguments appear in the same order as in the well-formed
-- assembly statement;
--
-- string after the '_' corresponds to the instruction pneumonic:
--
data MB_Ins  = MB_add MBReg MBReg MBReg
             | MB_addc MBReg MBReg MBReg
             | MB_addk MBReg MBReg MBReg
             | MB_addkc MBReg MBReg MBReg

             | MB_addi MBReg MBReg MBVal
             | MB_addic MBReg MBReg MBVal
             | MB_addik MBReg MBReg MBVal
             | MB_addikc MBReg MBReg MBVal

             | MB_and MBReg MBReg MBReg
             | MB_andi MBReg MBReg MBVal
             | MB_andn MBReg MBReg MBReg
             | MB_andni MBReg MBReg MBVal

             | MB_beq MBReg MBReg
             | MB_beqd MBReg MBReg
             | MB_beqi MBReg MBVal
             | MB_beqid MBReg MBVal
             | MB_bge MBReg MBReg
             | MB_bged MBReg MBReg
             | MB_bgei MBReg MBVal
             | MB_bgeid MBReg MBVal
             | MB_bgt MBReg MBReg
             | MB_bgtd MBReg MBReg
             | MB_bgti MBReg MBVal
             | MB_bgtid MBReg MBVal
             | MB_ble MBReg MBReg
             | MB_bled MBReg MBReg
             | MB_blei MBReg MBVal
             | MB_bleid MBReg MBVal
             | MB_blt MBReg MBReg
             | MB_bltd MBReg MBReg
             | MB_blti MBReg MBVal
             | MB_bltid MBReg MBVal
             | MB_bne MBReg MBReg
             | MB_bned MBReg MBReg
             | MB_bnei MBReg MBVal
             | MB_bneid MBReg MBVal
             | MB_br MBReg
             | MB_bra MBReg
             | MB_brd MBReg
             | MB_brad MBReg
             | MB_brld MBReg MBReg
             | MB_brald MBReg MBReg

             | MB_bri MBVal
             | MB_brai MBVal
             | MB_brid MBVal
             | MB_braid MBVal
             | MB_brlid MBReg MBVal
             | MB_bralid MBReg MBVal

             | MB_brk MBReg MBReg
             | MB_brki MBReg MBVal

             | MB_bsrl MBReg MBReg MBReg
             | MB_bsra MBReg MBReg MBReg
             | MB_bsll MBReg MBReg MBReg

             | MB_bsrli MBReg MBReg MBVal
             | MB_bsrai MBReg MBReg MBVal
             | MB_bslli MBReg MBReg MBVal

             | MB_cmp MBReg MBReg MBReg
             | MB_cmpu MBReg MBReg MBReg

             | MB_fadd MBReg MBReg MBReg
             | MB_frsub MBReg MBReg MBReg

             | MB_fmul MBReg MBReg MBReg
             | MB_fdiv MBReg MBReg MBReg

             -- the following seven need a '.' before the last two characters
             -- in the code when put to formatted strings:
             | MB_fcmpun MBReg MBReg MBReg
             | MB_fcmplt MBReg MBReg MBReg
             | MB_fcmpeq MBReg MBReg MBReg
             | MB_fcmple MBReg MBReg MBReg
             | MB_fcmpgt MBReg MBReg MBReg
             | MB_fcmpne MBReg MBReg MBReg
             | MB_fcmpge MBReg MBReg MBReg

             | MB_flt MBReg MBReg
             | MB_fint MBReg MBReg
             | MB_fsqrt MBReg MBReg

             -- get from the FSL interface:
             | MB_get MBReg Int
             | MB_getd MBReg Int

             | MB_idiv MBReg MBReg MBReg
             | MB_idivu MBReg MBReg MBReg

             | MB_imm

             | MB_lbu MBReg MBReg MBReg
             | MB_lbui MBReg MBReg MBVal
             | MB_lhu MBReg MBReg MBReg
             | MB_lhui MBReg MBReg MBVal
             | MB_lw MBReg MBReg MBReg
             | MB_lwi MBReg MBReg MBVal

             | MB_mfs MBReg MBReg
             | MB_msrclr MBReg MBVal
             | MB_msrset MBReg MBVal
             | MB_mts MBReg MBVal

             | MB_mul MBReg MBReg MBReg
             | MB_mulhu MBReg MBReg MBReg
             | MB_mulhsu MBReg MBReg MBReg
             | MB_muli MBReg MBReg MBVal

             | MB_or MBReg MBReg MBReg
             | MB_ori MBReg MBReg MBVal

             | MB_pcmpbf MBReg MBReg MBReg
             | MB_pcmpne MBReg MBReg MBReg

             -- put to FSL interface:
             | MB_put MBReg Int
             | MB_putd MBReg MBReg Int
             | MB_rsub MBReg MBReg MBReg
             | MB_rsubc MBReg MBReg MBReg
             | MB_rsubk MBReg MBReg MBReg
             | MB_rsubkc MBReg MBReg MBReg

             | MB_rsubi MBReg MBReg MBVal
             | MB_rsubic MBReg MBReg MBVal
             | MB_rsubik MBReg MBReg MBVal
             | MB_rsubikc MBReg MBReg MBVal

             | MB_rtbd MBReg MBVal
             | MB_rtid MBReg MBVal
             | MB_rted MBReg MBVal
             | MB_rtsd MBReg MBVal

             | MB_sb MBReg MBReg MBReg
             | MB_sbi MBReg MBReg MBVal
             | MB_sext16 MBReg MBReg

             | MB_sh MBReg MBReg MBReg
             | MB_shi MBReg MBReg MBVal

             | MB_sra MBReg MBReg
             | MB_src MBReg MBReg
             | MB_sw MBReg MBReg MBReg
             | MB_swi MBReg MBReg MBVal

             | MB_wdc MBReg MBReg
             | MB_wic MBReg MBReg

             | MB_xor MBReg MBReg MBReg
             | MB_xori MBReg MBReg MBVal
             deriving Show


argsof :: MB_Ins -> [Either MBVal MBReg]

argsof (MB_add r r' r'') = map Right [r, r', r'']
argsof (MB_addc r r' r'') = map Right [r, r', r'']
argsof (MB_addk r r' r'') = map Right [r, r', r'']
argsof (MB_addkc r r' r'') = map Right [r, r', r'']

argsof (MB_addi r r' r'') = [Right r, Right r', Left r'']
argsof (MB_addic r r' r'') = [Right r, Right r', Left r'']
argsof (MB_addik r r' r'') = [Right r, Right r', Left r'']
argsof (MB_addikc r r' r'') = [Right r, Right r', Left r'']

argsof (MB_and r r' r'') = map Right [r, r', r'']
argsof (MB_andi r r' r'') = [Right r, Right r', Left r'']
argsof (MB_andn r r' r'') = map Right [r, r', r'']
argsof (MB_andni r r' r'') = [Right r, Right r', Left r'']

argsof (MB_beq r r') = map Right [r, r']
argsof (MB_beqd r r') = map Right [r, r']

argsof (MB_beqi r r') = [Right r, Left r']
argsof (MB_beqid r r') = [Right r, Left r']

argsof (MB_bge r r') = map Right [r, r']
argsof (MB_bged r r') = map Right [r, r']

argsof (MB_bgei r r') = [Right r, Left r']
argsof (MB_bgeid r r') = [Right r, Left r']

argsof (MB_bgt r r') = map Right [r, r']
argsof (MB_bgtd r r') = map Right [r, r']

argsof (MB_bgti r r') = [Right r, Left r']
argsof (MB_bgtid r r') = [Right r, Left r']

argsof (MB_ble r r') = map Right [r, r']
argsof (MB_bled r r') = map Right [r, r']
argsof (MB_blei r r') = [Right r, Left r']
argsof (MB_bleid r r') = [Right r, Left r']
argsof (MB_blt r r') = map Right [r, r']
argsof (MB_bltd r r') = map Right [r, r']

argsof (MB_blti r r') = [Right r, Left r']
argsof (MB_bltid r r') = [Right r, Left r']

argsof (MB_bne r r') = map Right [r, r']
argsof (MB_bned r r') = map Right [r, r']
argsof (MB_bnei r r') = [Right r, Left r']
argsof (MB_bneid r r') = [Right r, Left r']

argsof (MB_br r) = [Right r]
argsof (MB_bra r) = [Right r]
argsof (MB_brd r) = [Right r]
argsof (MB_brad r) = [Right r]

argsof (MB_brld r r') = map Right [r, r']
argsof (MB_brald r r') = map Right [r, r']

argsof (MB_bri r) = [Left r]
argsof (MB_brai r) = [Left r]
argsof (MB_brid r) = [Left r]
argsof (MB_braid r) = [Left r]

argsof (MB_brlid r r') = [Right r, Left r']
argsof (MB_bralid r r') = [Right r, Left r']

argsof (MB_brk r r') = [Right r, Right r']
argsof (MB_brki r r') = [Right r, Left r']

argsof (MB_bsrl r r' r'') = map Right [r, r', r'']
argsof (MB_bsra r r' r'') = map Right [r, r', r'']
argsof (MB_bsll r r' r'') = map Right [r, r', r'']

argsof (MB_bsrli r r' r'') = [Right r, Right r', Left r'']
argsof (MB_bsrai r r' r'') = [Right r, Right r', Left r'']
argsof (MB_bslli r r' r'') = [Right r, Right r', Left r'']

argsof (MB_cmp r r' r'') = [Right r, Right r', Right r'']
argsof (MB_cmpu r r' r'') = [Right r, Right r', Right r'']

argsof (MB_fadd r r' r'') = [Right r, Right r', Right r'']
argsof (MB_frsub r r' r'') = [Right r, Right r', Right r'']

argsof (MB_fmul r r' r'') = [Right r, Right r', Right r'']
argsof (MB_fdiv r r' r'') = [Right r, Right r', Right r'']

argsof (MB_fcmpun r r' r'') = map Right [r, r', r'']
argsof (MB_fcmplt r r' r'') = map Right [r, r', r'']
argsof (MB_fcmpeq r r' r'') = map Right [r, r', r'']
argsof (MB_fcmple r r' r'') = map Right [r, r', r'']
argsof (MB_fcmpgt r r' r'') = map Right [r, r', r'']
argsof (MB_fcmpne r r' r'') = map Right [r, r', r'']
argsof (MB_fcmpge r r' r'') = map Right [r, r', r'']

argsof (MB_flt r r') = [Right r, Right r']
argsof (MB_fint r r') = [Right r, Right r']
argsof (MB_fsqrt r r') = [Right r, Right r']

-- not quite, but fuck repetitive data entry:
argsof (MB_get r _) = [Right r]
argsof (MB_getd r _) = [Right r]

argsof (MB_idiv r r' r'') = map Right [r, r', r'']
argsof (MB_idivu r r' r'') = map Right [r, r', r'']

argsof MB_imm = []

argsof (MB_lbu r r' r'') = map Right [r, r', r'']
argsof (MB_lbui r r' r'') = [Right r, Right r', Left r'']
argsof (MB_lhu r r' r'') = map Right [r, r', r'']
argsof (MB_lhui r r' r'') = [Right r, Right r', Left r'']

argsof (MB_lw r r' r'') = map Right [r, r', r'']
argsof (MB_lwi r r' r'') = [Right r, Right r', Left r'']

argsof (MB_mfs r r') = [Right r, Right r']
argsof (MB_msrclr r r') = [Right r, Left r']
argsof (MB_msrset r r') = [Right r, Left r']
argsof (MB_mts r r') = [Right r, Left r']

argsof (MB_mul r r' r'') = [Right r, Right r', Right r'']
argsof (MB_mulhu r r' r'') = [Right r, Right r', Right r'']
argsof (MB_mulhsu r r' r'') = [Right r, Right r', Right r'']
argsof (MB_muli r r' r'') = [Right r, Right r', Left r'']

argsof (MB_or r r' r'') = [Right r, Right r', Right r'']
argsof (MB_ori r r' r'') = [Right r, Right r', Left r'']

argsof (MB_pcmpbf r r' r'') = [Right r, Right r', Right r'']
argsof (MB_pcmpne r r' r'') = [Right r, Right r', Right r'']

argsof (MB_put r _) = [Right r]
argsof (MB_putd r r' _) = [Right r, Right r']

argsof (MB_rsub r r' r'') = [Right r, Right r', Right r'']
argsof (MB_rsubc r r' r'') = [Right r, Right r', Right r'']
argsof (MB_rsubk r r' r'') = [Right r, Right r', Right r'']
argsof (MB_rsubkc r r' r'') = [Right r, Right r', Right r'']

argsof (MB_rsubi r r' r'') = [Right r, Right r', Left r'']
argsof (MB_rsubic r r' r'') = [Right r, Right r', Left r'']
argsof (MB_rsubik r r' r'') = [Right r, Right r', Left r'']
argsof (MB_rsubikc r r' r'') = [Right r, Right r', Left r'']

argsof (MB_rtbd r r') = [Right r, Left r']
argsof (MB_rtid r r') = [Right r, Left r']
argsof (MB_rted r r') = [Right r, Left r']
argsof (MB_rtsd r r') = [Right r, Left r']

argsof (MB_sb r r' r'') = [Right r, Right r', Right r'']
argsof (MB_sbi r r' r'') = [Right r, Right r', Left r'']

argsof (MB_sext16 r r') = [Right r, Right r']

argsof (MB_sh r r' r'') = [Right r, Right r', Right r'']
argsof (MB_shi r r' r'') = [Right r, Right r', Left r'']

argsof (MB_sra r r') = [Right r, Right r']
argsof (MB_src r r') = [Right r, Right r']

argsof (MB_sw r r' r'') = [Right r, Right r', Right r'']
argsof (MB_swi r r' r'') = [Right r, Right r', Left r'']

argsof (MB_wdc r r') = [Right r, Right r']
argsof (MB_wic r r') = [Right r, Right r']

argsof (MB_xor r r' r'') = [Right r, Right r', Right r'']
argsof (MB_xori r r' r'') = [Right r, Right r', Left r'']


instance PPT MB_Ins where
  ppt a = let code = (drop 3 . head . words) (show a)
              args = argsof a
          in
            code ++ (foldr (\r -> \s -> ' ':(ppt r) ++ s) "" args)


-- THIS IS THE END OF THE FILE --
