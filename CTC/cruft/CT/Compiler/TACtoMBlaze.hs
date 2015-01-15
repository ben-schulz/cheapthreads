module CT.Compiler.TACtoMBlaze where 

import CT.Compiler.ThreeAddressCode

{-
 - Conventions for using this
 - Goal is to produce an assembly string/file that has the following features:
 - Register File called "regfile" (label to memory segment)
 - Stack File called "stack" (label to memory segment)
 - Main section called "main" (label to main spot)
 - Halt label referencing itself
-}
tacToString :: TacCommand -> String
 --PushReg Register
tacToString (PushReg r) =
      (loadReg r 3) ++   --Load register procedure
      "lwi r3 r3 0\n" ++ --Load register in r3 to itself, dereference
      "swi r3 r1 0\n" ++ --Store the contents of r3 on the stack
      "addi r1 r1 4\n"   --Increment the stack pointer by 4 to keep it word aligned and correct

--Base register is reg1 and is going into register 3
--Length/offset is reg2 and is going to register 4
--r6 is the counter 
tacToString (PushMem reg1 reg2) = 
      (loadReg reg1 3) ++ --Load Register procedure
      "lwi r3 r3 0\n" ++  --Load reg1 r3
      (loadReg reg2 4) ++ --Load Register procedure
      "lwi r4 r4 0\n" ++  --Load reg2 in r4
      "addi r6 r0 0\n"++  --Zero out r6 for counter
      "lwi r7 r3 r6\n"++  --Load the memory item at base register + counter offset r4 into r7
      "sw r7 r1\n"    ++  --Store the contents of r7 into the stackpointer location
      "addi r6 r6 4\n"++  --Increment the counter r6
      "addi r1 r1 4\n"++  --Increment the stack pointer
      "sub r8 r4 r6\n"++  --Get the difference between the counter and the len reg r4
      "blei r8 -20\n"++   --If the difference is still positive, jump back 5 instructions to loop
      "nop\n"             --Nop as required for a branch, I think. :)

tacToString (PopReg (VR r)) =
      "addi r3 r0 regfile\n" ++ -- Load the base address of the regfile memspace in r3
      "addi r3 r3 " ++ show(4*r) ++"\n" ++ -- add the register offset value to regfile
      "lwi r4 r1 0\n" ++ --Load the memory location at the stack pointer into r4
      "swi r4 r3 0\n" ++ --Store the memory at the stack pointer (r4) in the location r3 (+0)
      "addi r1 r1 -4\n"  --Decrement the stack pointer by 4 (word aligned)


tacToString (MoveMem reg1 reg2 reg3) = 
      (loadReg reg1 3) ++ --Load reg1 into r3
      "lwi r3 r3 0\n" ++
      (loadReg reg2 4) ++ --Load reg2 into r4
      "lwi r4 r4 0\n" ++
      (loadReg reg3 5) ++ --Load reg3 into r5
      "lwi r5 r5 0\n" ++
      "addi r6 r0 0\n"++  --Zero out r6 for counter use
      "lwi r7 r4 r6\n"++  --Load the memory location at r4 + counter (word aligned) into r7
      "swi r7 r3 r6\n"++  --Store the word in r7 at counter+base destination register
      "addi r6 r6 4\n"++  --Add 4 to the counter (word aligned)
      "sub r8 r5 r6\n"++  --Store the difference between r5 and r6 in r8 (counter vs length)
      "blei r8 -16\n"++   --If the difference is less than or equal to zero, jump back 4 ins.
      "nop\n"             --Nop required after a jump

tacToString (Constant (VR r) const) =
      "addi r3 r0 regfile\n" ++                -- Load the location of the regfile into r3
      "addi r3 r3 " ++ show(r*4) ++ "\n" ++    -- Add the offset for the VR
      "addi r4 r0 " ++ show(const) ++ "\n" ++  -- Add put the constant in r4
      "swi r4 r3 0\n"                          -- Store the constant in r4 in r3, or VR r

--Not sure if you'd ever want to set the SP to an arbitrary value? :-/
tacToString (Constant SP const) =
      "addi r1 r0 0\n" ++                      -- Set r1 to zero YIKES :(
      "addi r1 r0 " ++ show(const) ++ "\n"     -- Add the constant to the (zero val) SP

tacToString (Labeled (Label lbl)) =
      lbl ++ ":\n"                             -- Print this out as a label

tacToString (Unary reg1 op reg2) =
      case op of
          Deref -> (loadReg reg2 3) ++         -- load reg2 into r3
                   "lwi r3 r3 0\n"  ++         -- Dereference r3 to r3
                   "lwi r3 r3 0\n"  ++         -- Dereferenced r3/reg2
                   (loadReg reg1 4) ++         -- Load reg1 to r4
                   "swi r3 r4 0\n"             -- Stored Dereferenced reg2 in r4/reg1

          Neg   -> (loadReg reg2 3) ++         -- Load reg2 to r3
                   "lwi r3 r3 0\n"  ++         -- Deref r3 to r3
                   "muli r3 r3 -1\n"++         -- mult r3 by -1
                   (loadReg reg1 4) ++         -- Load reg1 into r4
                   "swi r3 r4 0\n"             -- Storing neg r3 in r4 which is reg1


tacToString (Binary reg1 reg2 op reg3) =
      case op of
          Plus -> (loadReg reg2 3) ++          -- Load reg2 to r3
                  "lwi r3 r3 0\n" ++
                  (loadReg reg3 4) ++          -- Load reg3 to r4
                  "lwi r4 r4 0\n" ++
                  (loadReg reg1 5) ++          -- Load reg1 to r5
                  "add r3 r3 r4\n" ++          -- Add r3 and r4, put in r3
                  "swi r3 r5 0\n"              -- Store r3 at memloc in r5

          Minus ->(loadReg reg2 3) ++          -- load reg2 to r3
                  "lwi r3 r3 0\n" ++
                  (loadReg reg3 4) ++          -- load reg3 to r4
                  "lwi r4 r4 0\n" ++
                  (loadReg reg1 5) ++          -- load reg1 to r5
                  "muli r4 r4 -1\n" ++         -- mult r4 by -1 for subtraction
                  "add r3 r3 r4\n" ++          -- add r3 to r4, place in r3 (subtraction step)
                  "swi r3 r5 0\n"              -- store result in memloc at r3 (reg2)
          IsEqual->(loadReg reg2 3) ++          -- load reg2 to r3
                  "lwi r3 r3 0\n" ++
                  (loadReg reg3 4) ++          -- load reg3 to r4
                  "lwi r4 r4 0\n" ++
                  (loadReg reg1 5) ++          -- load reg1 to r5
                  "rsub r6 r4 r3\n" ++          -- subtract r4 and r3 and store in r6
                  "bnei r6 20\n" ++             -- if r6 is not zero (aka r4 and r3 are not eq) jump ahead
                  "nop\n" ++
                  "addi r7 r0 1\n" ++          -- Set r7 to 1 (true)
                  "swi r7 r3 0\n"  ++          -- Store the one into reg1's space in regfile 
                  "bri 12\n" ++                -- Jump past the last ins in this command
                  "nop\n" ++
                  "addi r7 r0 0\n" ++          -- Set r7 to 0 (false)
                  "swi r7 r3 0\n"            -- Store the one into reg1's space in regfile
          GrtrThan->(loadReg reg2 3) ++          -- load reg2 to r3
                  "lwi r3 r3 0\n" ++
                  (loadReg reg3 4) ++          -- load reg3 to r4
                  "lwi r4 r4 0\n" ++
                  (loadReg reg1 5) ++          -- load reg1 to r5
                  "rsub r6 r4 r3\n" ++          -- subtract r4 and r3 and store in r6
                  "blei r6 20\n" ++             -- if r6 is <= zero (aka r4 and r3 are not eq) jump ahead
                  "nop\n" ++
                  "addi r7 r0 1\n" ++          -- Set r7 to 1 (true)
                  "swi r7 r3 0\n"  ++          -- Store the one into reg1's space in regfile 
                  "bri 12\n" ++                -- Jump past the last ins in this command
                  "nop\n" ++
                  "addi r7 r0 0\n" ++          -- Set r7 to 0 (false)
                  "swi r7 r3 0\n"            -- Store the one into reg1's space in regfile
          LessThan->(loadReg reg2 3) ++          -- load reg2 to r3
                  "lwi r3 r3 0\n" ++
                  (loadReg reg3 4) ++          -- load reg3 to r4
                  "lwi r4 r4 0\n" ++
                  (loadReg reg1 5) ++          -- load reg1 to r5
                  "rsub r6 r4 r3\n" ++          -- subtract r4 and r3 and store in r6
                  "bgei r6 20\n" ++             -- if r6 is >= zero (aka r4 and r3 are not eq) jump ahead
                  "nop\n" ++
                  "addi r7 r0 1\n" ++          -- Set r7 to 1 (true)
                  "swi r7 r3 0\n"  ++          -- Store the one into reg1's space in regfile 
                  "bri 12\n" ++                -- Jump past the last ins in this command
                  "nop\n" ++
                  "addi r7 r0 0\n" ++          -- Set r7 to 0 (false)
                  "swi r7 r3 0\n"            -- Store the one into reg1's space in regfile

tacToString (Move reg1 reg2) =
      (loadReg reg1 3) ++                      -- loadRegister at reg1 in r3
      (loadReg reg2 4) ++                      -- load register at reg2 in r4
      "lwi r4 r4 0\n" ++                       -- deref r4 into r4
      "add r5 r0 r4\n" ++                      -- add 0 to r4 and put it into 5 (a move)
      "swi r5 r3 0\n"                          -- store r5 into memloc in r3

tacToString (BZero r (Label lbl)) =
      (loadReg r 3) ++                         -- load r into r3
      "lwi r3 r3 0\n" ++                       -- dref r3 into itself 
      "beqi r3 " ++ lbl ++ "\n"                -- branch to the label lbl

tacToString (Jump (Label lbl)) =             
      "jmp " ++ lbl ++ "\n"                    -- One ins, jump to lbl

tacToString (Comment str) =
      "# " ++ str ++ "\n"                      -- Print hte string in the asm with a # for comment

tacToString c = error $ "Can't handle this: " ++ show c   -- Fail out

compReg :: TacCommand -> Int -> Int
compReg x num =
 case x of
   (PushReg  r) -> (lgst2 num r)
   (PushMem r len) -> (lgst2 num r)
   (PopReg r) -> (lgst2 num r)
   (MoveMem reg1 reg2 len) -> (lgst3 num reg1 reg2)
   (Constant r const) -> (lgst2 num r)
   (Labeled (Label lbl)) -> num
   (Unary reg1 op reg2) -> (lgst3 num reg1 reg2)
   (Binary reg1 reg2 op reg3) -> (lgst2 (lgst3 num reg1 reg2) reg3)
   (Move reg1 reg2) -> (lgst3 num reg1 reg2)
   (BZero r (Label lbl)) -> (lgst2 num r)
   (Jump (Label lbl)) -> num
   (Comment str) -> num

countReg :: [TacCommand] -> Int -> Int
countReg [] num = num
countReg (x:xs) num = countReg xs (compReg x num) --This really twigs my brain for some reason 

tacListProc :: [TacCommand] -> String
tacListProc [] = ""
tacListProc (x:xs) = (tacToString x) ++ (tacListProc xs)


tacToMBlaze :: [TacCommand] -> String
tacToMBlaze coms = result
  where
    words = (countReg coms 0)
    regfile = ".global main\n\nregfile:\n\n.word " ++ show(words) ++ "\n\n" --Make a regfile section
    stack = "stack:\n\n .word 2048\n\n"                     --Make a stack section of 2KB
    main = "main:\n\naddi r1 r0 stack\n\n" ++ (tacListProc coms) ++ "\n\n" --Set the stack pointer and dump the Mblaze here
    footer = "halt: brai halt"                               --Halt section, jump to itself               
    result = regfile ++ stack ++ main ++ footer             --Return all this stuck together

--For the memory footer, we have a label to jump to and have our vars on the stack
--r5 gets len, r4 gets src mem base, r3 gets dest mem base, r6 gets counter 



--Load a register by taking the virtual rep of it and return a string representing assembly
loadReg :: Register -> Int -> String
loadReg (VR r) num =
    "addi "++reg++" r0 regfile\n" ++                 --First load the regfile's location into reg
    "addi "++reg++" "++reg++" "++show(4*r) ++ "\n"   --Add the offset for the VR to the regfile loc
  where
    reg = "r" ++ show(num)

loadReg (SP) num =
    "addi "++reg++" r0 r1\n" ++                      --SP case, load the value of SP into reg
    "nop\n"                                          --Nop so these are the same length
  where
    reg = "r" ++ show(num)

popstack = "addi r1 r1 -4\n"                         --popstack decrements SP by -4

lgst2 :: Int -> Register -> Int
lgst2 a b =
  case b of
    SP   -> a
    VR r -> if r > a then r else a

lgst3 :: Int -> Register -> Register -> Int
lgst3 a b c = lgst2 (lgst2 a b) c

