module CT.Compiler.TacSemantics where

import CT.Compiler.TacM
import CT.Compiler.ThreeAddressCode




----------------------
-- Main entry point --
----------------------
go :: TacProg -> IO ()
go (TacProg cmds) = let
                       (initLabelMap,commands) = splitCommands 0 ((\ (Label l) -> error $ "undefined label " ++ l),cmds)
                       initCode                = (commands!!)
                       initPC                  = 0
                       initRegFile             = (\ r -> if r == SP then 1000000 else 0)
                       initMemory              = const 0
                    in
                       runTacM loop initCode initLabelMap initPC initRegFile initMemory

-- Strips labels and comments from the instruction stream, and returns the
-- modified instruction stream and a mapping from labels to code addresses.
splitCommands :: PC -> (LabelMap,[TacCommand]) -> (LabelMap,[TacCommand])
splitCommands n (labelMap,(Labeled l):cs) = splitCommands n ((\ l' -> if l == l' then n else labelMap l),cs)
splitCommands n (labelMap,(Comment _):cs) = splitCommands n (labelMap,cs)
splitCommands n (labelMap,c:cs)           = let
                                               (labelMap',cs') = splitCommands (n+1) (labelMap,cs)
                                            in
                                               (labelMap',c:cs')
splitCommands _ (labelMap,[])             = (labelMap,[])

--------------------------
-- "Fetch/execute" loop --
--------------------------
loop :: TacM ()
loop = do
          code      <- rdCodeTacM
          pc        <- getPCTacM
          let instr =  code pc
          exec instr
          loop

--------------------------------------------------------------------
-- Executes one instruction.                                      --
--------------------------------------------------------------------
exec :: TacCommand -> TacM ()
exec (PutStr s)                = do
                                  liftIOTacM $ putStrLn s
                                  updatePCTacM (+1)
                                  return ()
exec (PutReg r)                = do
                                  regFile <- getRegFileTacM
                                  let v   =  regFile r
                                  liftIOTacM $ print v
                                  updatePCTacM (+1)
                                  return ()
exec (Jump l)                  = do
                                  labelMap <- rdLabelMapTacM
                                  let pc'  =  labelMap l
                                  putPCTacM pc'
exec (Constant r i)            = do
                                  regFile <- getRegFileTacM
                                  putRegFileTacM (tweek r i regFile)
                                  updatePCTacM (+1)
                                  return ()
exec (BZero r l)               = do
                                  regFile   <- getRegFileTacM
                                  labelMap  <- rdLabelMapTacM
                                  pc        <- getPCTacM
                                  let v     = regFile r
                                  let pc'   = if v==0 then labelMap l else (pc+1)
                                  putPCTacM pc'
exec (MoveMem r1 r2 r3)        = do
                                  regFile  <- getRegFileTacM
                                  mem      <- getMemoryTacM
                                  let newmem = movemem mem (regFile r1) (regFile r2) (regFile r3)
                                  putMemoryTacM newmem
                                  updatePCTacM (+1)
                                  return ()
exec (ConstLabel r1 lbl)       = do
                                  regFile  <- getRegFileTacM
                                  labelMap <- rdLabelMapTacM
                                  putRegFileTacM (tweek r1 (labelMap lbl) regFile)
                                  updatePCTacM (+1)
                                  return ()
exec (Unary r1 Deref r2)       = do
                                  regFile <- getRegFileTacM
                                  mem     <- getMemoryTacM
                                  putRegFileTacM (tweek r1 (mem (regFile r2)) regFile) 
                                  updatePCTacM (+1)
                                  return ()
exec (Unary r1 Neg r2)         = do
                                  regFile <- getRegFileTacM
                                  putRegFileTacM (tweek r1 ((regFile r2) * (-1)) regFile)
                                  updatePCTacM (+1)
                                  return ()
exec (Binary r1 r2 Plus r3)    = do
                                  regFile <- getRegFileTacM
                                  putRegFileTacM (tweek r1 ((regFile r2) + (regFile r3)) regFile)
                                  updatePCTacM (+1)
                                  return ()
exec (Binary r1 r2 Minus r3)   = do
                                  regFile <- getRegFileTacM
                                  putRegFileTacM (tweek r1 ((regFile r2) - (regFile r3)) regFile) 
                                  updatePCTacM (+1)
                                  return ()
exec (Binary r1 r2 IsEqual r3) = do
                                  regFile <- getRegFileTacM
                                  let iseq = if (regFile r2) == (regFile r3) then 1 else 0
                                  putRegFileTacM (tweek r1 iseq regFile)
                                  updatePCTacM (+1)
                                  return ()
exec (Binary r1 r2 GrtrThan r3) = do
                                  regFile <- getRegFileTacM
                                  let iseq = if (regFile r2) > (regFile r3) then 1 else 0
                                  putRegFileTacM (tweek r1 iseq regFile)
                                  updatePCTacM (+1)
                                  return ()
exec (Binary r1 r2 LessThan r3) = do
                                  regFile <- getRegFileTacM
                                  let iseq = if (regFile r2) < (regFile r3) then 1 else 0
                                  putRegFileTacM (tweek r1 iseq regFile)
                                  updatePCTacM (+1)
                                  return ()
exec (Move r1 r2)              = do
                                  regFile  <- getRegFileTacM
                                  mem      <- getMemoryTacM
                                  let newmem = movemem mem (regFile r1) (regFile r2) 0 
                                  putMemoryTacM newmem
                                  updatePCTacM (+1)
                                  return ()
exec (PushReg r1)              = do
                                  regFile      <- getRegFileTacM
                                  mem          <- getMemoryTacM
                                  let memloc   = regFile SP
                                  let mem'     = tweek (regFile SP) (regFile r1) mem 
                                  let regFile' = tweek SP ((regFile SP) + 4) regFile 
                                  putMemoryTacM mem'
                                  putRegFileTacM regFile'
                                  updatePCTacM (+1)
                                  return ()
exec (PushMem r1 r2)           = do
                                  regFile  <- getRegFileTacM
                                  mem      <- getMemoryTacM
                                  let newmem = movemem mem (regFile SP) (regFile r1) (regFile r2)
                                  putMemoryTacM newmem
                                  updatePCTacM (+1)
                                  return ()
exec (PopReg r1)               = do
                                  regFile  <- getRegFileTacM
                                  mem      <- getMemoryTacM
                                  let memval = mem (regFile SP)
                                  let regFile' = tweek SP ((regFile SP) - 4) regFile 
                                  let regFile'' = tweek r1 memval regFile 
                                  putRegFileTacM regFile''
                                  updatePCTacM (+1)
                                  return ()

exec c                         = error $ "FIXME: I don't know how to handle this: " ++ show c

--tweek proper needs to reapplied to all this stuff so we have less repetition of code. :)
tweek x v f                    = \ n -> if x==n then v else f n

-- Shall we make this word aligned, or not?  I don't think it makes a difference.
-- I'm going to go with word-alignedness for now, but this can be easily changed.
-- Actually it should make a difference pending on how the caller uses word aligned offsets.
movemem :: Memory -> Loc -> Loc -> Word -> Memory
movemem mem l1 l2 0    = newmem 
                         where newmem   = \x -> if x == l1 then (mem l2) else (mem x)
movemem mem l1 l2 off  = movemem (newmem) (l1+4) (l2+4) (off-4)
                         where newmem   = \x -> if x == l1 then (mem l2) else (mem x)

