{-
	TODOS:: Test the Mempush methods
			Clean this crap up, it is pure nasty plumbing
			Finish implementing MoveMem to complete the implementation of TAC
			Test Test Test
			
			--Ian
-}

module CT.Compiler.TACtoMicroBlaze where
	
import CT.Compiler.ThreeAddressCode

iStackByte = "addi r1, r1, 1\n"
iStackWord = "addi, r1, r1, 4\n"
iPopWord = "subi, r1, r1, 4\n"

virtBase = 0x000000 --one meg for the VR's starting at zero
stackBase = 0x100000 --one meg for stack

--Memory address range of SPI memory in Spartan-3E starter board is 2MB 0x0 - 0x1FFFFF
--Memory address range for reserved Virtual registers s


registerLookupTable :: [(String, Maybe (Register))]
registerLookupTable =  [("r19", Nothing),("r20", Nothing),("r21", Nothing),("r22", Nothing),("r23", Nothing),("r24", Nothing),("r25", Nothing),("r26", Nothing),("r27", Nothing),("r28", Nothing),("r29", Nothing),("r30", Nothing),("r31", Nothing)]

--List of Strings that are Microblaze Assembly representing our TAC program
tacProgtoMicroBlaze :: [TacCommand] -> [String]
tacProgtoMicroBlaze (x:xs) = tacString:tacProgtoMicroBlaze(xs)
	where
		(tacString, _) = (tactoMicroBlaze x registerLookupTable)

tacProgtoMicroBlaze [] = []


tactoMicroBlaze :: TacCommand -> [(String , (Maybe (Register)))] -> (String ,[(String, (Maybe (Register)))])
tactoMicroBlaze (PushReg reg) table = if (lookupSec reg table) == Nothing then (upStr++outStr, table') else (outStr,table)
	where
		outStr = (mblazeStackPush (regstr, reg))
		(upStr,regstr,table') = (updateNecTable table reg)

tactoMicroBlaze (PushMem reg numval) table = if numval >= 4 then (outstr ++ nextstr, table'') else (outstr, table'')
	where
		(nextstr, table''') = (tactoMicroBlazeHelper (PushMem reg (numval-4)) tempReg table'')
		outstr = upStr1 ++ upStr2 ++ "lw " ++ regstr2 ++ ", " ++ regstr1 ++ ", r0\nsw " ++ regstr2 ++ ", " ++regstr1++", r0\n"
		suffix = if numval > 4 then "addi " ++ regstr1 ++ ", " ++ regstr1 ++ " 4\n" else ""
		(upStr2, regstr2, table'') = (updateNecTableNoLoad table' tempReg)
		tempReg = (VR (-1)) -- placeholder, we're never storing this
		(upStr1,regstr1,table') = (updateNecTable table reg)
		

tactoMicroBlaze (PopReg reg) table = if (lookupSec reg table) == Nothing then (upStr++outStr, table') else (outStr, table)
	where
		outStr = "lwi " ++ regstr ++ ", r1, r0\n" ++ iPopWord
		(upStr,regstr,table') = (updateNecTableNoLoad table reg)

--This is a nightmare, I think I need a monad....or something.
tactoMicroBlaze (MoveMem reg1 reg2 numval) table = ("# !!Movemem Unfinished!!", table)


tactoMicroBlaze (Constant reg numval) table = if (lookupSec reg table) == Nothing then (upStr++outStr, table') else (outStr, table)
	where
		outStr = "addi " ++ regstr ++ ", r0, " ++ (show numval) ++ "\n"
		(upStr,regstr,table') = (updateNecTableNoLoad table reg)

tactoMicroBlaze (Labeled (Label lbl)) table = (lbl ++ ":", table)

tactoMicroBlaze (Unary regdest Neg reg) table = (upStr ++ outStr, table'')
	where
		outStr = "rsub " ++ regdeststr ++ ", r0, " ++ regstr ++ "\n"
		upStr = upS1 ++ upS2
		(upS2,regdeststr, table'')	= (updateNecTableNoLoad table' regdest)
		(upS1,regstr,table') = (updateNecTable table reg)

tactoMicroBlaze (Unary regdest Deref reg) table = (upStr ++ outStr, table'')
	where
		outStr = "lw " ++ regdeststr ++ ", r0, " ++ regstr ++ "\n"
		upStr = upS1 ++ upS2
		(upS2,regdeststr, table'')	= (updateNecTableNoLoad table' regdest)
		(upS1,regstr,table') = (updateNecTable table reg)

tactoMicroBlaze (Binary regdest reg1 Plus reg2) table = (upS1 ++ upS2 ++ upS3 ++ outstr, table''')
	where
		outstr = "add " ++ regdeststr ++ ", " ++ regstr1 ++ ", " ++ regstr2 ++ "\n"
		(upS3,regdeststr, table''')	= (updateNecTableNoLoad table'' regdest)
		(upS2,regstr2, table'')	= (updateNecTable table' reg2)
		(upS1,regstr1,table') = (updateNecTable table reg1)

tactoMicroBlaze (Binary regdest reg1 Minus reg2) table = (upS1 ++ upS2 ++ upS3 ++ outstr, table''')
	where
		outstr = "sub " ++ regdeststr ++ ", " ++ regstr1 ++ ", " ++ regstr2 ++ "\n"
		(upS3,regdeststr, table''')	= (updateNecTableNoLoad table'' regdest)
		(upS2,regstr2, table'')	= (updateNecTable table' reg2)
		(upS1,regstr1,table') = (updateNecTable table reg1)



tactoMicroBlaze (Move regdest srcreg) table = (upS1 ++ upS2 ++ outstr, table'')
	where
		outstr = "add " ++ regdeststr ++ ", r0, " ++ regstr1 ++ "\n"
		(upS2,regdeststr, table'')	= (updateNecTableNoLoad table' regdest)
		(upS1,regstr1,table') = (updateNecTable table srcreg)

tactoMicroBlaze (BZero reg (Label lbl) ) table = (upStr ++ outstr, table')
	where
		outstr = "beqi " ++ regstr1 ++ ", " ++ lbl ++ "\n"
		(upStr,regstr1,table') = (updateNecTable table reg)
		
tactoMicroBlaze (Jump (Label lbl)) table = (outstr,table)
	where
		outstr = "bri " ++ lbl ++ "\n"

tactoMicroBlaze (Comment str) table = ("# " ++ str ++ "\n", table)


--When we need to load a value into a register before using it
mblazeRegSwap :: (String, Maybe (Register)) -> (String,Register) -> String
mblazeRegSwap (oldregstr, Just (oldvreg)) (newregstr, newvreg) = "swi " ++ oldregstr ++ ", r0, " ++ show (offsetVR oldvreg) ++ "\n"  ++ "lwi " ++ newregstr ++ "r0, " ++ show (offsetVR newvreg) ++"\n" -- Store word from live register into correct offset
mblazeRegSwap (oldregstr, Nothing) (newregstr, newvreg) = "lwi " ++ newregstr ++ ", r0, " ++ show (offsetVR newvreg) ++"\n" -- Simply load up Virtual Register from offset into real reg b/c we have no meaningful original data

--When we don't need to load a value into a register before using it
mblazeRegSwapNoLoad :: (String, Maybe (Register)) -> (String,Register) -> String
mblazeRegSwapNoLoad (oldregstr, Just (oldvreg)) (newregstr, newvreg) = "swi " ++ oldregstr ++ ", r0, " ++ show (offsetVR oldvreg) ++ "\n"  ++ "lwi " ++ newregstr ++ "r0, " ++ show (offsetVR newvreg) ++"\n" -- Store word from live register into correct offset
mblazeRegSwapNoLoad (oldregstr, Nothing) _ = "" -- If the spot has nothing, we're not going to load anything into it

mblazeStackPush :: (String,Register) -> String
mblazeStackPush (regstr, reg) = "swi " ++ regstr ++ ", r1, r0\n" ++ iStackWord


updateNecTable :: [(String, Maybe (Register))] -> Register -> (String, String, [(String, Maybe (Register))])
updateNecTable table SP = ("", "r1", table)
updateNecTable table reg = if (lookupSec reg table) == Nothing then (upStr,regstr, table') else ("",regstr,table)
	where
		upStr = (mblazeRegSwap (regstr,oldvreg) (regstr,reg))
		table' = (insertReg table reg)
		(regstr, oldvreg) = head table

updateNecTableNoLoad :: [(String, Maybe (Register))] -> Register -> (String, String, [(String, Maybe (Register))])
updateNecTableNoLoad table SP = ("", "r1", table)
updateNecTableNoLoad table reg = if (lookupSec reg table) == Nothing then (upStr, regstr, table') else ("",regstr, table)
	where
		upStr = (mblazeRegSwapNoLoad (regstr,oldvreg) (regstr,reg))
		table' = (insertReg table reg)
		(regstr, oldvreg) = head table


tactoMicroBlazeHelper :: TacCommand -> Register -> [(String, Maybe (Register))] -> (String, [(String, Maybe (Register))])
tactoMicroBlazeHelper (PushMem reg numval) tempReg table = if numval >= 4 then (outstr ++ nextstr, table'') else (outstr, table'')
	where
		(nextstr, table''') = (tactoMicroBlazeHelper  (PushMem reg (numval-4)) tempReg table'')
		outstr = upStr1 ++ upStr2 ++ "lw " ++ regstr2 ++ ", " ++ regstr1 ++ ", r0\nsw " ++ regstr2 ++ ", " ++regstr1++", r0\n"
		suffix = if numval > 4 then "addi " ++ regstr1 ++ ", " ++ regstr1 ++ " 4\n" else ""
		(upStr2, regstr2, table'') = (updateNecTableNoLoad table' tempReg)
		(upStr1,regstr1,table') = (updateNecTable table reg)

insertReg :: [(String, Maybe (Register))] -> (Register) -> [(String, Maybe (Register))]
insertReg table reg = body ++ (upreg:[])
	where
		upreg = (regstring, Just reg)
		body = tail table
		(regstring,vReg) = head table



updateTable :: (String, Maybe (Register)) -> [(String, Maybe (Register))] -> [(String, Maybe (Register))]
updateTable _ [] = []
updateTable (reg, mReg) xs = prefix ++ ((reg,mReg):[]) ++ suffix'
	where 
		  (suffix')		   = tail suffix
		  (prefix,suffix)  = break ((bMatch reg)) xs

--Register Utils
--Calculate's the offset of a particular Virtual register based on its number
--Offset is at least 4 bytes, base word is used for temp vars
offsetVR :: Register -> Int
offsetVR (VR a) = 4 * a + 4
offsetVR (GR _) = 1024 --predefined catchall for now

--Utils

--Will only be called when you know that the item is in there from a previous lookup
lookupSecCrashy :: Eq b => b -> [(a,b)] ->  a
lookupSecCrashy (vReg) ((a,b):xs) = if vReg == b then a else lookupSecCrashy vReg xs

lookupSec :: Eq b => b -> [(a, Maybe b)] ->  Maybe a
lookupSec _ [] = Nothing
lookupSec (vReg) ((a,Just b):xs) = if vReg == b then (Just a) else lookupSec vReg xs
lookupSec (vReg) ((a,Nothing):xs) = lookupSec vReg xs

bMatch :: String -> ((String, Maybe (Register)) -> Bool)
bMatch a = \(b,_) -> if a == b then True else False
