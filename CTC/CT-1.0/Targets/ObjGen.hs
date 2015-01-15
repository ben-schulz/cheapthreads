--
-- this is ~/cheapthreads/CTC/CT-1.0/Targets/ObjGen.hs
--
-- Top-level switch for generating object code from the SAL intermediate phase.
--
-- put here 2010.11.19
--
-- Schulz
--

module Targets.ObjGen where

import Targets.Microblaze.InsSet
import Targets.Microblaze.Selector

import RSI.SAL.Syntax

import CT.PPT

data Obj = MB_ASM MB_ASM
         deriving Show

instance PPT Obj where
  ppt (MB_ASM p) = ppt p

objgen :: Arch -> SAL -> Obj
objgen t (SAL (_, (_, ps))) =

  case t of
    MB -> MB_ASM (foldr (\p -> \p' -> mbinscat p p') MBNil (map mb_select ps))


--         --
-- TARGETS --
--         --

data Arch = MB           -- Microblaze
          | Other        -- something else?
          deriving Show



-- THIS IS THE END OF THE FILE --
