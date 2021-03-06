--
-- this is ~/cheapthreads/ctc/ct/defunctionalizer/WriteFSM.hs
--
-- functions for writing the output of the defunctionalizer
-- in FSMLang concrete syntax
--
-- see Agron's "Domain-Specific Language for HW/SW Co-Design for FPGAs"
-- for details of the syntax
--
-- put here 08.04.09 Schulz
--


module CT.Defunctionalizer.WriteFSM where

import Data.Char
import Control.Monad
import CT.Syntax
import CT.Defunctionalizer.DefunTypes
import CT.Defunctionalizer.PreDefun
import CT.Defunctionalizer.BMonad

--           --
-- TOP LEVEL --
--           --

--
-- old version with old types:
--
{-
writeFSM ::  KState -> [RRule] -> String
writeFSM k r = top_header ++
               internal_state_sig_block ++
               generics_block ++
               ports_block ++
               connections_block ++
               memories_block ++
               signal_header ++ (mkSignals k) ++
               initial_block ++
               trans_header ++
               (transitions r) ++
               end_block ++
               "\n"
-}

--writeFSMPlus ::  KStatePlus -> [RRulePlus] -> String
--writeFSMPlus ::  KStatePlus -> [Transition] -> String

writeFSMPlus ::  SysConfig -> String
writeFSMPlus (k, m, r) =
  top_header ++
  internal_state_sig_block ++
  generics_block ++
  ports_block ++
  connections_block ++
  memories_block ++ (memories m) ++
  signal_header ++ (mkSignals k) ++
  initial_block ++
  trans_header ++
  (transitions r) ++
  end_block ++
  "\n"
               

--                --
-- PROGRAM BLOCKS --
--                --

--
-- a default header
--

top_header :: String
top_header = "--\n-- CODE AUTOMATICALLY GENERATED BY CT DEFUNCTIONALIZER\n\n"

--
-- current- and next-state signals names
--
-- here we simply adopt the naming convention from Agron's paper
--
internal_state_sig_block :: String
internal_state_sig_block = "CS: current_state;\nNS: next_state;\n\n"

--
-- generics, i.e. compile time constants
--
-- for now, we use the convention of 32-bit integers
--
generics_block :: String
generics_block = "GENERICS:\nINT_WIDTH, integer, 32;\n\n"

--
-- ports block
--
ports_block :: String
ports_block = "PORTS:\n\n"

--
-- connections block
--
connections_block :: String
connections_block = "CONNECTIONS:\n\n"

--
-- memories block
--
memories_block :: String
memories_block = "MEMS:\n\n"

memories :: [Mem] -> String
memories ms = foldr
                (\(Mem m) -> \s -> (m ++
                                    ", " ++ default_dWidth ++
                                    ", " ++ default_aWidth ++ ";\n") ++
                                    s)
              "\n\n" ms


--
-- these address and data widths are arbitrarily chosen for now
--
-- 2009.11.16 Schulz
--
default_dWidth :: String
default_dWidth = "16"

default_aWidth :: String
default_aWidth = "16"

--
-- 'INITIAL' i.e. 'initial state' block of the program
--

initial_block :: String
initial_block = "INITIAL: " ++ init_label ++ ";\n\n"

--
-- signals i.e states block;
--
-- these correspond to the states of K
--

signal_header :: String
signal_header = "SIGS:\n"


--
-- declare the signals corresponding to state-bound identifiers
-- declared in the source code:
--
-- see log (2009.11.12) for explanation of the conventions
--
mkSignals :: KStatePlus -> String
mkSignals ((x, (V v)):vs) = 
  let cs  = words x
      id  = if (take 2 x) == "__" then mkSigIdent $ unwords cs
--            else mkSigIdent $ unwords $ init cs
            else mkSigIdent $ unwords cs
      ty  = last cs  -- put here for future use, after typechecker is fixed
      dec = (mkSigIdent id) ++ ", " ++ default_fsm_type_label ++ ";\n"
  in
    dec ++ mkSignals vs

mkSignals vs@(_:_) = error "improperly initialized list passed to code " ++
                           "generator: " ++ (show vs)

mkSignals [ ] = "\n"

{-

--
-- old version with old types; this is horribly written code,
-- and now deprecated
--
-- 2009.11.12 Schulz
--
mkSignals :: KState -> String
mkSignals k = let ls = map fst k
                  defaults = dropWhile (not . ((==) "__") . (take 2)) ls
                  users = takeWhile (not . ((==) "__") . (take 2)) ls
                  ts = map (last . words) users
                  z  = zip (map mkSigIdent ls) ts
              in
                (foldr (\ (x, y) -> \ s -> s ++ x ++ ", " ++ y ++ ";\n") "\n" z)
                  ++
                (foldr (\ x -> \ s ->
                  s ++ x ++ ", std_logic_vector(0 to INT_WIDTH - 1);\n")
                  "\n" defaults)
                  ++ "\n"
-}

mkSigIdent :: CtsIdent -> String
mkSigIdent x = foldr f "" x
               where
                 f u v = if ((not . isSpace) u)
                         then
                           (u:v)
                         else
                           ('_':v)

--
-- 'TRANS' i.e. transition logic block of program
--

trans_header :: String
trans_header = "TRANS:\n\n"

--transitions :: [RRulePlus] -> String
transitions :: [Transition] -> String
transitions = foldr ((++) . writeTransPlus) ""

--
-- we are presently working under the assumption
-- that the transition function is WELL-DEFINED and
-- DETERMINISTIC, i.e. each program counter value
-- should transition to one and only one new value
--
-- 24.04.09 Schulz
--

--
-- similar to old version, but extended to handle recent additions,
-- i.e. if-then-else 'values' and conditional loops
--
-- 2009.11.12 Schulz
--
--
--writeTransPlus :: RRulePlus -> String
--

writeTransPlus :: Transition -> String

-- generate unconditional transition:
writeTransPlus (Left ((pc1, k1), (pc2, k2))) =
  let ids   = map (fillIdent . fst) k1    -- this assumes k1 == k2
      ks    = zip ids $ zip (map snd k1) (map snd k2)
      ts    = foldr ((++) . (\ (x, (u, v)) ->
                               if u == v
                               then ""
                               else
                                 case (runB v) of
                                   (DFMemWrite m a w) ->
                                       m ++ "[" ++ (show a) ++ "]" ++
                                       "\'  <=   " ++ (show w) ++ "\n"

                                 -- special translation for the 'weird' values
                                   DFUnit -> x ++ "\'  <=  " ++ "0" ++ "\n"
                                   DFNil  -> x ++ "\'  <=  " ++ "0" ++ "\n"
                                   _ -> x ++ "\'  <=  " ++ (show v) ++ "\n"))

                "" ks
  in
    (writePC pc1) ++ 
    " -> " ++ (writePC pc2) ++
    "\n{\n" ++ ts ++ "}\n\n"

-- generate conditional transition:
writeTransPlus (Right (sent, ((pc1, k1), (pc2, k2)))) =
  let ids   = map (fillIdent . fst) k1    -- this assumes k1 == k2
      ks    = zip ids $ zip (map snd k1) (map snd k2)
      ts    = foldr ((++) . (\ (x, (u, v)) ->
                               if u == v
                               then ""
                               else
                                 case (runB v) of
                                   (DFMemWrite m a w) ->
                                       m ++ "[" ++ (show a) ++ "]" ++
                                       "\'  <=   " ++ (show w) ++ "\n"

                                   _ -> x ++ "\'  <=  " ++ (show v) ++ "\n"))

                "" ks
  in
    (writePC pc1) ++ 
    " | (" ++ (show sent) ++ ") " ++ -- add a guard for conditional transition
    " -> " ++ (writePC pc2) ++
    "\n{\n" ++ ts ++ "}\n\n"

{-
writeTransPlus ((pc1, k1), (pc2, k2)) =
  let ids   = map (fillIdent . fst) k1    -- this assumes k1 == k2
      ks    = zip ids $ zip (map snd k1) (map snd k2)
      guard = case (snd $ head k2) of
                (V v)     -> ""
                _         -> error "not done yet!"
      ts    = foldr ((++) . (\ (x, (u, v)) ->
                               if u == v
                               then ""
                               else x ++ "\'  <=  " ++ (show v) ++ "\n"))
                "" ks
  in
    (writePC pc1) ++ guard ++ 
    " -> " ++ (writePC pc2) ++
    "\n{\n" ++ ts ++ "}\n\n"
-}
  

{-
writeTrans :: RRule -> String
writeTrans ((pc1, k1), (pc2, k2)) =
  let ids = map (fillIdent . fst) k1    -- this assumes k1 == k2
      ks = zip ids $ zip (map snd k1) (map snd k2)
      ts = foldr ((++) . (\ (x, (u, v)) ->
                            if u == v
                            then ""
                            else x ++ "\'  <=  " ++ (show v) ++ "\n"))
           "" ks
  in
  (writePC pc1) ++ " -> " ++ (writePC pc2) ++ "\n{\n" ++ ts ++ "}\n\n"
  
-}

--
-- remove spaces from identifiers in intermediate representation
--
fillIdent :: String -> String
fillIdent = foldr f ""
            where
              f x y = if (isSpace x) then '_':y else x:y
--
-- a trailer for the generated code
--
end_block :: String
end_block = "\n\n-- END OF GENERATED CODE --\n"
-- THIS IS THE END OF THE FILE --
