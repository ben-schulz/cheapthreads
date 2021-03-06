--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/DFun/WriteFSM.hs
--
-- output of concrete FSMLang syntax from the abstract machine
-- produced by the defunctionalizer
--
-- put here 2010.03.31
--
-- Schulz
--

module CT.DFun.WriteFSM where

import CT.DFun.FSM
import CT.Syntax

--
-- top-level call to the object code generator:
--
writefsm :: FSMealy -> String
writefsm (((sigs, mems), chans), (d, ts)) =

  top_banner ++

  generics_banner ++

  generics ++

  ports_banner ++

  connections_banner ++

  mems_banner ++

  (write_mems mems) ++

  channels_banner ++

  (write_chans chans) ++

  sigs_banner ++

  (write_sigs sigs) ++

  (write_initial global_init) ++

  (write_trans d ts) ++

  fsmlang_eof


--
-- break-out functions for each of the fields:
--

write_sigs :: [FSMSignal] -> String
write_sigs sigs =

  -- print the signals:
  (foldr
    (\v -> \s ->
      (fst v) ++ ' ':(pptfsmty $ snd v) ++ ';':'\n':s
    )
      "" sigs
  )



write_mems :: [FSMMem] -> String
write_mems mems =

  -- this is a half-assed base-two logarithm that rounds up to ceil,
  -- to work around Haskell's obnoxious numeric typeclasses:
  --
  let log2' = \l -> \n -> let n' = div n 2
                          in
                            if n' == 0 then (l + 1) else log2' (l + 1) n'

      log2  = \n -> log2' 0 n
  in

  -- print the declared memories:
  (foldr
    (\(m, (z, t)) -> \s ->
      m ++ ',':(show $ sizeof t) ++ ',':(show $ log2 z) ++ ';':'\n':s
    )
      "" mems
  )



write_initial :: PC -> String
write_initial i = "\n\nINITIAL: " ++ (show i) ++ ";\n\n"

write_trans :: TransD -> [Trans] -> String
write_trans d ts =

  "\n\nTRANS:\n\n" ++

  -- print the transitions:
  (foldr
    (\t -> \s ->

      case t of
        (Left (i, i'))       -> (show i) ++ " -> " ++ (show i') ++
                                ' ':(ppttransduct d t) ++ '\n':'\n':s

        (Right (b, (i, i'))) -> (show i) ++ '|':(show b) ++
                                " -> " ++ (show i') ++ ' ':(ppttransduct d t) ++
                                '\n':'\n':s
    ) "" ts
  )

ppttransduct :: TransD -> Trans -> String
ppttransduct d t =
  case (d t) of

    r@(_:_) -> "where\n" ++

               '{':'\n':
               (
               foldr
               (\(x, e) -> \s ->

                 (show x) ++ "\' <= " ++ (show e) ++ '\n':s

               ) "" r

               ) ++ "}\n"

    []      -> ""

--
-- write out reactive signals as FSMLang channels:
--
-- this right now assumes only one argument per channel
-- constructor, which is reasonable for the present purposes
--
write_chans :: [CommSig] -> String
write_chans =

  foldr
  (\((ch, ts), (ch', ts')) -> \s ->

      case ts of
        (t:_) -> (ch ++ (pptfsmty t)) ++ ";\n" ++ s
        []    -> case ts' of
                 (t':_) -> (ch ++ (pptfsmty t')) ++ ";\n" ++ s
                 []     -> s

  ) ""


--
-- right now, we form types using the 'generics' mechanism
-- and a default integer width:
--
generics :: String
generics = data_width_label ++ ", integer, " ++ (show default_int_width)


--
-- form an FSM type declaration:
--
pptfsmty :: FSMTy -> String
pptfsmty CTIntTy  = ", std_logic_vector(0 to " ++
                    data_width_label ++
                    "-1)"

pptfsmty CTBoolTy = ", std_logic"
pptfsmty CTUnitTy = ", std_logic" 
pptfsmty _          = ", std_logic_vector(0 to " ++
                      data_width_label ++
                      "-1)"


--
-- CONSTANTS USED HERE
--


top_banner :: String
top_banner = "-- BEGIN CODE GENERATED BY THE CT COMPILER --\n\n\n\n"


generics_banner :: String
generics_banner = "\n\nGENERICS:\n\n"

ports_banner :: String
ports_banner = "\n\nPORTS:\n\n"

connections_banner :: String
connections_banner = "\n\nCONNECTIONS\n\n"

mems_banner :: String
mems_banner = "\n\nMEMS:\n\n"

channels_banner :: String
channels_banner = "\n\nCHANNELS:\n\n"

sigs_banner :: String
sigs_banner = "\n\nSIGS:\n\n"

fsmlang_eof :: String
fsmlang_eof = "\n\n-- END GENERATED CODE --"

-- THIS IS THE END OF THE FILE --
