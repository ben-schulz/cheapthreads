--
-- this ~/cheapthreads/CTC/CT-1.0/CT/DFun/DFun.hs
--
-- top-level entry point for the defunctionalizer,
-- and passes used to form the FSMLang headers
--
--
-- put here 2010.02.18
--
-- Schulz
--

module CT.DFun.DFun where

import CT.DFun.FSM
import CT.DFun.DFunR
import CT.DFun.DFunK

import CT.DFun.DFunOpt
import CT.DFun.WriteFSM

import CT.Syntax
import CT.INAST

import CT.PPT

--
-- defunctionalization starts here:
--

dfun :: INProg -> FSMealy
dfun (INProg ((INFunDec ((_, _), (_, p)), []), (dats, mons))) =

  let denv          = mkdconenv dats
      (sigs', mems) = getstateds denv mons
      sigs          = sigs' ++ (get_lbvs p)
      chans         = siftsigs dats
      (d, ts)       = dfunr p
  in
    (((sigs, mems), chans), (d, ts))



--
-- formatted output of the transition rules for the FSM:
--
pptfsm :: FSMealy -> String
pptfsm (((sigs, mems), _), (d, ts)) =

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
  
  ++

  -- print the signals:
  (foldr
    (\v -> \s ->
      (fst v) ++ ' ':(ppt $ snd v) ++ ';':'\n':s
    )
      "" sigs
  )

  ++

  -- print the transitions:
  (foldr
    (\t -> \s ->

      case t of
        (Left (i, i'))       -> (show i) ++ " -> " ++ (show i') ++ 
                                ' ':(ppttransd d t) ++ '\n':'\n':s

        (Right (b, (i, i'))) -> (show i) ++ '|':(show b) ++
                                " -> " ++ (show i') ++ ' ':(ppttransd d t) ++
                                '\n':'\n':s
    ) "" ts
  )


ppttransd :: TransD -> Trans -> String
ppttransd d t =
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


--                                             --
-- INITIALIZATION PASSES AND UTILITY FUNCTIONS -- 
--                                             --


--
-- collect all declared data types into
-- a single environment:
--
type DEnv = CTIdent -> [(TyCon, [CTTy])]

mkdconenv :: [DataDec] -> DEnv
mkdconenv =

  foldr
  (\(DataDec (TyCon c) _ cs) -> \f ->

    tweek f c cs

  ) (\_ -> [])


--
-- collect lambda-bound variables into signals:
--

get_lbvs :: INAST -> [FSMSignal]
get_lbvs (CTAppIN a a' _)    = let vs  = get_lbvs a
                                   vs' = get_lbvs a'
                               in
                                 vs ++ vs'

get_lbvs (CTRecAppIN a a' _) = let vs  = get_lbvs a
                                   vs' = get_lbvs a'
                               in
                                 vs ++ vs'

get_lbvs (CTLamIN x a t')     = let vs    = get_lbvs a

                                    domof = \x -> case x of
                                                    (CTAbsTy a _) -> domof a
                                                    a             -> a

                                    t = domof t'

                                in
                                  (x, t):vs

get_lbvs (CTBindIN a a' _)   = let vs  = get_lbvs a
                                   vs' = get_lbvs a'
                               in
                                 vs ++ vs'
                                      
get_lbvs (CTNullBindIN a a' _) = let vs  = get_lbvs a
                                     vs' = get_lbvs a'
                                 in
                                   vs ++ vs'

get_lbvs (CTReturnIN a _)     = get_lbvs a

get_lbvs (CTPutIN _ a _)      = get_lbvs a
                                      

get_lbvs (CTReadIN _ a _)     = get_lbvs a

get_lbvs (CTWriteIN _ a a' t) = let vs  = get_lbvs a
                                    vs' = get_lbvs a'
                                in
                                  vs ++ vs'

get_lbvs (CTStepIN a _)      = get_lbvs a


{-
-- CHANGE THIS:
-- later, as in, when we get rid of the list argument:
-- (2010.03.25) Schulz
--
get_lbvs (CTFixIN (CTLamIN _ a _) as _) = let vs  = get_lbvs a
                                              vs' = concat $ map get_lbvs as
                                          in
                                              vs ++ vs'
-}
get_lbvs (CTFixIN (CTLamIN _ a _) _) = get_lbvs a

get_lbvs (CTFixAppIN a as _)         = let vs  = get_lbvs a
                                           vs' = concat $ map get_lbvs as
                                       in
                                         vs ++ vs'


get_lbvs (CTSignalIN a _)     = get_lbvs a


get_lbvs (CTPrim1aryIN _ a _) = get_lbvs a

get_lbvs (CTPrim2aryIN op a a' t) = let vs  = get_lbvs a
                                        vs' = get_lbvs a'
                                    in
                                      vs ++ vs'

get_lbvs (CTPrim3aryIN _ a a' a'' t) = let vs   = get_lbvs a
                                           vs'  = get_lbvs a'
                                           vs'' = get_lbvs a''
                                       in
                                         vs ++ vs' ++ vs''

get_lbvs (CTBranchIN a a' a'' t) = let vs   = get_lbvs a
                                       vs'  = get_lbvs a'
                                       vs'' = get_lbvs a''
                                   in
                                     vs ++ vs' ++ vs''

get_lbvs (CTCaseIN a alts t) = let vs   = get_lbvs a
                                   vs'  = map get_patvs (map fst alts)
                                   vs'' = concat $ map get_lbvs (map snd alts)
                               in
                                 vs''
                                 -- error $ "finish case expressions in get_lbvs"

get_lbvs (CTPairIN a a' t) = let vs  = get_lbvs a
                                 vs' = get_lbvs a'
                             in
                               vs ++ vs'
                               
get_lbvs (CTGetReqIN x _) = get_lbvs x

-- anything else takes no expression-argument
get_lbvs x = []


--
-- collect the pattern variables from patterns
--
-- THIS IS A STUB
--
-- 2010.03.27 Schulz
--

get_patvs :: CTPat -> [FSMSignal]
get_patvs x = []



--
-- collect all 'StateT' and 'MemT' declarations into FSM state components:
--
-- returns a list of signals, and a list of memories
--
-- (why waste another pass through the dec list?)
--
getstateds :: DEnv -> [MonadDec] -> ([FSMSignal], [FSMMem])
getstateds denv =

  foldr
  (\d -> \(sigs, mems) ->

    case d of

      (CTStateT _ ss) -> (

                           foldr
                           (\(k, (x, t)) -> \(ls, ms) ->

                             case k of

                               -- we make the tacit assumption
                               -- that memory layers DO NOT
                               -- involve aggregate types,
                               -- though 'StateT' may:

                               StateL   -> case t of

                                             (CTConTy c _) -> (
                                                                (mkdsigs
                                                                  denv c x)
                                                                ++ ls,

                                                                ms
                                                              )

                                             _             -> ((x, t):ls, ms)

                               (MemL n) -> (ls, (x, (n, t)):ms)

                           ) (sigs, mems) ss

                         ) 

      _               -> (sigs, mems)

  ) ([], [])



--
-- make the signals for an aggregate-typed variable:
--
-- first argument: environment of declared data types;
-- second argument: the type constructor of a declared data type;
-- third argument: the variable identifier
--
mkdsigs :: DEnv -> TyCon -> CTIdent -> [FSMSignal]
mkdsigs denv (TyCon d) x =

  let cs = (denv d)
  in

    (conflagof x, conflagty):

    
    (

      foldr
      (\(c, ts) -> \ss ->

        snd
        (
          foldr
          (\t -> \(n, as) ->

            (n + 1,
            ((mkagident x c n), t):as)

          ) (1, []) ts

        )

      ) [] cs

    )


--
-- make a unique identifier for the signal corresponding
-- to one component of an aggregate value;
--
-- first argument: the aggregate value identifier
-- first argument: the constructor name
-- second argument: the index of the argument
--
mkagident :: CTIdent -> TyCon -> Int -> String
mkagident x (TyCon c) n = x ++ ' ':(c ++ ' ':(show n))


--
-- sift the reactive signals out of a list of data decs:
--
siftsigs :: [DataDec] -> [CommSig]
siftsigs =
  foldr
    (\x -> \xs ->

      case x of
        (SigDec _ cs) -> xs ++ cs
        _               -> xs
    )
      []


--
-- accessors for the signals produced by for an aggregate type:
--

--
-- the constructor flag:
--
conflagof :: CTIdent -> String
conflagof x = x ++ "__DCON"

conflagty :: CTTy
conflagty = CTIntTy

--
-- the nth argument of a given constructor:
--
dargof :: CTIdent -> TyCon -> Int -> String
dargof = mkagident


-- THIS IS THE END OF THE FILE --
