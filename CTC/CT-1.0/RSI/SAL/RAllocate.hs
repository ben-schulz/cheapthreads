--
-- this is ~/cheapthreads/CTC/CT-1.0/RSI/SAL/RAllocate.hs
--
-- a register allocator for the CT compiler
--
-- the current implementation uses a linear scan register allocation procedure,
-- as described in:
--
--   "Linear Scan Register Allocation" by Poletto and Sarkar, 1999.
--
-- put here 2010.11.03
--
-- Schulz
--

module RSI.SAL.RAllocate where


import RSI.SAL.FlowAnalysis
import RSI.SAL.Syntax
import RSI.Syntax

import Targets.ObjGen

import CT.PPT

import Data.List

--                 --
-- TOP LEVEL CALLS --
--                 --

--
-- allocate registers, and map virtual registers to machine registers
-- in the program text:
--
ralloc :: Target -> SAL_AN -> SAL
ralloc ((_, rs), rm) (SAL_AN (ds, (it, ps))) = 

      -- get numbered, folded representation of the CFGs:
  let ps'  = foldr
               (\(l, (vs, es)) -> \ps' ->
                 (fst (mknumbering l (map fst vs, es)):(ps'))) [] ps

      -- make register maps for each of the line-numbered CFGs:
      rms  = foldr (\(l, g) -> \ps' -> (mkrmap rs l g):ps') [] ps

      -- and apply the register maps:
      ps'' = foldr
               (\(p, m) -> \ps' -> (apprmap rs (m ++ rm) p):ps')
                 [] (zip ps' rms)
  in
    SAL (ds, (it, ps''))


-- generate the register map from variable liveness information:
mkrmap :: [MReg] -> Label -> CFG_L -> RMap
mkrmap ms st g =

  let g'      = mkswitches g          -- factor out context-switch edges
      vs      = fst g'
      cfg     = (map fst vs, snd g')  -- get CFG with liveness disregarded
      (p, bs) = mknumbering st cfg    -- get line numbers, block intervals

      -- pair up individual variables with their liveness intervals:
      ls      = lintzip (map (\(x, (y, _)) -> (x, y)) vs) bs

      -- and make the register map:
  in
    lscan ms ls


-- apply the register map:
apprmap :: [MReg] -> RMap -> InsSeq_N -> InsSeq

apprmap ms rm (Semi_N n i is) =

  if (chkspill n i rm)
  then
    inscat (mkspill n i ms rm) (apprmap ms rm is)
  else
    let vs = varsof i
        ms = map (\v -> rmlookup (v, (n, n)) rm) vs  -- get register mappings
        i' = alpha (zip vs ms) i                     -- and apply
    in
      Semi i' (apprmap ms rm is)

apprmap ms rm (Labeled_N l is) = Labeled l (apprmap ms rm is)
apprmap _ _ Nil_N              = Nil


--                 --
-- DATA STRUCTURES --
--                 --

--
-- a target includes an architecture, a list of registers,
-- and a possible base mapping, e.g. for certain dedicated registers:
--
type Target = ((Arch, [MReg]), RMap)



-- live intervals of a register:
type LInterval = (VReg, (Int, Int))


between :: Int -> (Int, Int) -> Bool
between n (n', n'') = (n' <= n) && (n <= n'')


-- ordering of liveness intervals by start point:
stord :: LInterval -> LInterval -> Ordering
stord (_, (n, _)) (_, (n', _))

  | (n < n')  = LT
  | (n > n')  = GT
  | otherwise = EQ


-- ordering of liveness intervals by end point:
enord :: LInterval -> LInterval -> Ordering
enord (_, (_, n)) (_, (_, n'))

  | (n < n')  = LT
  | (n > n')  = GT
  | otherwise = EQ


type RKey = (MReg, LInterval)
type RMap = [RKey]

-- ordering of keys by interval start point:
astord :: RKey -> RKey -> Ordering
astord (_, l) (_, l') = stord l l'

-- ordering of keys by interval endpoint
aenord :: RKey -> RKey -> Ordering
aenord (_, l) (_, l') = enord l l'

-- lookup the machine register mapped to a variable on a given interval:
rmlookup :: LInterval -> RMap -> MReg
rmlookup l@(v, (n, n')) rm =

  -- take any live interval matching the variable and containing the
  -- interval in question, endpoints inclusive:

  let p = \(_, (v', ns)) -> (v' == v) && (between n ns) && (between n' ns)
  in

  case (find p rm) of
    (Just m) -> fst m
    Nothing  -> error $ "failed lookup of live interval: " ++ (show l) ++ "\n\n"
                        ++ "in register map: " ++ (show rm)


-- association of blocks to their corresponding numbered intervals:
type LBlock = ([Label], (Int, Int))

-- instruction sequence, annotated with instruction numbers:
data InsSeq_N = Semi_N Int Ins InsSeq_N
              | Labeled_N Label InsSeq_N
              | Nil_N
              deriving Show

inscat_n :: InsSeq_N -> InsSeq_N -> InsSeq_N
inscat_n (Semi_N n i is) is'  = Semi_N n i (inscat_n is is')
inscat_n (Labeled_N l is) is' = Labeled_N l (inscat_n is is')
inscat_n Nil_N is'            = is'


--                     --
-- REGISTER ALLOCATION --
--                     --

--
-- linear scan of live intervals, allocating and spilling registers
-- according to active range, current location;
--
-- this is a functional adaptation of the algorithm presented in:
--
--   [Poletto and Sarkar, 1999]
--
-- first arg: number of machine registers available;
-- second arg: the list of variables and their liveness intervals;
--
lscan :: [MReg] -> [LInterval] -> RMap
lscan regs =

  let nr = length regs
  in

  fst . fst .

  (
    -- three accumulators, respectively:
    -- the current mapping, currently active intervals, free machine registers;

    foldr
    (\l@(_, (_, n)) -> \((rs, as), ms) -> 

      let (as', ms') = expire_lint n as  -- expire passed intervals
          usd        = length as'
          ms''       = ms ++ ms'         -- pass on free registers
      in
        if (usd >= nr)         -- if all registers currently occupied, spill
        then
          let (rs', as') = spill_lint l as rs
          in
            ((rs', as'), ms'')

        else                     -- otherwise, allocate a free register
          let m     = head ms''
              ms''' = tail ms''
          in
            (((m, l):rs, as'), ms''')

    ) (([], []), regs)

  )


expire_lint :: Int -> [RKey] -> ([RKey], [MReg])
expire_lint n ls =

  let ls' = sortBy aenord ls
      p   = \(_, (_, (_, n'))) -> n' <= n
  in
    (dropWhile p ls', map fst (takeWhile p ls'))


--
-- spill an active interval 
--
-- first argument: the interval requiring allocation;
-- second argument: currently active intervals:
-- third argument: the current register map, which may be altered;
--
-- return: new register map, new active accumulator, respectively
--
spill_lint :: LInterval -> [RKey] -> [RKey] -> ([RKey], [RKey])
spill_lint l@(v, (_, n')) ls rs =

  let sp  = last ls              -- get last interval from active
      ls' = init ls              -- drop last interval from active
      en  = (snd . snd . snd) sp -- endpoint of the last interval in active
      r'  = fst sp               -- register currently allocated to last
  in
    if (en > n')  -- if last interval ends after endpoint, then swap out
    then

      let l'  = (r', l)            -- allocate register from the spill
          l'' = (Spill v, snd sp)  -- mark the spill
          rs' = delete sp rs       -- drop old key for spill from the map
      in
        (sortBy aenord (l':l'':rs'), sortBy aenord (l':ls'))

    else             
      let l' = (Spill ((fst . snd) sp), l) -- otherwise, live interval spills
      in
        (l':rs, ls)



--                   -- 
-- LIVENESS ANALYSIS --
--                   -- 


-- aggregate block-wise liveness information into
-- variable-wise live intervals:
agglive :: [(BBlock, ([VReg], [VReg]))] -> [LBlock] -> [LInterval]
agglive vs bs =

  foldr
  (\(b, ls) -> \is ->

    let k = labelsof b
    in
    case (lookup k bs) of

      -- a variable is live in 'b' if it is live incoming:
      (Just i) -> let ins = fst ls
                  in
                    (zip ins (repeat i)) ++ is

      Nothing  -> error $ "in function agglive: no block labeled: " ++ (show k)

  ) [] vs


--                  --
-- PREPROCESS SCANS -- 
--                  --


--
-- traverse the flow graph, replacing 'CSW' edges with ordinary 'CFE' edges
-- and adding the appropriate spill-restore instructions necessary to effect
-- the context switch:
--
mkswitches :: CFG_L -> CFG_L

mkswitches (vs, es) = 

  let es' = foldr
            (\e -> \es' -> 

              case e of

                -- replace 'CSW' edges and add spill/restore instructions:
                (CSW b b') -> let (i, o)   = lkpblk b vs

                                  -- spill live registers in b before jump:
                                  c        = prespill b i

                                  -- restore live-in registers in b' after jump:
                                  c'       = postspill b' o
                              in
                                (CFE c c'):es'

                -- everything else remains invariant:
                _          -> e:es'

            ) [] es
  in 
    (vs, es')

--
-- top-level call: traverse the CFG and produce the numbered instruction seq,
-- together with the instruction intervals corresponding to the basic blocks
-- of the control flow graph:
--
mknumbering :: Label -> CFG -> (InsSeq_N, [LBlock])
mknumbering l (vs, es) =

  let v0 = case (labellkp l vs) of
             (Just v) -> v
             Nothing  -> error $ "invalid entry point: " ++ l
  in
    mkintervals v0 (vs, es)


-- traverse the CFG, numbering instructions in order of visitation:
mkintervals :: BBlock -> CFG -> (InsSeq_N, [LBlock])
mkintervals v0 g = (fst . fst) (dft_n v0 g Nil_N [] numblock 0)


-- number the instructions of a basic block, in the straightforward way:
numblock :: Int -> BBlock -> InsSeq_N
numblock n (BB _ is) = numscan n is

-- scan to number instruction for liveness interval computation:
numscan :: Int -> InsSeq -> InsSeq_N
numscan n (Semi i is)    = Semi_N n i (numscan (n + 1) is)
numscan n (Labeled l is) = Labeled_N l (numscan n is)
numscan _ Nil            = Nil_N


--                 --
-- REGISTER SPILLS --
--                 --

--
-- determine if any spills are required for a given instruction
--
chkspill :: Int -> Ins -> RMap -> Bool
chkspill n i rm = any isspill (mregsof n i rm)



--
-- get the machine registers used by a given instruction:
--
mregsof :: Int -> Ins -> RMap -> [MReg]
mregsof n i rm = foldr (\v -> \ms -> (rmlookup (v, (n, n)) rm):ms) [] (varsof i)

--
-- produce a very naive instruction sequence corresponding to a spill
-- of a given variable:
--
mkspill :: Int -> Ins -> [MReg] -> RMap -> InsSeq
mkspill n i ms rm =

  let ms' = ms \\ (mregsof n i rm)              -- don't spill used regs
      vs  = map spillvarof (filter isspill ms') -- get spilled vars
      rs  = take (length vs) ms'                -- pick out registers to spill

      pre = map spillr rs                       -- spill-out instructions
      pst = map unspillr rs                     -- spill-restore instructions
      i'  = alpha (zip vs rs) i                 -- make register substitutions 
  in
    foldr (\i -> \is -> Semi i is) Nil (pre ++ (i':pst))


--
-- NOTE: the functions below ('takespill', 'spillcans') are important,
-- but not presently in use, at least, not until a well-defined register
-- spilling heuristic can be settled on.
--
-- At least one heuristic is described in the log ('~/CT-1.0/RSI/rsi.log.txt'),
-- but it would introduce a huge amount of complexity that I don't think would
-- be profitable to tackle at right this moment.
--
-- (2010.11.17) Schulz

--
-- take some number of instructions affected by a register spill
-- from the front of an instruction sequence:
--
-- NOTE: this function has been put here expressly to allow for
-- easy changes to the spilling heuristics later
--
-- (2010.11.17) Schulz
--
--
-- first arg: maximum line number; if reached, the take stops;
-- second arg: the spilled register;
-- third arg: instruction sequence remaining;
--
-- returns: the candidate instructions, their endpoint, remaining instructions;
--
takespills :: Int -> VReg -> InsSeq_N -> (([Ins], Int), InsSeq_N)

takespills mx v (Semi_N n i is) =

  if (mx <= n) then (([], n), Semi_N n i is)
  else

  if (usedby v i)
  then 
    let ((ss, n'), is') = case is of
                           -- need this look-ahead to deal with number scheme
                           Nil_N -> (([], n), is)

                           _     -> takespills mx v is
    in
      ((i:ss, n'), is')
  else 
    (([], n), Semi_N n i is)

takespills mx v (Labeled_N _ is) = takespills mx v is


--
-- determine which registers are not used in a given collection of instructions:
--
spillcans :: (Int, Int) -> [Ins] -> [MReg] -> RMap -> [MReg]
spillcans (n, n') is ms rm =

      -- collect the variables from the instructions:
  let vs = foldr
           (\v -> \vs ->

             case (dst v) of
               (Just r) -> r:(src v ++ vs)
               Nothing  -> src v ++ vs

           ) [] is

   in
   let something = []
   in
      -- get the corresponding machine registers from the map:
   let rs = foldr
            (\v -> \rs -> 

              something
 
            ) [] vs
   in
     something

-- spill virtual register into corresponding variable location:
spillr ::  MReg -> Ins
spillr v = StoreI (MR v) rspill (Adr (ppt v))

-- spill machine register into corresponding varialbe location:
vspillr ::  VReg -> Ins
vspillr v = StoreI v rspill (Adr (ppt v))

-- restore machine register from corresponding variable location:
unspillr ::  MReg -> Ins
unspillr v = LoadI (MR v) rspill (Adr (ppt v))

-- restore virtual register from corresponding variable location:
vunspillr ::  VReg -> Ins
vunspillr v = LoadI v rspill (Adr (ppt v))


-- append a sequence of location-neutral spills to the end of a block;
--
-- assumed that last instruction in the block is a jump,
-- which needs to retain its place as the last instruction in the block;
--
prespill :: BBlock -> [VReg] -> BBlock
prespill (BB l b) vs =
  let jmp = Semi (lastins b) Nil
  in
    BB l
      (inscat (foldr (\i -> \is -> Semi i is) (initins b) (map vspillr vs)) jmp)


-- prepend a sequence of spills to the beginning of a block:
postspill :: BBlock -> [VReg] -> BBlock
postspill (BB l b) vs =
  BB l (foldl (\is -> \i -> inscat is (Semi i Nil)) b (map vunspillr vs))


--
-- set-aside register for doing spills;
-- this may be completely removed later, but is
-- convenient for the time being;
--
-- (2010.11.15) Schulz
--
rspill :: VReg
rspill = SReg R_Spill



--                      --
-- TARGETS AND CONTANTS --
--                      --

--
-- Target: Microblaze:
--

--
-- these are the general purpose microblaze registers,
-- minus R0 and R14-17, which have either suggested or hard-wired
-- special purposes:
--
mb_regs :: [MReg]
mb_regs = map MReg $
            [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] ++
            [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

--
-- some (mostly arbitrary) conventions for mapping the special registers
-- to Microblaze:
--
mb_base_map :: RMap
mb_base_map =

 let inf = (0, (maxBound :: Int))
 in

 [
   -- the 'spill' register is really just used as a zero offset:
   (MReg 0, (SReg R_Spill, inf))
 ]

--
-- mapping of the integer interval representing number of available registers
-- onto the actual register names:
--
mb_regs_map :: Int -> MReg
mb_regs_map = \n -> head (drop (n - 1) mb_regs)



--                  --
-- HELPER FUNCTIONS --
--                  --

--
-- another special-purpose depth-first traversal,
-- better suited to the tasks in this module
--
-- this function is used specifically to annotate the
-- control flow graph with a preorder-traversal numbering
--
dft_n :: BBlock -> CFG -> InsSeq_N -> [LBlock] ->
           (Int -> BBlock -> InsSeq_N) ->
             Int -> (((InsSeq_N, [LBlock]), Int), CFG)
           
dft_n v (vs, es) is ls f n =

  let sc  = (vsucc_r v (vs, es))
      es' = es \\ (esucc v es)  -- mark all successor edges as traversed
      vs' = vs \\ sc            -- mark all successors as visited
  in
    let is'       = f n v           -- visit 'v'

        is'''     = mklabelblkn (labelsof v) -- grab the labels out

        n'        = n + blklen v    -- update the instruction counter

        l         = (labelsof v, (n, n')) -- compute and save the block range
    in
    let t = foldr
            (\v' -> \(((is'', ls'), n''), g') ->

              -- traverse from the successors:
              dft_n v' g' is'' ls' f n''

            ) (((Nil_N, ls), n'), (vs', es')) sc

        is''        = (fst . fst . fst) t
        ls''        = (snd . fst . fst) t
        n''         = (snd . fst) t
        vs''        = (fst . snd) t
        es''        = (snd . snd) t
    in
      (((inscat_n is''' (inscat_n is' is''), l:ls''), n''), (vs'', es''))




--
-- collect the liveness intervals for a given variable:
--
lintzip :: [(BBlock, [VReg])] -> [LBlock] -> [LInterval]
lintzip bs ls =

  foldr
  (\(b, vs) -> \ls' -> 

    let xs = labelsof b
        ns = case (find ((== xs) . fst) ls) of

               (Just ds) -> snd ds

               Nothing   -> error $ "bad block label header in \'lintzip\': "
                                    ++ (show xs)

    in

      (foldr (\v -> \vs' -> (v, ns):vs') [] vs) ++ ls'

  ) [] bs



mklabelblkn :: [Label] -> InsSeq_N
mklabelblkn = foldr (\l -> \b -> Labeled_N l b) Nil_N


-- THIS IS THE END OF THE FILE --
