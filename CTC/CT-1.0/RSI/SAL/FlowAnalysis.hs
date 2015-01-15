--
-- this is ~/cheapthreads/CTC/CT-1.0/RSI/SAL/FlowAnalysis.hs
--
-- Data flow and control flow analysis for the SAL intermediate representation;
--
-- Functions that produce a control flow graph of the output
-- from RSI.SAl.Compile, and perform other data flow analyses
--
-- put there 2010.11.04
--
-- Schulz
--

module RSI.SAL.FlowAnalysis where

import RSI.SAL.Syntax
import RSI.Syntax

import CT.Debug

import Data.List   -- mostly for graph manipulations

--                 --
-- TOP LEVEL CALLS --
--                 --

--
-- produce the control flow graph for an instruction sequence,
-- annotated with live registers in each block,
-- and indicating the starting node for execution;
--
flanalyze :: InsSeq -> (Label, CFG_L)
flanalyze is =
  let (_, (v0, is'))  = nxtbblock is        -- determine next block in sequence
  in
    let g   = mkcfg is                      -- generate the control flow graph;
        es  = snd g                         -- get vertex set of the graph;
        l0  = zip (fst g) (repeat ([], [])) -- create initial liveness acc;
        vs  = livevs_solve v0 g l0          -- compute live regs in each block,
                                            -- starting at initial block;
    in

      case (labelsof v0) of
        (h:_) -> (h, (vs, es))
        _     -> dbtrace ("--->" ++ show is) ("", ([], []))

--      dbtrace ("---->" ++ show (nxtbblock is)) (head (labelsof v0), (vs, es))
--      (head (labelsof v0), (vs, es))
      


--                    --
-- CONTROL FLOW GRAPH --
--                    --

--
-- note that separation of code blocks is preserved here,
-- but only implicitly; there will, in general be no explicit edges
-- between blocks, although 'CSW' implies an runtime-determined jump
-- that, in general, will go between blocks
--
-- (2010.11.08) Schulz
--

cfg :: SAL -> CFG
cfg (SAL (_, (_, is))) =

  foldr
  (\i -> \(v, e) ->

    let g' = mkcfg i
    in
      ((fst g') ++ v, (snd g') ++ e)

  ) ([], []) is
  
  

--
-- generate the control flow graph from an instruction sequence:
--
-- first application ('bbreak') produces blocks, and draws
-- trivial control flow edges;
--
-- second ('cfvtxs') produces the list of vertices (blocks) in the graph;
--
-- third ('cfedges') draws the remaining edges, i.e. those specifying
-- non-trivial control flow;
--
mkcfg :: InsSeq -> CFG
mkcfg is = let bs = bbreak is
               vs = cfvtxs bs
           in
             (vs, cfedges vs bs)


cfvtxs :: [Either ((BBlock, BBlock) ,Ins) CFEdge] -> [BBlock]
cfvtxs =

  nub . 

  (
  foldr
  (\b -> \bs -> case b of
                  (Left ((b, b'), _))    -> b:b':bs
                  (Right (CFE b b'))     -> b:b':bs
                  (Right (CSW b b'))     -> b:b':bs
                  (Right (CFB b b' b'')) -> b:b':b'':bs

  ) [])


--
-- draw control flow edges between the blocks:
--
cfedges :: [BBlock] -> [Either ((BBlock, BBlock), Ins) CFEdge] -> [CFEdge]

cfedges vs bs =

  foldr
  (\b -> \g ->

    case b of
      (Right e) -> e:g
      (Left t)  -> (edgelkp t vs):g

  ) [] bs


--
-- draw edges from the given block, terminated by
-- the given control flow instruction, to all relevant
-- blocks in the given list
--
edgelkp :: ((BBlock, BBlock), Ins) -> [BBlock] -> CFEdge

-- conditional branches constitute a special case,
-- i.e. the only situation in which a vertex will have
-- two outgoing edges
-- (2010.11.11) Schulz

edgelkp ((b, b'), i@(MBZ _ (Adr l))) bs =


  case (labellkp l bs) of

    (Just b'') -> CFB b b' b''

    Nothing   -> error $ "malformed jump: " ++ (show i)

--
-- everything else has only one;
--
-- however, we must also account for implict returns in the handling of
-- register-targeted jumps:
--
edgelkp ((b, b'), i) bs =

  case (jtar i) of

    (Left _)        -> CSW b b'

    (Right (Adr l)) -> case (labellkp l bs) of

                         (Just b'') -> CFE b b''

                         Nothing   -> error $ "malformed jump: " ++ (show i)

--
-- lookup control destination blocks by label:
--
labellkp :: Label -> [BBlock] -> (Maybe BBlock)

labellkp l (b:bs) = let ls = labelsof b
                    in
                      if (elem l ls) then (Just b) else labellkp l bs

labellkp l []     = Nothing


--
-- break an instruction sequence into blocks,
-- and draw edges between blocks following in simple sequence;
--
-- each block is paired with a terminating control
-- jump instruction, where these occur;
-- 
-- edge for conditional jumps are formed as sequential-paired blocks,
-- together with the branch address (the tuple on the RHS of second  'Either')
--
bbreak :: InsSeq -> [Either ((BBlock, BBlock), Ins) CFEdge]

bbreak Nil = []

bbreak is =
  let (i, (b, is')) = nxtbblock is
  in
    case i of
      Nothing  -> case (bbreak is') of
                    (h:t) -> case h of
                               (Left ((b', _), _)) -> (Right (CFE b b')):h:t

                               (Right (CFE b' _))  -> let e' = CFE b b'
                                                      in
                                                        (Right e'):h:t
                    []    -> []

      -- pair control flow instructions with blocks following
      -- them in textual sequence:
      (Just i) -> case (bbreak is') of
                    (h:t) -> case h of
                               (Left ((b', _), _)) -> (Left ((b, b'), i)):h:t

                               (Right (CFE b' _))  -> (Right (CFE b b')):h:t

                    []    -> []



--
-- parse the next basic block out of a sequence;
-- 
-- return the block and the remainder of the sequence.
--
-- blocks are broken off at jumps and branches, and also at labels;
-- blocks are broken at labels to facillitate drawing edges from
-- immediate-argument jumps
--
-- NOTE: we use here the assumption that every basic block in the RSI
-- representation is labeled -- which it should be
--

nxtbblock :: InsSeq -> (Maybe Ins, (BBlock, InsSeq))
nxtbblock is = let (ls, is')       = blklabels [] is  -- separate leading labels
                   (i, (bb, is'')) = mkbblock Nil is' -- get block instructions
               in
                 (i, (BB ls bb, is''))



mkbblock :: InsSeq -> InsSeq -> (Maybe Ins, (InsSeq, InsSeq))

mkbblock b (Semi i is)    = if ((not . cfi) i)
                            then mkbblock (inscat b (Semi i Nil)) is
                            else (Just i, (inscat b (Semi i Nil), is))

mkbblock b (Labeled l is) = (Nothing, (b, Labeled l is))

mkbblock b Nil            = (Nothing, (b, Nil))


--
-- take all synonymous (consecutive) labels from the beginning of a sequence:
--
blklabels :: [Label] -> InsSeq -> ([Label], InsSeq)
blklabels ls (Labeled l is) = blklabels (l:ls) is
blklabels ls is             = (ls, is)


--                        --
-- DATA FLOW AND LIVENESS --
--                        --

--
-- accumulate live variables until all possible have been computed;
--
livevs_solve :: BBlock -> CFG ->
                  [(BBlock, ([VReg], [VReg]))] -> [(BBlock, ([VReg], [VReg]))]
livevs_solve b g vs =

  let vs' = livevs b g vs
  in
    if (vs == vs') then vs' else (livevs_solve b g vs')

--
-- determine the live variables (virtual registers) in each basic block;
--
-- IMPORTANT: in general, this requires a correctly specified initial vertex!
--
livevs :: BBlock -> CFG -> [(BBlock, ([VReg], [VReg]))] ->
            [(BBlock, ([VReg], [VReg]))]
livevs v0 (vs, es) ls =

  let f = \n -> \es' -> \as -> (n, lives es' as n) -- new lives for n

      g = \as -> \n' ->
            n':(deleteBy (\x -> \y -> (fst x) == (fst y)) n' as) -- update acc

  in 
    dft v0 es f g ls


--
-- get the live-in (fst) and live-out (snd) variables given
-- a vertex and an accumulation of live-in and -out registers so far;
--
lives :: [CFEdge] -> [(BBlock, ([VReg], [VReg]))] -> BBlock -> ([VReg], [VReg])
lives es bs@(_:_) b =

  let vs   = lkpblk b bs
      sc   = vsucc b es

      -- live-in IF used in 'b' OR IF life-out AND not deffed;
      vin  = union (vuses b) ((snd vs) \\ (vdefs b))

      -- live-out IF live-in for any successor of 'b'
      vout = bigunion (map fst (map (lives es bs) sc))
  in
    (vin, vout)
    
lives _  [] _ = ([], [])


lkpblk :: (Show a) => BBlock -> [(BBlock, a)] -> a
lkpblk b bs = case (lookup b bs) of
                (Just b') -> b'
                Nothing   -> error $ "couldn't lookup block: " ++ show (b, bs)

--
-- get the variable (virtual register) uses in a block:
--
vuses :: BBlock -> [VReg]
vuses (BB _ is) = (nub . (foldinsseq (\i -> \vs -> (src i) ++ vs) [])) is

--
-- get the variable definitions occurring in a block:
--
vdefs :: BBlock -> [VReg]
vdefs (BB _ is) = (nub . (foldinsseq (\i -> \vs -> case (dst i) of
                                                    (Just v) -> v:vs
                                                    Nothing  -> vs) [])) is

--
-- get the blocks using a given variable (virtual register):
--
nuses :: VReg -> [BBlock] -> [BBlock]
nuses v g =

  foldr (\b -> \bs -> if (elem v (vuses b)) then (b:bs) else bs) [] g
  

--
-- get the blocks defining a given variable (virtual register):
--
ndefs :: VReg -> [BBlock] -> [BBlock]
ndefs v g =

  foldr (\b -> \bs -> if (elem v (vdefs b)) then (b:bs) else bs) [] g



--                  --
-- HELPER FUNCTIONS --
--                  --


--
-- a special-case depth-first traversal of the control flow graph:
--
-- first argument: currently visited node;
--
-- second argument: the list of untraversed edges;
--
-- third argument: the 'visitation function', which produces info from the node;
--
-- fourth argument: update function on the accumulator;
--
-- fifth argument: an accumulator;
--
-- All information gathered from each visited node is aggreated into a list;
--
--
dft :: BBlock -> [CFEdge] -> (BBlock -> [CFEdge] -> b -> a) ->
         (b -> a -> b) -> b -> [a]

dft v es f g i =

  let vs' = vsucc v es            -- get successor vertices
      es' = es \\ (esucc v es)    -- remove traversed edges
      v'  = f v es i              -- apply the 'visitation' function
      i'  = g i v'                -- update the accumulator
  in
    v':(foldr (\v' -> \xs -> (dft v' es' f g i') ++ xs) [] vs')


--
-- successor vertices of a given vertex in the graph:
--
vsucc :: BBlock -> [CFEdge] -> [BBlock]
vsucc b es =

  foldr
  (\e -> \bs ->

    case e of
      (CFE b' b'')      -> if b' == b then (b'':bs) else bs
      (CFB b' b'' b''') -> if b' == b then (b'':b''':bs) else bs

      -- although a context-switch occurs at the end of b',
      -- control should eventually return to b'';
      -- this is needed for the integrity of the traversal
      --
      -- (2010.11.15) Schulz
      (CSW b' b'')      -> if b' == b then (b'':bs) else bs

  ) [] es


--
-- a variant of the successor function, to be used when it is expedient
-- to remove vertices from the graph during a traversal;
-- this checks whether vertices specified in an edge are present
-- in the vertex list, and drops them if not
--
vsucc_r :: BBlock -> CFG -> [BBlock]
vsucc_r v (vs, es) = filter (\x -> elem x vs) (vsucc v es)


--
-- successor edges of a given vertex in the graph:
--
esucc :: BBlock -> [CFEdge] -> [CFEdge]
esucc b es =

  foldr
  (\e -> \es' ->

    case e of
      (CFE b' _)   -> if b' == b then (e:es') else es'
      (CFB b' _ _) -> if b' == b then (e:es') else es'
      (CSW b' _)   -> if b' == b then (e:es') else es'

  ) [] es

--
-- predecessor vertices of a vertex in the graph:
--
vpred :: BBlock -> [CFEdge] -> [BBlock]
vpred b es =

  foldr
  (\e -> \bs ->

    case e of
      (CFE b' b'')      -> if b'' == b then (b':bs) else bs
      (CFB b' b'' b''') -> if ((b'' == b) || (b''' == b)) then (b':bs) else bs

      (CSW b' b'')      -> if (b' == b) then (b':bs) else bs

  ) [] es


--
-- predecessor edges of a vertex in the graph:
--
epred :: BBlock -> [CFEdge] -> [CFEdge]
epred b es =

  foldr
  (\e -> \es' ->

    case e of
      (CFE _ b')     -> if b' == b then (e:es') else es'
      (CFB _ b' b'') -> if ((b' == b) || (b'' == b)) then (e:es') else es'
      (CSW _ b'')    -> if (b'' == b) then (e:es) else es'

  ) [] es


--
-- predicate for control flow altering instructions:
--
cfi :: Ins -> Bool
cfi (MBZ _ _) = True
cfi (MJmp _)  = True 
cfi (MJmpI _) = True
cfi _         = False

--
-- union over multiple lists:
--
bigunion :: (Eq a) => [[a]] -> [a]
bigunion = foldr (\x -> \xs -> union x xs) []


mklabelblk :: [Label] -> InsSeq
mklabelblk = foldr (\l -> \b -> Labeled l b) Nil

-- THIS IS THE END OF THE FILE --
