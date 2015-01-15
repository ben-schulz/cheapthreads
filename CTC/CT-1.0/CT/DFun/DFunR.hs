--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/DFun/DFunR.hs
--
-- the resumptive- and reactive-resumptive layer ("R") defunctionalizer
--
-- put here 2010.02.17
--
-- Schulz
--

module CT.DFun.DFunR where

import CT.Syntax
import CT.INAST

import CT.MonadicConstructions

import CT.DFun.FSM
import CT.DFun.DFunK

--
-- top-level call to the R-defunctionalizer;
--
-- transform a resumption or reactive-resumption-typed term
-- into a set of (possibly guarded) state transitions,
-- together with a function that associates a state 
-- transduction to each transition
--
dfunr :: INAST -> (TransD, [Trans])
dfunr e = prjdfr $ dfrinterp inittransd e



dfrinterp :: TransD -> INAST -> DFR (TransD, [Trans])

dfrinterp d (CTBindIN e e' _) = dfrinterp d e >>= \(d', ts') ->

                                -- set aside PC values for the transition
                                -- between the two terms:
                                readpc >>= \i ->
                                newpcval >>= \i' ->

                                dfrinterp d' (lambof e') >>= \(d'', ts'') ->

                                -- construct the in-between transition
                                -- that updates the lambda parameter with
                                -- the appropriate value:
                                let t    = Left (i, i')
                                    x    = lampof e'
                                    m    = MX $ FSMSig retval
                                    d''' = tweek d'' t [(Sig x, m)]
                                in
                                  return (d''', (ts' ++ (t:ts'')))


-- null-bind is, of course, analogous to bind,
-- but simpler:
dfrinterp d (CTNullBindIN e e' _) = dfrinterp d e >>= \(d', ts') ->
                                    dfrinterp d' e' >>= \(d'', ts'') ->
                                    return (d'', (ts' ++ ts''))



--
-- the step rule:
--
dfrinterp d (CTStepIN e _)   = let k = dfunk e  -- dfun the argument
                               in

                                 -- turn the result into one or more transitions
                                 readpc >>= \i ->
                                 newpcval >>= \i' ->
                                 ktermtotrans d k >>= \(d', ts) ->

                                 -- make an unconditional transition from
                                 -- each branch of the tree to a single 
                                 -- terminal state:
                                 let t' = Left (i, i')
                                 in
                                   return (d', (t':ts))



--
-- the return (eta-R) rule:
--
dfrinterp d (CTReturnIN e _) = let t = CTMTy StateTy (typeofinast e)
                                   k = dfunk (CTReturnIN e t)
                               in 
                                 ktermtotrans d k >>= \(d', ts) ->
                                 
                                 
                                 return (d', ts)
                                 
-- presuming some signals that need to be added 2011.07.22
dfrinterp d (CTGetReqIN r t) =
  return (\_ -> [(Sig "retval", MX (FSMSig "CMD"))], [])

dfrinterp d (CTCaseIN r _ t) = ktermtotrans d (dfunk (CTReturnIN r t))


dfrinterp d (CTLoopIN e  _) = -- let k  = lampof e -- name of the fixed point
                                --   lam = lampsnd e   -- the rest of the lambda
                              let e'  = lambof e  -- the rest of the lambda
                                  ps  = lampsof e -- the loop variables

                              in
                               readpc >>= \i ->
                               -- make a label for the loop head
                               let k = ("__LOOP" ++ (show i)) in

                               -- defunctionalize the body with k
                               -- associated to its loop variables:
                               extbind k ps >>= \rho ->
                               newpcval >>= \i' ->
                               inEnv rho (dfrinterp d e') >>= \(d', rs) ->

                               -- get PC values for the exit transition:
                               readpc >>= \j ->
                               newpcval >>= \j' ->

                               -- set up the entry and exit
                               -- points for the loop:
                               --let vs   = map mksigassgn (zip ps is')
                               let vs   = []
                                   it   = Left (i, fst $ rho k)
                                   d''  = tweek d' it vs
                                   st   = Left (fst $ rho k, i')
                                   ex   = Left (j, j')
                               in
                                return (d'', (it:st:rs) ++ [ex])


                               

--
-- the fixpoint rule:
--

{-
dfrinterp d (CTFixIN e is _) = let k   = lampof e    -- name of the fixed point
                                   lam = lampsnd e   -- the rest of the lambda
                                   e'  = lambof lam  -- the rest of the lambda
                                   ps  = lampsof lam -- the loop variables

                                   is' = map toFSMExpr is -- the initial values
                               in
                                 readpc >>= \i ->

                                 -- defunctionalize the body with k
                                 -- associated to its loop variables:
                                 extbind k ps >>= \rho ->
                                 newpcval >>= \i' ->
                                 inEnv rho (dfrinterp d e') >>= \(d', rs) ->

                                 -- get PC values for the exit transition:
                                 readpc >>= \j ->
                                 newpcval >>= \j' ->

                                 -- set up the entry and exit
                                 -- points for the loop:
                                 let vs   = map mksigassgn (zip ps is')
                                     it   = Left (i, fst $ rho k)
                                     d''  = tweek d' it vs
                                     st   = Left (fst $ rho k, i')
                                     ex   = Left (j, j')
                                 in
                                   return (d'', (it:st:rs) ++ [ex])

-}

--
-- defunctionalize a fully-applied loop
-- into the loop structure and the initial assignments:
--
                                              -- form initial loop values:
dfrinterp d (CTLoopAppIN (CTLoopIN e _) is _) = let is' = map toFSMExpr is

                                                  -- the recursive parameter:
                                                  -- STUB 2011.07.22
                                                    k   = "__LOOP"

                                                  -- the rest of the lambda:
                                                    lam = e

                                                  -- body of the lambda:
                                                    e'  = lambof lam 

                                                  -- the loop parameters:
                                                    ps  = lampsof lam
                                              in
                                              readpc >>= \i ->

                                              -- defunctionalize the body with k
                                              -- associated to loop variables:
                                              extbind k ps >>= \rho ->
                                              newpcval >>= \i' ->
                                              inEnv rho
                                                (dfrinterp d e') >>= \(d',rs) ->

                                              --  PC values for exit transition:
                                              readpc >>= \j ->
                                              newpcval >>= \j' ->

                                              -- set up the entry and exit
                                              -- points for the loop:
                                              let vs   = map mksigassgn
                                                           (zip ps is')

                                                  it   = Left (i, fst $ rho k)
                                                  d''  = tweek d' it vs

                                                  st   = Left (fst $ rho k, i')
                                                  ex   = Left (j, j')
                                              in
                                                return (d'', (it:st:rs) ++ [ex])
                                              

-- form initial loop values:
dfrinterp d (CTFixAppIN (CTFixIN e _) is _) = let is' = map toFSMExpr is

                                                  -- the recursive parameter:
                                                  k   = lampof e

                                                  -- the rest of the lambda:
                                                  lam = lampsnd e

                                                  -- body of the lambda:
                                                  e'  = lambof lam 

                                                  -- the loop parameters:
                                                  ps  = lampsof lam
                                              in
                                              readpc >>= \i ->

                                              -- defunctionalize the body with k
                                              -- associated to loop variables:
                                              extbind k ps >>= \rho ->
                                              newpcval >>= \i' ->
                                              inEnv rho
                                                (dfrinterp d e') >>= \(d',rs) ->

                                              --  PC values for exit transition:
                                              readpc >>= \j ->
                                              newpcval >>= \j' ->

                                              -- set up the entry and exit
                                              -- points for the loop:
                                              let vs   = map mksigassgn
                                                           (zip ps is')

                                                  it   = Left (i, fst $ rho k)
                                                  d''  = tweek d' it vs

                                                  st   = Left (fst $ rho k, i')
                                                  ex   = Left (j, j')
                                              in
                                                return (d'', (it:st:rs) ++ [ex])


--
-- application of a fixpoint recursive call:
--
-- this simply creates an unconditional jump back to the head of the
-- loop, with new values assigned to the loop variables according
-- to the arguments of the application
--
dfrinterp d (CTRecAppIN a x _) = let (k:as) = (unfoldapp a) ++ [x]
                                 in
                                   rdEnv >>= \rho ->
                                   readpc >>= \i ->

                                   -- advance the PC, but don't use value here
                                   newpcval >>

                                   let k'  = nameofvar k
                                       as' = map toFSMExpr as
                                       vs  = map mksigassgn
                                                 (zip (snd $ rho k') as')
                                       t   = Left (i, fst $ rho k')
                                       d'  = tweek d t vs
                                   in
                                     return (d', [t])

--
-- the signal rule:
--
-- note that, in general, we assume that signals are
-- wrapped by a constructor; the values, however, need not
-- be constants or literals
--
dfrinterp d (CTSignalIN (CTConIN c [a] _) _) = let ch  = chan_prefix ++ c

                                                   -- put the req on the chan:
                                                   a'  = mkchanwrite
                                                          (ch, toFSMExpr a)
  
                                                   -- put the resp in retval:
                                                   a'' = mkchanread
                                                           (retval, ch)
                                               in
                                               readpc >>= \i ->
                                               newpcval >>= \i' ->
                                               newpcval >>= \i'' ->
  
                                                   -- first transition puts req
                                               let t  = Left (i, i')
                                                   d' = tweek d t [a']

                                                   -- next transition gets rsp:
                                                   t' = Left (i', i'')
                                                   d'' = tweek d' t' [a'']
                                               in
                                                 return (d'', [t, t'])


--
-- this corresponds to a read-only signal:
--
dfrinterp d (CTSignalIN (CTConIN c [] _) _) = let ch = chan_prefix ++ c

                                                   -- put the resp in retval:
                                                  a' = mkchanread
                                                         (retval, ch)
                                               in
                                               readpc >>= \i ->
                                               newpcval >>= \i' ->
  
                                                   -- read the expected rsp:
                                               let t  = Left (i, i')
                                                   d' = tweek d t [a']

                                               in
                                                 return (d', [t])

--
-- branches:
--
-- this is entirely straightforward
--
dfrinterp d (CTBranchIN b e e' _) = readpc >>= \h ->
                                    newpcval >>= \i ->
                                    dfrinterp d e >>= \(d', ts) ->
                                    readpc >>= \j ->

                                    newpcval >>= \i' ->
                                    dfrinterp d' e' >>= \(d'', ts') ->
                                    readpc >>= \j' ->

                                    mkbranchexit j j' ts ts' >>= \ts'' ->

                                    let t    = Right ((toBoolExpr b), (h, i))
                                        t'   = Left (h, i')
                                    in
                                      return (d'', t:t':(ts ++ ts' ++ ts''))

dfrinterp _ x = error $ show x


--
-- make an exit transition so that resumptive branches
-- rejoin at a common state after execution of either branch
--
-- we assume a label corresponds to a jump to the head of
-- a loop, and so should not be augmented with another transition
--
-- First argument: last PC used in the 'true' branch;
-- Second argument: last PC used in the 'false' branch;
-- Third argument: list of transitions occuring in the 'true' branch;
-- Fourth argument: list of transitions occuring in the 'false' branch;
--
-- If the last-used PC is the initial PC of a jump to the head of a loop,
-- it is assumed that the body of that branch jumps unconditionally
-- and so should not be augmented with an exit transition to the end
-- of the loop.
--
-- Otherwise, if the last-used PC does not occur as the initial PC of a jump,
-- it is tied to a "branch exit" transition that closes the reumptive branch.
--
--
mkbranchexit :: PC -> PC -> [Trans] -> [Trans] -> DFR [Trans]

mkbranchexit i j ts ts' |  (not $ isjump i ts) && (not $ isjump j ts')  =
                                          newpcval >>= \i' ->
                                          let t  = Left (i, i')
                                              t' = Left (j, i')
                                          in
                                            return [t, t']

                        |  (not $ isjump i ts)  =
                                          newpcval >>= \i' ->
                                          let t  = Left (i, i')
                                          in
                                            return [t]

                        |  (not $ isjump j ts')  =
                                          newpcval >>= \i' ->
                                          let t'  = Left (j, i')
                                          in
                                            return [t']

--                        |  otherwise  = return []
                        |  otherwise  = newpcval >> return []



--pp
-- look for the presence of a label-jump
-- with a given initial PC in a list of transitions:
--
isjump :: PC -> [Trans] -> Bool
isjump (PCI i) ts =

  foldr
    (\j -> \bs ->

      case j of
        (Left (PCI i', PCL _))       -> if (i == i') then True else bs

        (Right (_, (PCI i', PCL _))) -> if (i == i') then True else bs
     
        _                            -> bs
    )
      False ts




--
-- transform a condition tree, produced by the K-defunctionalizer,
-- into a transition sequence:
--
-- note that every branch in the tree has an empty transduction;
-- only the leaves make changes to signal values
--
-- return type is the extended transduction function,
-- together with the transitions corresponding to the condition tree,
-- and a list of the terminal states of the transition sequences
--

ktermtotrans :: TransD -> KSplit STMod -> DFR (TransD, [Trans])

ktermtotrans d (KBind e x r) = readpc >>= \i ->
                               newpcval >>= \i' ->
                               ksplittotrans d e >>= \(d', (ts, ss)) ->
                               newpcval >>= \i'' ->
                               newpcval >>= \i''' ->
                               ktermtotrans d' r >>= \(d'', ts'') ->

                                   -- make the initial transition in:
                               let t    = Left (i, i')

                                   -- make an unconditional transition from
                                   -- each branch of the act-tree to a single 
                                   -- terminal state:
                                   ts' = map (\pc -> Left (pc, i'')) ss

                                   -- map the intermediate transition
                                   -- to the intermediate action:
                                   st   = (Sig x, MX $ FSMSig retval)
                                   t'   = Left (i'', i''')
                                   d''' = tweek d'' t' [st]

                               in
                                 return
                                   (d''',
                                     (t:ts) ++ ts' ++ (t':ts''))
                                 

--
-- same as bind, except no state assignment
-- between actions:
--
ktermtotrans d (KNullBind e r) = readpc >>= \i ->
                                 newpcval >>= \i' ->
                                 ksplittotrans d e >>= \(d', (ts, ss)) ->
                                 newpcval >>= \i'' ->
                                 newpcval >>= \i''' ->
                                 ktermtotrans d' r >>= \(d'', ts'') ->

                                     -- make the initial transition in:
                                 let t    = Left (i, i')

                                     -- make an unconditional transition from
                                     -- each branch of the act-tree to a
                                     -- single terminal state:
                                     ts'  = map (\pc -> Left (pc, i'')) ss

                                     -- make the transition between acts:
                                     t'   = Left (i'', i''')

                                 in
                                   return
                                     (d'',
                                       (t:ts) ++ ts' ++ (t':ts''))
                                 
--
-- end case; transform the last action in the K-term:
--
ktermtotrans d (K e)           = readpc >>= \i ->
                                 newpcval >>= \i' ->
                                 ksplittotrans d e >>= \(d', (ts, ss)) ->
                                 newpcval >>= \i'' ->

                                     -- make the initial transition in:
                                 let t    = Left (i, i')

                                     -- make an unconditional transition from
                                     -- each branch of the act-tree to a
                                     -- single terminal state:
                                     ts'  = map (\pc -> Left (pc, i'')) ss

                                 in
                                   return
                                     (d',
                                       t:(ts ++ ts'))
                                 
                                 



ksplittotrans :: TransD -> SplitNode STMod -> DFR (TransD, ([Trans], [PC]))

ksplittotrans d (R1 x)     = readpc >>= \i ->
                             newpcval >>= \i' ->
                             let t = Left (i, i')
                             in
                               return
                                 (tweek d t x,
                                   ([t],
                                     [termof t]))

ksplittotrans d (R2 b x y) = readpc >>= \i ->
                             newpcval >>= \i' ->
                             ksplittotrans d x >>= \(d', (ts', ls)) ->
                             newpcval >>= \i'' ->
                             ksplittotrans d' y >>= \(d'', (ts'', ls')) ->

                             -- 
                             -- "if b (goto x) else (goto y)"
                             --
                             let t  = Right (b, (i, i'))
                                 f  = Left (i, i'')
                             in
                               return
                                 (d'',
                                   (
                                     ((t:ts') ++ (f:ts'')),
                                     (ls ++ ls')
                                   )
                                 )


--                           --
-- DATA STRUCTURES USED HERE --
--                           --


--
-- we re-use the familiar environment-state monad
-- that we have relied upon throughout;
--
-- the state portion holds a counter used for generating
-- unique PC values; the environment portion associates
-- fixpoints to formal parameters representing their loop variables.
--
-- note the Int-pair in the state; the first is used for
-- ordinary PC values; the second is used to ensure
-- that label names, which can be disinguished according to
-- lexical scope in the source, don't have name conflicts in the FSM
--
-- the PC component carries the last-used PC value
--

type DFR a = EnvT Binding (StateT (PC, (Int, Int)) Id) a

--
-- project out of this monad:
--
prjdfr :: DFR a -> a
prjdfr (ENV x) = fst $ deId ((deST (x (initbind)))
                             (global_init, (initpc, initpc)))

--
-- bindings associate a fixpoint label
-- (i.e. the first parameter in the lambda)
-- to a list of formal parameters that will be
-- used as loop variables, as well as a unique
-- label associated to the head of the loop
--
type Binding = String -> (PC, [String])


--
-- every parameter is initially bound to no loop variables,
--
initbind :: Binding
initbind = \_ -> (PCI (initpc - 1), [])

--
-- extend the environment with a new binding:
--
extbind :: String -> [String] -> DFR Binding
extbind x ps =
  rdEnv >>= \rho ->
  newlabel x >>= \k ->
  return (tweek rho x (k, ps))


--
-- increment the state counters, component-wise:
--
counterfst :: DFR Int
counterfst =
  liftEnv(
    get >>= \(pc, (i, j)) ->
    upd (\_ -> (pc, ((i + 1), j))) >>
    return i
  )

countersnd :: DFR Int
countersnd =
  liftEnv(
    get >>= \(pc, (i, j)) ->
    upd (\_ -> (pc, (i , (j + 1)))) >>
    return j
  )

 

--
-- generate a new PC value,
-- and update the last-used PC component
--
newpcval :: DFR PC
newpcval =
  counterfst >>= \n ->
  liftEnv
  (
    get >>= \(_, (i, j)) ->
    let pc = PCI n
    in
      upd (\_ -> (pc, (i, j))) >>
      return pc
  )

--
-- generate a non-conflicting label,
-- and update the last-used PC component
--
newlabel :: String -> DFR PC
newlabel k =
  countersnd >>= \i ->
  liftEnv
  (
    get >>= \(_, (i, j)) ->
    let pc = PCL (k ++ (show i))
    in
      upd (\_ -> (pc, (i, j))) >>
      return pc
  )

--
-- get the last-used PC value:
--
readpc :: DFR PC
readpc =
  liftEnv
  (
    get >>= \(pc, (_, _)) ->
    return pc
  )

tweek :: (Eq a) => (a -> b) -> a -> b -> (a -> b)
tweek f v t = \x -> if x == v then t else f x




-- THIS IS THE END OF THE FILE --
