--
-- this is ~/cheapthreads/ctc/ct/defunctionalizer/DFExec.hs
--
-- an executor for running the state machines produced by
-- the defunctionalizer
--
-- put here 18.03.09
--
--  Schulz
--

module CT.Defunctionalizer.DFExec where

import CT.Defunctionalizer.DefunTypes
import CT.Syntax

--
-- virtual registers corresponding to
-- components of the K-state
--
type VReg = (CtsIdent, DefunVal)

--
-- construct the virtual registers
--
mkVReg :: KState -> [VReg]
mkVReg = foldr ((:) . (\ (x, y) -> (x, DFNil))) [ ]

--
-- pretty-printer for the register dump
--
pptVReg :: [VReg] -> String
pptVReg = foldr (\ (u, v) -> \s -> s ++ u ++ " := " ++ (show v) ++ "\n") [ ]

--
-- main executor loop
--

dfexec :: [VReg] -> RState -> [RRule] -> IO ( )
dfexec vs k rs = do
                   state <- let pc = fst k in
                              return $ "{\npc := " ++ (show pc) ++ "\n"
                                       ++ (pptVReg vs) ++ "\n}\n"
                   putStrLn state
                   cmd <- getLine
                   c <- if null cmd
                        then
                          let newr = tapp k rs
                              newvs = updk vs (snd newr)
                          in
                            dfexec newvs newr rs
                        else
                          return ( )
                   return c

--
-- apply a transition rule and obtain the new state
--
tapp :: RState -> [RRule] -> RState
tapp rr fsm =
  let pc = fst rr
  in
    case filter (\ x -> (((==) pc) . fst . fst) x) fsm of
      [ ] -> error $ "transition from " ++ (show pc) ++ " failed; "
                         ++ "no corresponding rule\n"
      [t]  -> snd t
      ts   -> error $ "multiple transitions from " ++ (show pc) ++ ": "
                      ++ (pptRules ts)

--
-- update the K-state values, given a new R-state
--
updk :: [VReg] -> KState -> [VReg]
updk rs k = foldr ((:) . (writeval k rs)) [ ] rs

writeval :: KState -> [VReg] -> VReg -> VReg
writeval k prev (tag, val) =
  let newval = getval tag k
  in
    case newval of
      DFParam x -> (tag, getval x prev)
      DFPOp p   -> (tag, evalPOp prev k p)
      v         -> (tag, v)

--
-- get the value of a given virtual register in K
--
getval :: CtsIdent -> [VReg] -> DefunVal
getval x [ ] = DFNil  -- this is a kludge to deal with initialization
                      -- see log 02.04.09
getval x k =
  case lookup x k of
    Nothing  -> error $ "no state in K for register " ++ x
    Just val -> val

--
-- evaluate a primitive operation
--
evalPOp :: [VReg] -> KState -> PrimOp -> DefunVal
evalPOp _ _ (DFPlus (DFInt u) (DFInt v)) = DFInt (u + v)
evalPOp _ _ (DFMinus (DFInt u) (DFInt v)) = DFInt (u - v)
evalPOp vs k (DFPlus (DFParam x) (DFInt v)) =
  case getval x vs of
    DFInt u   -> DFInt (u + v)
    DFPOp p   -> let DFInt u = evalPOp vs k p
                 in
                   DFInt (u + v)
    DFParam y -> case lookup y vs of  -- see log 01.04.09
                   Just val -> evalPOp vs k (DFPlus val (DFInt v))
                   Nothing  -> error $ "register \'" ++ y ++ "\' not found\n"
    z         -> error $ show z
evalPOp vs k (DFMinus (DFParam x) (DFInt v)) =
  case getval x vs of
    DFInt u -> DFInt (u - v)
    DFPOp p -> let DFInt u = evalPOp vs k p
               in
                 DFInt (u - v)
evalPOp vs k (DFPlus (DFInt u) (DFParam y)) =
  case getval y vs of
    DFInt v -> DFInt (u + v)
    DFPOp p -> let DFInt v = evalPOp vs k p
               in
                 DFInt (u + v)
evalPOp vs k (DFMinus (DFInt u) (DFParam y)) =
  case getval y vs of
    DFInt v -> DFInt (u - v)
    DFPOp p -> let DFInt v = evalPOp vs k p
               in
                 DFInt (u - v)
evalPOp vs k (DFPlus (DFParam x) (DFParam y)) =
  let u = getval x vs
      v = getval y vs
  in
    evalPOp vs k (DFPlus u v)
evalPOp vs k (DFMinus (DFParam x) (DFParam y)) =
  let u = getval x vs
      v = getval y vs
  in
    evalPOp vs k (DFMinus u v)
evalPOp vs k (DFPlus (DFPOp x) (DFPOp y)) =
  let DFInt u = evalPOp vs k x
      DFInt v = evalPOp vs k y  -- see log (18.03.09)
  in
    DFInt (u + v)
evalPOp vs k (DFMinus (DFPOp x) (DFPOp y)) =
  let DFInt u = evalPOp vs k x
      DFInt v = evalPOp vs k y  -- see log (18.03.09)
  in
    DFInt (u - v)
evalPOp _ _ p = error $ "illegal primitive operation: " ++ (show p)
