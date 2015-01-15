--
-- this is ~/cheapthreads/ctc_working/CT-1.0/Theory/Unstep.hs
--
-- Definition for the proposed canonical deconstructor for the resumption monad,
-- which is central to writing handlers and schedulers in CT, and RPS generally.
--
-- put here 2010.08.30
--
-- Schulz
--

module Unstep where

import MonadicConstructions


type Mem = [(Int, Int)]
type K a = StateT Mem Id a
type R a = ResT (StateT Mem Id) a


resume :: R a -> R (R a)
resume (Pause x) = step_R x
resume (Done v)  = step_R ((return .return) v)
