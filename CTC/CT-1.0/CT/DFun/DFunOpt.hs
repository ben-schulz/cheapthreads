--
-- this is ~/cheapthreads/CTC/CT-1.0/CT/DFun/DFunOpt.hs
--
-- some simple optimizations for the state machine output
-- by the defunctionalizer
--
-- put here 2010.03.31
--
-- Schulz
--

module CT.DFun.DFunOpt where

import CT.DFun.FSM

import Data.List

--
-- collapse unconditional, non-transducing
-- transitions into a single transition, according
-- to the rule:
--
--    a => b  ,  b => c
--   ___________________
--         a => c
--
transtrans :: TransD -> [Trans] -> [Trans]
transtrans d ts =


  -- separate transitions affecting assignment or control flow:
  let (keep, mut)  = foldr
                     (\t -> \(ks, ms) ->

                       case t of
                         (Left (i, _)) -> case (d t) of

                                            [] -> if (any (iscondt i) ts)

                                                  -- keep implicit 'else'
                                                  then (t:ks, ms)

                                                  -- anything else can go:
                                                  else (ks, t:ms)

                                            -- keep an assignment
                                            _  -> (t:ks, ms)

                         -- keep a conditional
                         (Right _)     -> (t:ks, ms)

                     ) ([], []) ts


      -- transitively condense transitions:
      keep'         = condense mut

  in
    keep ++ keep'


--
-- condense all out-going paths from the terminal
-- point of a transition:
--
condense :: [Trans] -> [Trans]

condense (t:ts) =

  case (glkp t ts) of

    Nothing -> t:(condense ts)

    Just t' -> let ts' = filter (\x -> not $ (x == t) || (x == t')) ts
                   t'' = jointt t t'
               in
                 condense (t'':ts')
    
condense [] = []


glkp :: Trans -> [Trans] -> Maybe Trans
glkp t (t':ts) = if (termof t) == (initof t') then Just t' else glkp t ts
glkp _ []      = Nothing



--
-- identify whether an element with the given PC
-- occurs as the initial part of a conditional transition:
--
iscondt :: PC -> Trans -> Bool
iscondt pc (Right (_, (i, _))) = i == pc
iscondt _ _                    = False


--
-- check whether an unconditional transition terminates at a given node:
--
termsat :: PC -> Trans -> Bool
termsat pc (Left (_, j))      = pc == j
termsat _ (Right (_, (_, _))) = False

--
-- check whether an unconditional transition starts at a given node:
--
initsat :: PC -> Trans -> Bool
initsat pc (Left (i, _))      = pc == i
initsat _ (Right (_, (_, _))) = False


--
-- check whether an unconditional transition begins at a given node:
--

--
-- check whether two unconditional transitions share a node:
--
tcon :: Trans -> Trans -> Bool
tcon (Left (_, j)) (Left (i', _)) = j == i'
tcon _ _ = False

--
-- join two transitions into a single transition:
--
jointt :: Trans -> Trans -> Trans
jointt (Left (i, _)) (Left (_, j')) = Left (i, j')




-- THIS IS THE END OF THE FILE --
