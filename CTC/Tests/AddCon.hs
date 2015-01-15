module AddingContext where

import MonadicConstructions
import CommonTypes
import Boilerplate hiding (store)
import MonadAddingContext -- MLab-built monad

-- test case based on Defunctionalization/Code/AddingContext.hs

{- The MLab spec:
monad R       = ResT K + StateT(G) G
type  G       = Int
-}

                  ---------------------------
                  ---  Actions & Channel  ---
                  ---------------------------

{-
The actionA and actionB definitions below affect the single global state, so
there is no separation "by construction". Separation must be managed by the 
channel.
-}

--getGK :: K G
--putGK :: G -> K ()

actionA :: K ()
actionA = getGK *= \ g -> putGK (g+1) -- reg++ -- getloc *= \ v -> setloc (v+1) 

actionB :: K ()
actionB = getGK *= \ g -> putGK (g-1) -- reg--
{-
-}

store :: Int -> K ()
store x = putGK x

{--}
-- called "chan0" or "rchan" previously
main :: Int -> Int -> R ()
main  = fix (\ k -> \ a -> \ b -> step (store a >> actionA >> getGK) ||= \ newa -> 
                                  step (store b >> actionB >> getGK) ||= \ newb -> 
                                      k newa newb)
{-
main = fix (\ k -> 
                \ a -> 
                    (step (store a) >> step (actionA >> getGK)) ||= \ newa -> k newa)

-}




{-
threadA :: R ()
threadA = fix (\ k -> (step actionA) >> k)

threadB :: R ()
threadB = fix (\ k -> (step actionB) >> k)

chan0 :: A -> B -> R ()
chan0 = fix (\ k -> \ a -> \ b -> step (store a >> actionA >> g) >>= \ newa -> 
                                  step (store b >> actionB >> g) >>= \ newb -> 
                                      k newa newb)
-}


{-
-- Textbook definition of a monadic strength:
-- strength x phi = phi >>= (\ v -> return (x,v))
--
-- This one rearranges the order of arguments for convenience;
-- i.e., in the literature, its type is: strength :: K a -> b -> K (a,b)
strength :: K a -> b -> K (b,a)
strength = \ phi -> \ x -> phi >>= \ v -> return (x,v)

-- written in terms of strength?
combine :: K a -> K b -> K (a,b)
combine = \ phi -> \ gamma -> phi >>= (strength gamma)

channel :: (R(),A) -> (R(),B) -> R ()
channel (Pause phi1,a) (Pause phi2,b) 
    = step (store a >> combine phi1 g) >>= \ (phi1',a') -> 
      step (store b >> combine phi2 g) >>= \ (phi2',b') -> 
         channel (phi1',a') (phi2',b')

-- needs rewriting in the style of the new version of hardwired.
-- I.e., threads are [S ()]
chan :: (R(),A) -> (R(),B) -> R ()
chan = fix (\ k -> \ (Pause phi1,a) -> \ (Pause phi2,b) ->
               step (store a >> combine phi1 g) >>= \ (phi1',a') -> 
               step (store b >> combine phi2 g) >>= \ (phi2',b') -> 
                  k (phi1',a') (phi2',b'))
-}
