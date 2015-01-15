module AddingContext where

import MonadicConstructions

                  -------------------------
                  ---  Monad Hierarchy  ---
                  -------------------------

type A  = Int
type B  = Int
type G  = Int
type K  = StateT G I --- N.b., only one global state
type R  = ResT K 

etaR :: a -> R a   --- overloading sucks
etaR = return      

etaK :: a -> K a
etaK = return

                  ------------------
                  ---  Liftings  ---
                  ------------------

step :: K a -> R a
step x = Pause (x >>= (etaK . Done))

                  -----------------------------------
                  ---  Non-proper Morphisms of K  ---
                  -----------------------------------

g :: K Int
g = ST (\ l -> I (l,l))

u :: (G -> G) -> K ()
u delta = ST (\l -> I ((),delta l))

store :: Int -> K ()
store v = u (\ _ -> v)

                  ---------------------------
                  ---  Actions & Channel  ---
                  ---------------------------

{- 
Recall what occurs in the hardwired example. 

The action definitions affect different states:
     actionA = gA >>= (storeA . (\ v -> v + 1))
     actionB = gB >>= (storeB . (\ v -> v - 1))
-}


{-
The actionA and actionB definitions below affect the single global state, so
there is no separation "by construction". Separation must be managed by the 
channel.
-}

actionA = u (\ v -> v + 1) -- reg++
actionB = u (\ v -> v - 1) -- reg--

threadA :: R ()
threadA = fix (\ k -> (step actionA) >> k)

threadB :: R ()
threadB = fix (\ k -> (step actionB) >> k)

{-
In the hardwired example, the channel doesn't do anything but alternate between
A and B actions:
    channel = step actionA >> step actionB >> channel

In the new definition below, contexts for A and B are added. Now, the channel
"swaps in" A by copying the current value of the A state (called a below) 
to the global state. Then, actionA executes, thereby incrementing the current
value of a. The A context is then saved by first reading the global state with 
g and then binding the result to a' in "... >> g) >>= \ a' ->...". The story 
is analogous for B. Note that the new contexts, a' and b', are passed onto
the next channel iteration.
-}

{- Previous versions.

channel :: A -> B -> R ()
channel a b = step (store a >> actionA >> g) >>= \ a' -> 
              step (store b >> actionB >> g) >>= \ b' -> 
                 channel a' b'

chan :: A -> B -> R ()
chan = fix (\ k -> \ a -> \ b -> step (store a >> actionA >> g) >>= \ a' -> 
                                 step (store b >> actionB >> g) >>= \ b' -> 
                                    k a' b')
-}

-- Textbook definition of a monadic strength:
-- strength x phi = phi >>= (\ v -> return (x,v))
--
-- This one rearranges the order of arguments for convenience:
--strength :: K a -> b -> K (a,b)
strength phi x = phi >>= \ v -> return (x,v)

-- written in terms of strength?
combine :: K a -> K b -> K (a,b)
combine phi gamma = phi >>= (strength gamma)

channel :: (R(),A) -> (R(),B) -> R ()
channel (Pause phi1,a) (Pause phi2,b) 
    = step (store a >> combine phi1 g) >>= \ (phi1',a') -> 
      step (store b >> combine phi2 g) >>= \ (phi2',b') -> 
         channel (phi1',a') (phi2',b')

chan :: (R(),A) -> (R(),B) -> R ()
chan = fix (\ k -> \ (Pause phi1,a) -> \ (Pause phi2,b) ->
               step (store a >> combine phi1 g) >>= \ (phi1',a') -> 
               step (store b >> combine phi2 g) >>= \ (phi2',b') -> 
                  k (phi1',a') (phi2',b'))

fix :: (a -> a) -> a
fix f = f (fix f)

{-

System states will have the following form:
       <group> ( <function-args> , <internal-monadic-states> , return-value )

Here, <group> is a tag signifying the state group that the state belongs to. Because these
are monadic computations that always return a value of some form, the last component is the 
return value.

In defunctionalizing (step \phi), the rules in defun(\phi) will all have the same state group. 
In (step phi_1) >> ... >> (step phi_n), each state group tag for (step phi_i) is
unique. These group names are used to maintain the control flow.

In the case of the channel above, the states will look like:
       <group> (a,b,reg,val)

The a and b components are from the a and b arguments to chan, reg is the state internal to K, 
and val is the return value. 

-}

-- To see the states after n steps, type
--
--        go n a b
--
-- at the Haskell prompt where a and b are initial A and B states, resp.
--
-- In this case one only gets the value of the last channel action:
--    HardwiredSeparation> go 100 0 0
--      -50

go n a b = (runK undefined . run . takeR n) (chan (threadA,a) (threadB,b))
    --- here the global state is undefined, because the channel "swaps in"
    --- the context of A or B.

takeR :: Int -> R a -> R a
takeR 0 phi             = Done undefined
takeR (n+1) (Pause phi) = Pause (phi >>= (etaK . takeR n))
takeR (n+1) (Done v)    = error "undefined on purpose"

run :: R a -> K a
run (Pause phi) = phi >>= run
run (Done v)    = etaK v

runK :: G -> K t -> G
runK g (ST phi) = snd (deI (phi g))

-- Compilation monad. Ignore what follows for the moment.
type M a = EnvT Int (StateT Int I) a

etaM :: a -> M a
etaM = return

gM :: M Int
gM = liftEnv (ST (\ l -> return (l,l)))

uM :: (A -> A) -> M ()
uM delta = liftEnv $ ST (\l -> return ((),delta l))

newstate :: M Int -- label generator
newstate = uM (\ v -> v + 1) >> gM

-- defun (Fix v e) = newstate >>= \ sigma ->



-- R_Exp is the source language
type Var   = String
data R_Exp = Fix Var R_Exp         -- fix (\ k -> e)
           | Step R_Exp            -- in (Step phi), it is assumed phi is in the K monad
           | BindNull [R_Exp]      -- >>
           | Bind R_Exp Var R_Exp  -- >>=
           | Upd StateTransform    -- e.g., u (\ v -> v + 1)
           | Lambda Var R_Exp
           | V Var                 -- occurrences of recursively bound variables
     deriving Show

data StateTransform = Var :|-> Exp deriving Show
data Exp = Lit Int | Plus Exp Exp | Name Var deriving Show

-- chan :: A -> B -> R ()
-- chan = fix (\ k -> \ a -> \ b -> step (store a >> actionA >> g) >>= \ a' -> 
--                                  step (store b >> actionB >> g) >>= \ b' -> 
--                                     k a' b')

rchan = Fix "k"          $
           Lambda "a"    $
              Lambda "b" $
                 Bind (Step $ BindNull []) "a'" (V "dummy")
                   
