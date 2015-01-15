module Twist where

import MonadicConstructions

                  -------------------------
                  ---  Monad Hierarchy  ---
                  -------------------------

type A  = Int
type B  = Int
type K  = StateT A (StateT A I)
type R  = ResT K 

etaR :: a -> R a  --- overloading sucks
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

gA :: K A
gA = liftST (ST (\ l -> return (l,l)))

uA :: (A -> A) -> K ()
uA delta = liftST (ST (\l -> return ((),delta l)))

gB :: K B
gB = ST (\ h -> return (h,h))

uB :: (B->B) -> K ()
uB delta = ST (\h -> return ((),delta h))

storeA :: Int -> K ()
storeA v = uA (\ _ -> v)
storeB :: Int -> K ()
storeB v = uB (\ _ -> v)

                  ---------------------------
                  ---  Actions & Channel  ---
                  ---------------------------

actionA = uA (\ v -> v + 1)
actionB = uB (\ v -> v - 1)

channel = step actionA >> step actionB >> channel

-- example from DefunctionalizingCheapThreads notes
twist :: R () -> R () -> R ()
twist x y = fix (\ k -> x >> y >> k)
   where
      fix :: (a -> a) -> a
      fix f = f (fix f)

-- expresses channel in terms of an explicit fix.
chan = twist (step actionA) (step actionB) 

reified_chan = Fix "k"
                   (BindNull [Step (UpdA ("v" :|-> Plus (Name "v") (Lit 1))),
                              Step (UpdB ("v" :|-> Plus (Name "v") (Lit (-1)))),
                              V "k"])

-- Compilation monad.
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
           | UpdA StateTransform   -- e.g., uA (\ v -> v + 1)
           | UpdB StateTransform   
           | Lambda Var R_Exp
           | V Var                 -- occurrences of recursively bound variables
     deriving Show

data StateTransform = Var :|-> Exp deriving Show
data Exp = Lit Int | Plus Exp Exp | Name Var deriving Show

-- chan :: A -> B -> R ()
-- chan = fix (\ k -> \ a -> \ b -> step (store a >> actionA >> g) >>= \ a' -> 
--                                  step (store b >> actionB >> g) >>= \ b' -> 
--                                     k a' b')

chan = Fix "k"          $
          Lambda "a"    $
             Lambda "b" $
                Step    $
                   

-- To see the states after n steps, type
--
--        go n a b
--
-- at the Haskell prompt where a and b are initial A and B states, resp.
--
-- One gets:
--    HardwiredSeparation> go 100 0 0 channel
--      (50,-50)

go n a b = (runK a b . run . takeR n) channel

takeR :: Int -> R a -> R a
takeR 0 phi             = Done undefined
takeR (n+1) (Pause phi) = Pause (phi >>= (etaK . takeR n))
takeR (n+1) (Done v)    = error "undefined on purpose"

run :: R a -> K a
run (Pause phi) = phi >>= run
run (Done v)    = etaK v

runK :: A -> B -> K t -> (A,B)
runK a b (ST phi) = two_of_three (deI (deST (phi a) b))
   where two_of_three ((t,b),a) = (a,b)
