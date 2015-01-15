module HardwiredSeparation where

import MonadicConstructions

                  -------------------------
                  ---  Monad Hierarchy  ---
                  -------------------------

type A = Int
type B = Int
type Condi x y = StateT x (StateT y I)
--type K = StateT A (StateT B I)
type K = Condi A B
type R = ResT K 

etaR :: a -> R a   --- overloading sucks
etaR = return      

etaK :: a -> K a
etaK = return

                  ------------------
                  ---  Liftings  ---
                  ------------------

step :: K a -> R a
step x = Pause (x >>= (etaK . Done))

----------------------------Begin New Stuff--------------------------------

-- State monad S has only one global register:
type S = StateT Int I
update :: (Int -> Int) -> S ()
update delta = ST (\l -> etaI ((),delta l))
   where etaI = I

-- Just to avoid overloading related confusion:
etaS v = ST (\ s -> I (v,s))

-- There are two kinds of liftings of update into K possible here: "outer" 
-- and "inner". The inner lifting injects (update d) into the first layer of K
-- using liftST and corresponds to the B operations:

inner :: S a -> K a
inner = liftS
    where 
          liftS :: S a -> StateT s S a
--          liftS phi = ST $ \ s0 -> phi >>= \ v -> etaS (v,s0)
          liftS phi = ST $ \ s0 -> phi >>= \ v -> etaS (v,s0)

-- Hardwired version (not used)
updateB = inner . update

-- liftS is just liftST instantiated at S. What it does is it takes an
-- S operation and "wraps" a state transformer around it. I don't have
-- to redefine liftST here, but I did so to remove some Haskell 
-- bureaucracy.

-- The outer lifting executes the S action in the outer layer of K. I.e.,
-- it executes its argument in the A layer:
outer :: S a -> K a
--outer (ST phi) = ST (\ s -> let (I (v,t)) = phi s in etaS (v,t))
outer (ST phi) = ST (\ s -> let (I (v,t)) = phi s in etaS (v,t))

-- Hardwired version (not used)
updateA = outer . update

--- We'll define threads in S as infinite lists of S operations:
incs, decs :: [S ()]
incs = update (\ v -> v+1) : incs
decs = update (\ v -> v-1) : decs
-- N.b., these can interfere if you're not careful.

system :: [S ()] -> [S ()] -> R ()
system (o:os) (i:is) = step (inner i) >> -- N.b., the system decides where
                       step (outer o) >> -- the code executes via its use
                            system os is -- of outer and inner liftings.

sys :: [S ()] -> [S ()] -> R ()
-- outer is A, inner is B
sys = fix (\ k -> \ (o:os) -> \ (i:is) ->
                   step (inner i) >>
                   step (outer o) >>
                      k os is)

gogo n a b = (runK a b . run . takeR n) (sys incs decs)
-- In the original version below, the A thread is executed on the inner and the B thread on the
-- outer layers.

---------------------------End of New Stuff--------------------------------

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

threadA = fix (\ k -> step actionA >> k)
threadB = fix (\ k -> step actionB >> k)

fix :: (a -> a) -> a
fix f = f (fix f)

{- Previous channel definition
channel = step actionA >> step actionB >> channel
-}

channel :: R () -> R () -> R ()
channel (Pause phi1) (Pause phi2) = step phi1 >>= \ k1 ->
                                    step phi2 >>= \ k2 ->
                                      channel k1 k2
                                   
chan :: R () -> R () -> R ()
chan = fix (\ k -> \ (Pause phi1) -> \ (Pause phi2) ->
                   step phi1 >>= \ k1 ->
                   step phi2 >>= \ k2 ->
                      k k1 k2)

-- To see the states after n steps, type
--
--        go n a b
--
-- at the Haskell prompt where a and b are initial A and B states, resp.
--
-- One gets:
--    HardwiredSeparation> go 100 0 0 
--      (50,-50)

go n a b = (runK a b . run . takeR n) (chan threadA threadB)

takeR :: Int -> R a -> R a
takeR 0 phi             = Done undefined
takeR (n+1) (Pause phi) = Pause (phi >>= (etaK . takeR n))
takeR (n+1) (Done v)    = error "undefined on purpose"

run :: R a -> K a
run (Pause phi) = phi >>= run
run (Done v)    = etaK v

runK :: A -> B -> K t -> (A,B)
runK a b (ST phi) = two_of_three (deI (deST (phi a) b))
   where two_of_three ((t,a),b) = (a,b)
