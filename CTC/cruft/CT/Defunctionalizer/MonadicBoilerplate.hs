module MonadicBoilerplate where

import MonadicConstructions
import CommonTypes
import DefunMonad

-- Compilation monad. 
--type M a = EnvT Bindings (StateT Int I) a

-- A binding matches a recursively defined variable 
-- to its formal parameters.
--type Bindings = Var -> [Var]

etaM :: a -> M a
etaM = return

-- rdEnv and inEnv defined in MonadicConstructions.hs
tweek x v f = \ n -> if n==x then v else f n

gM :: M Int
--gM = liftEnv (ST (\ l -> return (l,l)))
gM = getStoM

uM :: (A -> A) -> M ()
--uM delta = liftEnv $ ST (\l -> return ((),delta l))
uM delta = getStoM >>= putStoM . delta

counter :: M Int -- label generator
counter = uM (\ v -> v + 1) >> gM

{-
runM :: M a -> a
runM phi = fst $ deI $ deST (deENV phi (\ v -> [])) init_label
-}

run phi = runM phi init_binds init_label init_tbs init_code

init_binds :: Bindings
init_binds = (\ v -> [])
init_label :: Int
init_label = 0
init_tbs   :: TypeBindings
init_tbs   = []
init_code  :: Code
init_code  = []