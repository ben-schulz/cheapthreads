module MonadicConstructions where
------------------------------------------------------------------

--- The underlying base monad (just Id here):
data I a = I a
deI (I x) = x

instance Monad I where
   return v    = I v
   (I x) >>= f = f x

--------------- The environment monad transformer

data (Monad m) => EnvT env m a = ENV (env -> m a)
deENV (ENV x) = x


instance (Monad m) => Monad (EnvT env m) where
   return v      = ENV (\ e -> return v)
   (ENV x) >>= f = ENV (\ e -> (x e) >>= \ v -> deENV (f v) e)

rdEnv :: (Monad m) => EnvT env m env
rdEnv = ENV (\ e -> return e)

inEnv :: (Monad m) => env -> EnvT env m a -> EnvT env m a
inEnv e (ENV phi) = ENV (\ _ -> phi e)

liftEnv :: (Monad m) => m a -> EnvT env m a
liftEnv x = ENV (\ _ -> x)

--------------- The state monad transformer

data (Monad m) => StateT s m a = ST (s -> m (a,s))
deST (ST x) = x

instance Monad m => Monad (StateT s m) where
   return v      = ST (\ s0 -> return (v,s0))
   (ST x) >>= f  = ST (\ s0 -> (x s0) >>= \ (y,s1) -> deST (f y) s1) 

liftST :: Monad m => m a -> StateT s m a
liftST phi = ST $ \ s0 -> phi >>= \ v -> return (v,s0)

--- N.b. neither resumption monad requires a system pause (e.g., "PauseS") as 
--- there are no system events in the same sense as regular events. 
--- In other words, there is no notion of a system thread per se.
data (Monad m) => ResT m a = Done a | Pause (m (ResT m a))

instance Monad m => Monad (ResT m) where
    return v       = Done v
    Done v >>= f   = f v
    Pause m >>= f  = Pause (m >>= \r -> return (r >>= f))

type React q r a = (q,r->a)
data (Monad m) => ReactT q r m a = D a 
                                 | P (React q r (m (ReactT q r m a)))
                                         
instance Monad m => Monad (ReactT q r m) where
    return v      = D v
    D v >>= f     = f v
    P (r,s) >>= f = P (r, \rsp -> (s rsp) >>= \m -> return (m >>= f))  
                                 ---      ^^^"bind" ^^^^^^ "unit" on monad m

foldM_ :: (Monad m) => [m ()] -> m ()
foldM_ []         = return ()
foldM_ (phi:phis) = phi >> foldM_ phis


mergeND :: [[a]] -> [a]
mergeND = concat 

-- this is a lifting of merge through (StateT Sto)
mergeST merge phis = ST (\ s0 -> merge $ map ((\ phi -> phi s0) . deST) phis)
