--
-- these are Bill's standard monad definitions
--
-- copied here 2010.01.01
--

module MonadicConstructions where
------------------------------------------------------------------

--- The Id monad:
data Id a = Id a
deId (Id x) = x

instance Monad Id where
   return v    = Id v
   (Id x) >>= f = f x

{-
data S sto a = S (sto -> (a,sto))
deS (S x) = x

instance Monad (S sto) where
   return v      = S $ \ s -> (v,s)
   (S phi) >>= f = S $ \ s0 -> let (v,s1) = phi s0 in deS (f v) s1

g :: S sto sto
g       = S (\ s -> (s,s))

u :: (sto -> sto) -> S sto ()
u delta = S (\ s -> ((), delta s))
-}

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

liftEnv :: Monad m => m a -> EnvT e m a
liftEnv phi = ENV $ \ _ -> phi

--------------- The state monad transformer

data (Monad m) => StateT s m a = ST (s -> m (a,s))
deST (ST x) = x

liftSt :: Monad m => m a -> StateT s m a
liftSt phi = ST $ \ s0 -> phi >>= \ v -> return (v,s0)

instance Monad m => Monad (StateT s m) where
   return v      = ST (\ s0 -> return (v,s0))
   (ST x) >>= f  = ST (\ s0 -> (x s0) >>= \ (y,s1) -> deST (f y) s1) 

u :: (Monad m) => (s -> s) -> StateT s m ()
u f = ST (\ s0 -> return ((),f s0))

g :: (Monad m) => StateT s m s
g = ST (\ s -> return (s,s))

--------------- The resumption monad transformer
data (Monad m) => ResT m a = Done a | Pause (m (ResT m a))
                              
instance Monad m => Monad (ResT m) where
    return v       = Done v
    Done v >>= f   = f v
    Pause m >>= f  = Pause (m >>= \r -> return (r >>= f))

-- The reactive resumption monad transformer
type Dialog q r a = (q,r->a)
data Monad m => ReactT q r m a = D a 
                               | P (Dialog q r (m (ReactT q r m a)))
                                         
instance Monad m => Monad (ReactT q r m) where
    return v      = D v
    D v >>= f     = f v
    P (r,s) >>= f = P (r, \rsp -> (s rsp) >>= \m -> return (m >>= f))  
                                 ---      ^^^"bind" ^^^^^^ "unit" on monad m


-- The "snapshot" resumption monad transformer
data (Monad m) => ObsT obs m a = Dn a | Ps obs (m (ObsT obs m a))
                                         
instance Monad m => Monad (ObsT obs m) where
    return = Dn
    (Dn v) >>= f = f v
    Ps o m >>= f = Ps o (m >>= \r -> return (r >>= f))

-----------------------------------------------------------------------
-----------------------------------------------------------------------
-- The monad transformer of nondeterministic interactive computations

type FinSet a = [a]

data (Monad m) => NReactT q r m a = ND a 
                                  | NP (Dialog q r (m (FinSet (NReactT q r m a))))

instance Monad m => Monad (NReactT q r m) where
    return v       = ND v
    ND v >>= f     = f v
    NP (r,s) >>= f = NP (r, \rsp -> (s rsp) >>= \ms -> return (map (\ m -> m >>= f) ms)) 

-----------------------------------------------------------------------
-----------------------------------------------------------------------
-----------------------------------------------------------------------
