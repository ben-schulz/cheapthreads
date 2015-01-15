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

upd :: (Monad m) => (s -> s) -> StateT s m ()
upd f = ST (\ s0 -> return ((),f s0))

get :: (Monad m) => StateT s m s
get = ST (\ s -> return (s,s))

put :: (Monad m) => s -> StateT s m ()
put v = upd (\_ -> v)

--------------- The error-checking monad transformer:


data (Monad m) => ErrT m a = Err | OK a | Nxt (m (ErrT m a))

instance (Monad m) => Monad (ErrT m) where
  return v        = OK v
  (Nxt x) >>= f   = Nxt (x >>= \y -> return (y >>= f))
  (OK v)  >>= f   = f v
  Err     >>= _   = Err


step_Err :: (Monad m) => m a -> ErrT m a
step_Err x = Nxt (x >>= \v -> return (OK v))


prj_err :: (Monad m) => ErrT m a -> m (Maybe a)
prj_err (Nxt x) = x >>= prj_err
prj_err (OK v)  = return (Just v)
prj_err Err     = return Nothing



--------------- The resumption monad transformer
data (Monad m) => ResT m a = Done a | Pause (m (ResT m a))
                              
instance Monad m => Monad (ResT m) where
    return v       = Done v
    Done v >>= f   = f v
    Pause m >>= f  = Pause (m >>= \r -> return (r >>= f))


run_R :: (Monad m) => ResT m a -> m a
run_R (Done v)  = return v
run_R (Pause r) = r >>= run_R


step_R :: (Monad m) => m a -> ResT m a
step_R x = Pause (x >>= return . return)


map_R :: (Monad m) => (m (ResT m a) -> m (ResT m a)) -> ResT m a -> ResT m a
map_R h (Pause x) = step_R (h x) >>= \v -> map_R h v
map_R h (Done v)  = Done v

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

-- The CPS Monad Transformer
data (Monad m) => ContT ans m a = CPS ((a -> m ans) -> m ans)
deCPS (CPS x) = x

instance Monad m => Monad (ContT s m) where
   return v	 = CPS (\ k -> k v)
   (CPS x) >>= f = CPS $ \ k -> x (\ a -> deCPS (f a) k)

liftCPS :: Monad m => m a -> ContT ans m a
liftCPS phi = CPS (phi >>=) 


--
-- First-class continuations are evil, but it's your soul.
-- BTW, this is callcc as defined in Liang, et al. "Modular Interpreters 
-- and Monad Transformers" with a few extra CPS/deCPS thrown in for 
-- good measure.
--
callcc :: (Monad m) => ((a -> ContT ans m b) -> ContT ans m a) -> ContT ans m a
callcc f = CPS $ \ k -> deCPS (f (\ a -> CPS $ \ _ -> k a)) k
