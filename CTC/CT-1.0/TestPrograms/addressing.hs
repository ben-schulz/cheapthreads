--
-- this is ~/cheapthreads/CTC/CT-1.0/TestPrograms/addressing.hs
--
-- an attempt to construct a simple, addressable state monad
--
-- put here 2010.01.02
--
-- Schulz
--

module Addressing where

import Control.Monad

--
-- the identity monad:
--
data I a = I a

instance Monad I where
  return v    = I v
  (I x) >>= f = f x

deI :: I a -> a
deI (I x) = x


--
-- the state monad:
--

data St s a = St (s -> (a, s))

deSt :: St s a -> (s -> (a, s))
deSt (St x) = x

instance Monad (St s) where
  return v     = St (\s -> (v, s))
  (St x) >>= f = St (\s -> let (y, s') = (x s) in deSt (f y) s')

--
-- the state monad transformer:
--

data StateT s m a = ST (s -> m (a, s))

deST :: StateT s m a -> (s -> m (a, s))
deST (ST x) = x

instance (Monad m) => Monad (StateT s m) where
  return v     = ST (\s -> return (v, s))
  (ST x) >>= f = ST(\s -> (x s) >>= \(y, s') -> deST (f y) s')


--
-- the lifting:
--
lift :: (Monad m) => m a -> StateT s m a
lift x = ST (\s -> x >>= \v -> return (v, s))

--
-- the state monad operators:
--

get :: St s s
get = St (\s -> (s, s))

put :: (s -> s) -> St s ()
put f = St (\s -> ((), f s))


--
-- the one-bit addressable "memory":
--

type Zero = StateT Int I

type One = StateT Int Zero

type Mem = One

--
-- the separate operators:
--

put0 :: (Int -> Int) -> Zero ()
put0 f = ST (\s -> return ((), f s))

get0 :: Zero Int
get0 = ST (\s -> return (s, s))

put1 :: (Int -> Int) -> One ()
put1 = lift . put0

get1 :: One Int
get1 = lift get0

--
-- and now, the addressing:
--

deref :: Int -> Mem Int
deref 0 = get1
deref 1 = ST (\h -> return (h, h))

point :: Int -> (Int -> Int) -> Mem ()
point 0 f = put1 f
point 1 f = ST (\h -> return ((), f h))

--
-- try it out
--

main = deI (deST ((deST test) 0) 0)

test :: Mem Int
test =
  (point 0 (\_ -> 1)) >>    -- m[0] <= 1
  (point 1 (\_ -> -1)) >>   -- m[1] <= -1
  (deref 0) >>= \i ->       -- i := m[0]
  (deref i)                 -- return m[i]
  
