--
-- this is ~/cheapthreads/ctc_working/CT-1.0/CT/MemT.hs
--
-- an attempt to construct the sought-after "memory monad"
--
-- put here 2010.02.25
--
-- Schulz
--

module MemT where



--
-- wherein I re-introduce my favorite example,
-- the 1-bit addressable memory:
--

data (Monad m) => MemT s m a = Mem ((s, s) -> m (a, (s, s)))

dcon (Mem x) = x

--
-- which is virtually identical to the State monad:
--
instance Monad m => Monad (MemT s m) where
  return v      = Mem (\s -> return (v, s))
  (Mem x) >>= f = Mem (\s -> (x s) >>= \(y, s') -> dcon (f y) s')


--
-- ... and moreover admits its standard operators:
--
upd :: (Monad m) => ((s, s) -> (s, s)) -> MemT s m ()
upd f = Mem (\s -> return ((), f s))

get :: (Monad m) => MemT s m (s, s)
get = Mem (\(x, y) -> return ((x, y), (x, y)))

--
-- but here's the subtlety:
--
-- we stipulate that the state component possesses 
-- some further structure so that there is some N, some
-- f, g and some constructor c such that:
--
--   c :: a1 -> ... -> aN -> b
--
--   f :: [1..n] -> (b -> a)
--   g :: [1..n] -> (a -> b -> b)
--
--
-- in this example, c is simply ',' i.e. the cartesian product,
-- 'f' is read and g is write; these give us respective sets of
-- operators:
--
--   { fst :: b -> a  , snd :: b -> a }
--
--   { \z -> \(x, y) -> (z, y) :: a -> b -> b
--     \z -> \(x, y) -> (x, z) :: a -> b -> b
--   }
--
-- more succinctly, the state comes with operators that act
-- as projectors and injectors; the ordinary state monad is
-- then clearly just a trivial case where the injectors and projectors
-- are just 'id'.
--
write :: (Monad m) => Int -> s -> MemT s m ()
write 0 z = upd (\(_, y) -> (z, y))
write 1 z = upd (\(x, _) -> (x, z))

read :: (Monad m) => Int -> MemT s m s
read 0 = get >>= \s -> return (fst s)
read 1 = get >>= \s -> return (snd s)
