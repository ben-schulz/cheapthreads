--
-- this is ~/cheapthreads/ctc_working/CT-1.0/TestPrograms/CTMonad.hs
--
-- construction of the environment monad as it might be used
-- in the still-speculative 3-layer CT
--

module CTMonad where

import MonadicConstructions

type Val = Int

type Req = Int
type Rsp = Int


type Addr = Int

type Env = [(Addr, Val)]

type S = StateT Val Id
type E = EnvT Env S
type Re = ReactT Req Rsp E

type CTMonad = Re



--
-- the basic functions we need in CT:
--

step :: E a -> Re a
step x = P (0, \_ -> x >>= (return . D))

--
-- i.e. memory read:
--
readE :: Addr -> E Val
readE a =
  let lkp ((a', v):xs) a = if a == a' then v else lkp xs a
  in
  rdEnv >>= \rho ->
  return (lkp rho a)


--
-- i.e. memory write:
--

writeE :: Env -> S Addr -> S Val -> E Val
writeE xs a v = 
  let f = \(a', v') -> \ys -> if a == a'
                              then (a, v)   : ys
                              else (a', v') : ys
  in
    inEnv (foldr f [] xs) (return v)

{-
writeE :: Env -> Addr -> Val -> E Val
writeE xs a v = 
  let f = \(a', v') -> \ys -> if a == a'
                              then (a, v)   : ys
                              else (a', v') : ys
  in
    inEnv (foldr f [] xs) (return v)
-}

--
-- stateful 'get':
--
get :: S Val
get = g

--
-- stateful 'put':
--
put :: Val -> S ()
put v = u (\_ -> v)
