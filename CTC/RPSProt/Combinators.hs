--
-- this is ~/cheapthreads/CTC/RPSProt/Combinators.hs
--
-- Some useful combinators that typify a proposed approach to specifying
-- and verying network protocols using the reactive resumption monad
--
-- put here 2011.02.15
--
-- Schulz
--

module Combinators where

import MonadicConstructions


data Event a = Msg a | Working | Listen

msg :: Event a -> Bool
msg e = case e of
          Msg _   -> True
          _       -> False

finished :: Event a -> Bool
finished e = case e of
               Working -> False
               _       -> True

type Role q p m a = ReactT (Event q) (Event p) m a


step_Re :: (Monad m) => m a -> Role q p m a
step_Re x = P (Working, \_ -> x >>= \v -> return (return v))


send :: (Monad m) => q -> ReactT (Event q) (Event p) m (Event p)
send q = signal (Msg q)

dountil :: (Monad m) => (Event p -> Bool) ->
             ReactT (Event q) (Event p) m (Event p) ->
               ReactT (Event q) (Event p) m (Event p)

dountil t r = r >>= \p -> if t p then return p else dountil t r


waitfor :: (Monad m) => ((Event p) -> Bool) ->
             ReactT (Event q) (Event p) m (Event p)
waitfor t = dountil t (signal Listen)


listen :: (Monad m) => ReactT (Event q) (Event p) m (Event p)
listen = waitfor msg


-- THE END --
