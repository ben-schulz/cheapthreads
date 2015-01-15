--
-- this is ~/cheapthreads/ctc_working/tests/secureq/backend/ports.hs
--
-- a Haskell model of ports implemented as reactive resumptions,
-- meant to serve as a first pass at a CT implentation that will
-- correctly express ports
--
-- put here 2009.12.02
--
-- Schulz
--

module Ports where


data Bit = Zero | One | Nil deriving Show

instance Eq Bit where
  One == One   = True
  Zero == Zero = True
  Nil == Nil   = True
  _ == _       = False
  x /= y       = not $ x == y

type Port = Bit

data Req = NBRead | Valid | WriteOut Bit | ClearMSR deriving Show

data Rsp = RspNBR Bit | RspValid Bool | OK deriving Show

type System = ([Bit], Bool, Port, [Bit])

data Re a = D a | P (Req, Rsp -> Re a)

instance Monad Re where
  return x       = D x
  D v >>= f      = f v
  P (q, r) >>= f = P(q, \rsp -> (r rsp) >>= f)

data R a = Done a | Pause (R a)

instance Monad R where
  return x        = Done x
  (Pause r) >>= f = Pause (r >>= f)
  (Done v) >>= f  = f v

step :: a -> R a
step x = Pause (return x)


runR :: R a -> a
runR (Pause r) = runR r
runR (Done x)  = x

--
-- back-end reads off the port:
--

backend :: Re Req

backend =
  P (NBRead, \(RspNBR b) -> 
    P (Valid, \(RspValid v) -> 
      P (WriteOut (if v then b else Nil), \OK -> 
        P (ClearMSR, \OK -> D ())))) >> backend

--
-- external devices with access to "elsewhere" write to the port:
--

world :: System -> Re Req -> R [Bit]

world (bs, v, p, os) (P (NBRead, r)) =
  step (r (RspNBR p)) >>= world (bs, True, p, os)

world (bs, v, p, os) (P (Valid, r)) =
  case bs of
    (b:bs') -> step (r (RspValid v)) >>= world (bs', v, b, os)
    [ ]     -> step (r (RspValid v)) >>= \(P (WriteOut b, r')) ->
               step (r' OK) >>= \(P (ClearMSR, r'')) ->
               step (r'' OK) >>
               return (b:os)

world (bs, _, p, os) (P (ClearMSR, r)) =
  step (r OK) >>= world (bs, False, p, os)

world (bs, v, p, os) (P (WriteOut b, r)) =
  step (r OK) >>= world (bs, v, p, (b:os))

--
-- try it out:
--

go :: [Bit] -> [Bit]
go (b:bs) =
  let s = (bs, True, b, [])
  in
    runR $ world s backend

go [ ] = [ ]




-- perspective of the external device:

--
-- In this version, the port transmission acts as a reply
-- to an NBR request. The 'Valid' request acts as a signal
-- to the producer that something has been read from the FSL;
-- it may be interpreted as an acknowledgment or as a query.
--
-- Here, 'Valid' is used as an acknowledgment.
--
