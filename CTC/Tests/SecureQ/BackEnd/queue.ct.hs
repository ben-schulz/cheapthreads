--
-- implementation of a simple queue in CT, using memories
--
-- staging for working out queues in the back-end module
--
-- put here 2009.12.17
--
-- Schulz
--


--
-- data declarations:
--


data Req = NBRead | Valid | WriteOut Bit | ClearMSR

data Rsp = RspNBR Bit | RspValid Bool | OK

monad K =
  StateT(Int) Head +        -- index of the head of the queue
  StateT(Int) Tail +        -- index of the tail of the queue
  StateT(Mem) Q +           -- the queue in memory
  StateT(Int) New +         -- the next item to enqueue
  StateT(Bool) IsValid +      -- flag for a new value
  StateT(InPort) In +       -- a port via which new items arrive
  StateT(OutPort) Out       -- a port to which items are dequeued
  StateT(InPort) MSR_IN +   -- connection from the valid bit of the MSR
  StateT(OutPort) MSR_OUT   -- clear the valid bit of the MSR

monad Re = ReactT Req RspK

--
-- functions:
--

sizeOfInt :: Int
sizeOfInt = 16

sizeOfMem :: Int
sizeOfMem = 4096

getnext :: Re Int
getnext = (signal In NBRead) >>= \v -> step(putNewK v)

putnext :: Int -> Re Int
putnext v = (signal Out (WriteOUt v))

enqueue :: Re Int
enqueue =
  step(
    getNewK >>= \v ->
    getTailK >>= \t ->
    (write Q t v) >>
    putTailK(t + sizeOfInt)
  )

dequeue :: Re Int
dequeue =
  step(
    getHeadK >>= \h ->
    (read Q h) >>= \v ->
    (putnext v) >>
    putHeadK(h + sizeOfInt)
  )

main :: Re ()
main =
  fix (\k ->

    step(putValidK False) >>

    semifix (IsValid)
    (\k' ->
      (signal MSR_IN Valid) >>= \b ->
      step(putIsValidK b) >>
      k'
    )

    getnext >>
    putnext >>

    k
  ) >> return ()
