--
-- a simple example of how to implement a blocking signal
-- using non-blocking signals
--
-- put here 2009.12.10
--
-- Schulz
--

--
-- In essence, any state shared with an external device can be
-- treated as a port which is read and written by signalling.
-- Conversely, a port can be thought of as shared state,
-- although it cannot be represented here as shared state without
-- contradicting the usual state semantics.
--

monad K = StateT(Bool) Valid +
          StateT(InPort) FSL +
          StateT(InPort) MSR_IN + 
          StateT(OutPort) MSR_OUT +  -- MSR is set/cleared to flag new messages
          StateT(OutPort) Out

monad Re = ReactT Req Rsp K

data Bit = Zero | One

data Req = ReqNBRead | ReqValid | ReqClear | WriteOut Bit

data Rsp = RspNBR Bit | RspValid Bool | OK 


--
-- a simple loop that reads from the port(s):
--

main :: Re ( )

main =

  -- initialize the hand-shaking:
  stepRe (putValidK False) >>

  -- read and process indefinitely:
  fix (\k ->

    -- block until a valid message is signalled:
    semifix (not Valid)
    (\k' -> 

      (signal MSR_IN ReqValid) >>= \v ->
      stepRe (putValidK v) >>
      k'

    ) >>

    -- once valid message confirmed, read from the FSL
    (signal FSL ReqNBRead) >>= \b ->
    (signal MSR_OUT ReqClear) >>
    (signal Out (WriteOut b)) >>

    k

  ) >> return ()
