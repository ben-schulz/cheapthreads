--
-- this is ~/cheapthreads/ctc/tests/secureq/secureq.old.ct
--
-- Version of SecureQ from over the summer (2009), retaining
-- original notes, half-modifcations and boilerplate.
--
-- Keep here for reference.
--
--
-- put here 2009.11.17 Schulz
--




--
-- SecureQ in CT language
--
-- General differences from the Haskell version:
--
--    1. "Boilerplate" is removed
--    2. where-clauses are removed
--    3. Everything defined at top level must have a type signature
--    4. Pattern matching is pushed into case expressions
--    5. "Bit" and "Memory" are built-in types.
--


--
-- NOTE:
--
-- This was Adam's adaptation of Bill's SecureQ example
-- originally located at:
--
--   ~/mils-hardware/models/securequeues/cheapthreads/SecureQ.hs
--
-- a number of changes have since been made, in the interest
-- of expediting the SecureQ demonstration
--
-- This is the current version.
--
-- The previous version is located at:
--
--  ~/cheapthreads/ctc/ct/tests/secureq/secureq_adam.hs
--
-- 03.07.09 Schulz
--


--
-- 'getlocMem' and 'setlocMem' have been replaced by 'read' and 'write'
-- respectively; these are used as:
--
--    read memory address
--
--    write memory address value
--
-- For now, these are assumed to be primitives; the defunctionalizer
-- will translate them directly into FSMLang syntax
--
-- 17.07.09 Schulz



--
-- FIXME: Maybe we could have a BitString type? Or even BitString[n]?
--
{-

-- Subsuming this to Rsp data type below, to avoid nested
-- patterns noted further down;
--
-- this is a temporary kludge; better, faster, cheaper:
-- choose two
--
-- 03.07.09 Schulz
--

type SystemInput = (Bit, -- enq port
                    Bit, -- deq port
                    Int  -- data_in (really a bit string)
                   )
-}

data Req = Cont | GetPorts
data Rsp = Ack  | Ports Bit Bit Int  -- as noted above

monad K  = StateT(Bit) Deq + StateT(Bit) Enq + StateT(Bit) Busy +
           StateT(Bit) Empty + StateT(Bit) Full + StateT(Addr) HeadPtr +
           StateT(Addr) TailPtr + StateT(Data) Output +
           StateT(Data) LocalData + StateT(Memory) ExMem
monad R  = ResT K 
monad Re = ReactT Req Rsp K

--
-- FIXME: Could just build this in, but I think it would make more sense to
--        define some kind of built-in type constructor like "InputStream",
--        so e.g. here InputBehavior = InputStream SystemInput (where
--        SystemInput is a simple tuple type defined above).
--
--        Of course in the Haskell baseline we'd just have:
--
--            type InputBehavior a = [a]
--
--        :)
--

--type InputBehavior = [SystemInput] -- we assume, more or less, that this
                                     -- is infinite.

{-
addr_width :: Int
addr_width = 2 ^ 9

data_width :: Int
data_width = 2 ^ 8

all_zeros :: Addr
all_zeros = 0

all_ones :: Addr
all_ones = addr_width - 1
-}

addr_width :: Int
addr_width = 512

data_width :: Int
data_width = 256

all_zeros :: Addr
all_zeros = 0

all_ones :: Addr
all_ones = 511
                                     
{-
Each transition is represented by an (co-)equation of the form:
  state = stepRe action >> state'

Here, action is a single update on the device's internal state that corresponds
to the "<=" assignments. The next state is state'.

The idle transition is a little more complicated because it involves the 
reading of input ports (i.e., a signal in the reactive resumption monad).

The whole device is represented by a set of mutually recursive (co-)equations
  state1 = stepRe action1 >> next1
         ...
  staten = stepRe actionn >> nextn

The whole system can be represented as a single term:
  system = fix (\ (state1,...,staten) -> 
                       (stepRe action1 >> next1,...,stepRe actionn >> nextn))

-}

{-
make_secure -> scrub_ram where
{
    -- Assert busy
    busy'   <= '1';

    -- Initialize last RAM entry
    mem[ALL_ONES]   <= ALL_ZEROS;

    -- Reset address counter
    tail_ptr'       <= ALL_ZEROS;

    -- Set "stop" point
    head_ptr'       <= ALL_ONES;
}
-}

make_secure :: Re ()
make_secure = stepRe (putBusyK One >>
--                      setlocMem all_ones all_zeros >>
                      write ExMem all_ones all_zeros >>
                      putTailPtrK all_zeros >>
                      putHeadPtrK all_ones) 
                 >> scrub_ram

{-
-- Initialize all RAM entries and then go to reset state
scrub_ram | ( tail_ptr < head_ptr) -> scrub_ram where
{
    mem[tail_ptr]   <= ALL_ZEROS;
    tail_ptr'       <= tail_ptr + 1;
}
scrub_ram -> reset
-}

--
-- rewritten without the 'whileRe' construct:
--
-- 24.07.09 Schulz
--
--
-- rewritten again, using 'semifix'
--
-- 2009.11.16 Schulz
--
scrub_ram :: Re ()
scrub_ram = step(getHeadPtrK) >>= \head_ptr ->
            step(getTailPtrK) >>= \tail_ptr ->

            (semifix (tail_ptr < head_ptr)
              (\k -> 

                step(getTailPtrK >>= \tail_ptr->
                     write ExMem tail_ptr all_zeros >>
                     putTailPtrK (tail_ptr + 1)
                )

              )
            ) >> reset

{-
scrub_ram = fix(\k ->
                  if getTailPtrK >>= \tail_ptr ->
                     getHeadtrK >>= \head_ptr ->
                     return (tail_ptr < head_ptr)

                  then
                    getTailPtrK >>= \ tail_ptr ->
                    write mem tail_ptr all_zeros >>
                    putTailPtrK (tail_ptr + 1) >>
                    k

                   else
                    reset)
-}

{-
scrub_ram = whileRe (getTailPtrK >>= \ tail_ptr ->
                     getHeadPtrK >>= \ head_ptr ->
                       return (tail_ptr < head_ptr))

                    (stepRe (getTailPtrK >>= \ tail_ptr ->
--                             setlocMem tail_ptr all_zeros >>
                             write mem tail_ptr all_zeros >>
                               putTailPtrK (tail_ptr + 1)))
               >> reset
-}
        
{-
reset -> idle where
{
    -- Initialize all local signals
    local_data'     <= ALL_ZEROS;
    output'         <= ALL_ZEROS;
    head_ptr'       <= ALL_ZEROS;
    tail_ptr'       <= ALL_ZEROS;
    empty'          <= '1';
    full'           <= '0';
} 
-}

reset :: Re ()
reset = stepRe (putLocalDataK all_zeros >>
                putOutputK all_zeros >>
                putHeadPtrK all_zeros >>
                putTailPtrK all_zeros >>
                putEmptyK One >>
                putFullK Zero)
           >> idle

{-
idle | (enq = '1' and full /= '1') -> enqueue where
{
    -- Assert busy
    busy'       <= '1';

    -- Store data to be ENQ'ed
    local_data'	<= data_in;
}

idle | (deq = '1' and empty /= '1') -> dequeue where
{
    -- Assert busy
    busy'       <= '1';

    -- Move pointer to next queue entry
    head_ptr' <= head_ptr + 1;

    -- SECURITY : Zero out current queue entry
    mem[head_ptr]   <= ALL_ZEROS;
}

idle -> idle where
{
    -- De-assert busy
    busy'   <= '0';
}
-}

--
-- FIXME: A few issues here:
--
--    1. What's "sidestepRe" again?
--    2. We're returning functions in places (might be okay)
--    3. _ patterns -- can we just add them to the language, or does that
--       suggest a non-strictness we don't actually have? (I think we can
--       just add them, but have to think about it.)
--
idle :: Re ()

idle = fix (\k ->

       step(getEnqK) >>= \enq ->
       step(getFullK) >>= \full ->
       step(getDeqK) >>= \deq ->
       step(getEmptyK) >>= \empty ->

       -- equivalent to looping 'idle' while conditions met:
       semifix
       (((enq != One) || (full == One)) && ((deq != 1) || (empty == 1)))
       (\k0 -> \enq -> \deq -> \full -> \empty ->

         step(getEnqK) >>= \enq_next ->
         step(getDeqK) >>= \deq_next ->
         step(getFullK) >>= \full_next ->
         step(getEmptyK) >>= \empty_next ->

       k0 enq_next deq_next full_next empty_next) >>

       -- case for enqueue:
       semifix
       ((enq == One) && (full != One))
       (\k1 ->

         step(getTailPtrK >>= \ tail_ptr ->
              getLocalDataK >>= \ local_data ->
              (write mem tail_ptr local_data) >>
              putTailPtrK (tail_ptr + 1)
         ) >>

         -- update status:
         step(getHeadPtrK >>= \ head_ptr ->
              getTailPtrK >>= \ tail_ptr ->
              putEmptyK(if head_ptr == tail_ptr then One else Zero) >>
              putFullK(if head_ptr == tail_ptr then Zero else One) >>
              putBusyK(Zero)
         ) >> k
       ) >>

       -- case for dequeue:
       semifix
       ((deq == One) && (empty != One))
       (\k2 ->

         step(getHeadPtrK >>= \ head_ptr ->
              read ExMem head_ptr >>= \ contents_at_head ->
              putOutputK contents_at_head
         ) >>

       -- update status bits
         step(getHeadPtrK >>= \ head_ptr ->
              getTailPtrK >>= \ tail_ptr ->
              putEmptyK(if head_ptr == tail_ptr then One else Zero) >>
              putFullK(if head_ptr == tail_ptr then Zero else One) >>
              putBusyK(Zero)
         ) >> k

       )

       -- and loop indefinitely

       ) -- END FIX


-- END OF CODE --

{-
idle = signal GetPorts >>= \ ports ->
       case ports of
          --
          -- CT parser fails on this pattern:
          --
          -- reason: nested patterns not supported
          --
          -- 01.07.09 Schulz
          -- 
          (Ports enq deq data_in) ->
             sidestepRe (
                getEmptyK >>= \ empty ->
                getFullK  >>= \ full ->

                case enq of
                  One -> case full of
                           Zero -> putBusyK One >> 
                                   putLocalDataK data_in >>
                                     return enqueue
                           _    -> case deq of
                                     One -> case empty of 
                                              Zero -> putBusyK One >>
                                                      getHeadPtrK >>= \ head_ptr ->
                                                      putHeadPtrK (head_ptr + 1) >>
--                                                      setlocMem head_ptr all_zeros >>
                                                      write mem head_ptr all_zeros >>
                                                        return dequeue
                                     _   -> putBusyK Zero >>
                                              return idle

                  _   -> case deq of
                           One -> case empty of
                                  Zero -> putBusyK One >>
                                          getHeadPtrK >>= \ head_ptr ->
                                          putHeadPtrK (head_ptr + 1) >>
--                                          setlocMem head_ptr all_zeros >>
                                          write mem head_ptr all_zeros >>
                                            return dequeue
                                  _   -> putBusyK Zero >>
                                              return idle
-}


{-
          --
          -- These nested patterns cause the same problem;
          -- this is rewritten above, with the patterns unrolled
          --
          -- 03.07.09 Schulz
          --
                case (enq,deq,empty,full) of
                   (One,_,_,Zero) -> putBusyK One >> 
                                     putLocalDataK data_in >>
                                       return enqueue
                   (_,One,Zero,_) -> putBusyK One >>
                                     getHeadPtrK >>= \ head_ptr ->
                                     putHeadPtrK (head_ptr + 1) >>
--                                     setlocMem head_ptr all_zeros >>
                                     write mem head_ptr all_zeros >>
                                       return dequeue
                   (_,_,_,_)      -> putBusyK Zero >>
                                       return idle
                )
-}

{-
enqueue -> update_status where
{
    -- Store data in queue
	mem[tail_ptr] <= local_data;

    -- Update tail pointer
	tail_ptr' <= tail_ptr + 1;
}
-}

enqueue :: Re ()
enqueue = stepRe (getTailPtrK >>= \ tail_ptr ->
                  getLocalDataK >>= \ local_data ->
--                  setlocMem tail_ptr local_data >>
                  write mem tail_ptr local_data >>
                  putTailPtrK (tail_ptr + 1)
                 )
             >> update_status

{-
dequeue -> update_status where
{
    -- Update current value at head of queue
	output'	<= mem[head_ptr];
}
-}

dequeue :: Re ()
dequeue = stepRe (getHeadPtrK >>= \ head_ptr ->
--                  getlocMem head_ptr >>= \ contents_at_head ->
                  read mem head_ptr >>= \ contents_at_head ->
                  putOutputK contents_at_head
                  )
             >> update_status

{-
-- If head pointer and tail pointer are the same
-- then the queue is empty
update_status | (head_ptr = tail_ptr)-> idle where
{
    empty'  <= '1';
    full'   <= '0';
    busy'   <= '0';
}
-- If the tail pointer "will" (is about to) wrap around
-- to be the same as the head pointer, then the queue is full
update_status | (head_ptr = (tail_ptr + 1)) -> idle where
{
    empty'  <= '0';
    full'   <= '1';
    busy'   <= '0';
}
-- Otherwise the queue is neither full nor empty
update_status -> idle where
{
    empty'  <= '0';
    full'   <= '0';
    busy'   <= '0';
}
-}

update_status :: Re ()
update_status = stepRe (getHeadPtrK >>= \ head_ptr ->
                        getTailPtrK >>= \ tail_ptr ->
                        if head_ptr==tail_ptr
                         then (putEmptyK One >> putFullK Zero >> putBusyK Zero)
                         else if head_ptr==tail_ptr+1
                               then (putEmptyK Zero >> putFullK One >> putBusyK Zero)
                               else (putEmptyK Zero >> putFullK Zero >> putBusyK Zero)
                       )
                   >> idle

---------------------------------
--      Running the System     --
---------------------------------

--
-- we have a hard-wired handler in the defunctionalizer right now --
-- assuming that the hard-wired handler provides the desired
-- functionality, we will omit this handler for now
--
-- 08.07.09 Schulz
--

{-
handler :: InputBehavior -> Re () -> R ()
handler ports phi = case ports of
          --
          -- CT parser fails on this pattern:
          --
          -- reason: no pattern support for infix app
          -- (here: cons)
          --
          -- 01.07.09 Schulz
          -- 
                       (p:ps) -> stepR (
				     getreq phi >>= \ q ->
				     case q of
				        Cont     -> putrsp Ack phi
					GetPorts -> putrsp (Ports p) phi
		                    )
				  >>= \ phi' -> handler ps phi'
-}



--
-- at this point, the defunctionalizer requires a main function:
--
-- 07.07.09 Schulz
--

main = make_secure

--
-- for now, we define 'whileRe' explicitly here;
--
-- original definition in:
--
--  ~/cheapthreads/ct/tests/secureq/original/secureq.hs
--
-- this version modified from original
--
-- 21.07.09 Schulz
--

{-
whileRe :: K Bool -> Re () -> Re ()
whileRe b c = fix (\ k ->
                stepRe (b >>= \beta -> 
                  if beta then (c >> k) else (return ())))
-}


--
-- also, we need setlocMem explicitly defined:
--

--
-- these are being replaced by "taken-for-granted" primitives,
-- 'read', and 'write'
--
-- See:
--
--  ~/cheapthreads/ctc/ct/defunctionalizer/defun.log.txt
--
-- entry for 17.07.09
--
-- 17.07.09 Schulz
--
{-
-- this corresponds to the memory 'sigma' with value 'v'
-- written to location 'x'
tweek x v sigma loc = if loc == x then v else sigma loc

-- set address 'x' to value 'v' in 'mem'
setlocMem x v = getMemK >>= \ mem -> putMemK (tweek x v mem)

-- get value at address 'l' in 'mem'
getlocMem l = getMemK >>= \ mem -> return (mem l)
-}
