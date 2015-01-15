--
-- this is ~/cheapthreads/ctc/tests/secureq/secureq.hs
--
-- cleaned-up and simplified version of SecureQ that, more or less,
-- goes through the defunctionalizer
--
-- put here 2009.11.17
--
-- Schulz
--




data Req = Cont | GetPorts
data Rsp = Ack  | Ports Bit Bit Int  -- as noted above

monad K  = StateT(Bit) Deq + StateT(Bit) Enq + StateT(Bit) Busy +
           StateT(Bit) Empty + StateT(Bit) Full + StateT(Addr) HeadPtr +
           StateT(Addr) TailPtr + StateT(Data) Output +
           StateT(Bool) EnqFlag + StateT(Bool)DeqFlag + StateT(Bool) Br +
           StateT(Data) LocalData + StateT(Memory) ExMem
monad R  = ResT K 
monad Re = ReactT Req Rsp K



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

scrub_ram :: Re ()
scrub_ram = step(getHeadPtrK >>= \head_ptr ->
                 getTailPtrK >>= \tail_ptr ->
                 putBrK(tail_ptr < head_ptr)
                ) >>

            -- this is a hacky way of having branching resumptions
            (semifix (tail_ptr_next < head_ptr_next)
              (\k_scrub -> 

                -- zero out:
                step(getTailPtrK >>= \tail_ptr->
                     write ExMem tail_ptr all_zeros >>
                     putTailPtrK (tail_ptr + 1)
                ) >>

                -- do loop test
                step(getHeadPtrK >>= \head_ptr_next ->
                  getTailPtrK >>= \tail_ptr_next ->
                  putBrK(tail_ptr < head_ptr)
                ) >>


              k_scrub
              )
            ) >> reset

        


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

idle :: Re ()

idle = fix (\k -> \ports ->

       step(getEnqK >>= \enq ->
            getFullK >>= \full ->
            putEnqFlagK((enq == One) && (full != One)) >>

            getDeqK >>= \deq -> 
            getEmptyK >>= \empty ->
            putDeqFlagK((deq == 1) && (empty != One))
           ) >>


       -- equivalent to looping 'idle' while conditions met:
       semifix (False == EnqFlagK && False == DeqFlagK)
       (\k0 ->

         step(getEnqK >>= \enq ->
              getFullK >>= \full ->
              putEnqFlagK((enq == One) && (full != One)) >>

              getDeqK >>= \deq -> 
              getEmptyK >>= \empty ->
              putDeqFlagK((deq == 1) && (empty != One))
             ) >>

         k0 ) >>

       -- case for enqueue:
       semifix
       (True == EnqFlagK)
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
         )
       ) >>

       -- case for dequeue:
       semifix
       (True == DeqFlagK)
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
         )

       ) >>

       -- and loop indefinitely

       (k not_used)

       ) -- END FIX



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

--
-- types below are all fucked up
--
-- 2009.11.17 Schulz
--
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


--
-- at this point, the defunctionalizer requires a main function:
--
-- 07.07.09 Schulz
--

main = make_secure


-- END OF CODE --
