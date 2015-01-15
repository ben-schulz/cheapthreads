module SecureQ where

import MonadicConstructions
import Qmonad

type SystemInput = (Bit, -- enq port
                    Bit, -- deq port
                    Int  -- data_in (really a bit string)
                   )

type InputBehavior = [SystemInput] -- we assume, more or less, that this
                                   -- is infinite.

data Req = Cont | GetPorts
data Rsp = Ack  | Ports SystemInput

----------------------------------------------------------------------

-- Begin BOILERPLATE
{- 
All of these next definitions should have been defined by MonadLab; hey, it's a 
work-in-progress. In other words, normally, you would have all of these 
constructs defined for you automatically from Qmonad.mlab file.

Here are some things that get defined by MonadLab:

The monad K with morphisms (there are a lot more of these):
    getHeadPtrK :: K Addr
    putHeadPtrK :: Addr -> K ()
For any declaration, 
     monad M = ... + (StateT(<type>) <tag>) + ...
MonadLab defines 
    get<tag>M :: M <type>
    put<tag>M :: <type> -> M ()
-}

setlocMem x v = getMemK >>= putMemK . tweek x v
     where tweek x v sigma = \ loc -> if loc == x then v else sigma loc

getlocMem l = getMemK >>= \ mem -> return (mem l)

fix :: (a -> a) -> a
fix f = f (fix f)

type Re a = ReactT Req Rsp K a
-- type R a  = ResT

stepRe :: K a -> Re a
stepRe phi = P(Cont,\ Ack -> phi >>= (return . D))

sidestepRe :: K (Re a) -> Re a
sidestepRe phi = P(Cont,\ Ack -> phi)

signal :: Req -> Re Rsp
signal q = P(q,return . D)

-- this captures our only explicit use of fix
whileRe :: K Bool -> Re () -> Re ()
whileRe b c = fix $ \ k -> branchRe b (c >> k) (etaRe ())
    where etaRe :: a -> Re a
          etaRe = return

branchRe :: K Bool -> Re a -> Re a -> Re a
branchRe b k1 k2 = P (Cont,r)
    where r = \ Ack -> b >>= \ beta ->
		       if beta then etaK k1
			       else etaK k2
          etaK :: a -> K a
          etaK = return

-- End BOILERPLATE

-- %%%%%%%%%%%%%%%%%%%
-- TRANS 
-- %%%%%%%%%%%%%%%%%%%

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

make_secure = stepRe action >> scrub_ram
   where action = putBusyK One >>
                  setlocMem all_ones all_zeros >>
                  putTailPtrK all_zeros >>
                  putHeadPtrK all_ones 

{-
-- Initialize all RAM entries and then go to reset state
scrub_ram | ( tail_ptr < head_ptr) -> scrub_ram where
{
    mem[tail_ptr]   <= ALL_ZEROS;
    tail_ptr'       <= tail_ptr + 1;
}
scrub_ram -> reset
-}

scrub_ram = whileRe ptr_tst (stepRe zero_out) >> reset
   where ptr_tst  = getTailPtrK >>= \ tail_ptr ->
                    getHeadPtrK >>= \ head_ptr ->
                      return (tail_ptr < head_ptr)
         zero_out = getTailPtrK >>= \ tail_ptr ->
                    setlocMem tail_ptr all_zeros >>
                      putTailPtrK (tail_ptr + 1)
        
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

reset = stepRe action >> idle
  where action = putLocalDataK all_zeros >>
                 putOutputK all_zeros >>
                 putHeadPtrK all_zeros >>
                 putTailPtrK all_zeros >>
                 putEmptyK One >>
                 putFullK Zero

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

idle = signal GetPorts >>= \ (Ports (enq,deq,data_in)) ->
       sidestepRe $
              getEmptyK >>= \ empty ->
              getFullK  >>= \ full ->
              case (enq,deq,empty,full) of
                   (One,_,_,Zero) -> putBusyK One >> 
                                     putLocalDataK data_in >>
                                       return enqueue
                   (_,One,Zero,_) -> putBusyK One >>
                                     getHeadPtrK >>= \ head_ptr ->
                                     putHeadPtrK (head_ptr + 1) >>
                                     setlocMem head_ptr all_zeros >>
                                       return dequeue
                   (_,_,_,_)      -> putBusyK Zero >>
                                       return idle
                  
{-
idle' (enq,deq,data_in) =

idle (_,Zero,data_in) = 
enqueue_branch = putEnqK One >> putFullK Zero
dequeue_branch = putDeqK One >> putFullK Zero
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

enqueue = stepRe action >> update_status
   where action = getTailPtrK >>= \ tail_ptr ->
                  getLocalDataK >>= \ local_data ->
                  setlocMem tail_ptr local_data >>
                  putTailPtrK (tail_ptr + 1)

{-
dequeue -> update_status where
{
    -- Update current value at head of queue
	output'	<= mem[head_ptr];
}
-}

dequeue = stepRe action >> update_status
   where action = getHeadPtrK >>= \ head_ptr ->
                  getlocMem head_ptr >>= \ contents_at_head ->
                  putOutputK contents_at_head

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

update_status = stepRe action >> idle
   where action = getHeadPtrK >>= \ head_ptr ->
                  getTailPtrK >>= \ tail_ptr ->
                     if head_ptr==tail_ptr then equal
                     else 
                        if head_ptr==tail_ptr+1 then almost
                                                else other
         equal  = putEmptyK One >> putFullK Zero >> putBusyK Zero
         almost = putEmptyK Zero >> putFullK One >> putBusyK Zero
         other  = putEmptyK Zero >> putFullK Zero >> putBusyK Zero

---------------------------------
--      Running the System     --
---------------------------------

getreq :: Re a -> K Req
getreq (P(q,r)) = return q

putrsp :: Rsp -> Re a -> K (Re a)
putrsp rsp (P(q,r)) = r rsp

handler (p:ps) phi = stepR body >>= handler ps
     where body = getreq phi >>= \ q ->
                  case q of 
                       Cont     -> putrsp Ack phi
                       GetPorts -> putrsp (Ports p) phi

{-
handler :: InputBehavior -> Re () -> R ()
handler ports (P(Cont,r))      = PauseR (r Ack >>= return . handler ports)
handler (p:ps) (P(GetPorts,r)) = PauseR (r (Ports p) >>= return . handler ps)
-}