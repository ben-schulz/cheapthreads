--
-- this is ~/cheapthreads/ctc/tests/secureq/backend/backend.ct.hs
--
-- a monadic version of Jason's NRL back-end
-- (in './backend.c' and './backend.h')
--
-- put here 2009.11.18
--
-- Schulz
--

--
-- CONSTANTS:
--

_sizeOfHuInt :: Int
_sizeOfHuInt = 4   -- bytes, that is, i.e. 32-bit words

_sizeOfInt :: Int
_sizeOfInt = 4

_sizeOfQItem :: Int
_sizeOfQItem = 5 * _sizeOfInt

_NUM_CHANNELS :: Int
_NUM_CHANNELS = 2

_CHANNEL_NOT_USED :: Int
_CHANNEL_NOT_USED = 0

_CHANNEL_USED :: Int
_CHANNEL_USED = 1

_CMD_HEADER_WORD_WITH_FLAGS :: Int
_CMD_HEADER_WORD_WITH_FLAGS = 3

_CMD_HEADER_WORD_WITH_LENGTH :: Int
_CMD_HEADER_WORD_WITH_LENGTH = 2

_FINAL_TYPE :: Int
_FINAL_TYPE = 1

_DMA_SINC :: Int
_DMA_SINC = 8 * 2 * 2 * 2 * 2 * 2 * 2 * 2

_DMA_DINC :: Int
_DMA_DINC = 4 * 2 * 2 * 2 * 2 * 2 * 2 * 2

_DMA_DSIZE_WORD :: Int
_DMA_DSIZE_WORD = 4

_DMA_ERROR_MASK :: Int
_DMA_ERROR_MASK = 2

_DMA_BUSY_MASK :: Int
_DMA_BUSY_MASK = 8 * 2 * 2 * 2 * 2 * 2 * 2 * 2

_DMA_DONE_MASK :: Int
_DMA_DONE_MASK = 1

_CHAN_MASK :: Int
_CHAN_MASK = 255

_CHAN_SHIFT :: Int
_CHAN_SHIFT = 16

_DMA_LENGTH_SHIFT :: Int
_DMA_LENGTH_SHIFT = 0

_DMA_LENGTH_MASK :: Int
_DMA_LENGTH_MASK = 15 + (15 * 16) + (15 * 256) + (15 * 16 * 256)

_DMA_OFFSET_SHIFT :: Int
_DMA_OFFSET_SHIFT = 16

_DMA_OFFSET_MASK :: Int
_DMA_OFFSET_MASK =  15 + (15 * 16) + (15 * 256) + (15 * 16 * 256)

_DATA_INCL_MASK :: Int
_DATA_INCL_MASK = 4 * 2 * 2 * 2 * 2 * 2 * 2

_MSG_AVAIL_MASK :: Int
_MSG_AVAIL_MASK = 1 * 2 * 2 * 2 * 2 * 2 * 2 * 2


_NORMAL_TYPE :: Int
_NORMAL_TYPE = 0

_OP_MASK :: Int
_OP_MASK = 255

_OP_SHIFT :: Int
_OP_SHIFT = 24

_OP_DMA_BDONE :: Int
_OP_DMA_BDONE = 5

_OP_DMA_FDONE :: Int
_OP_DMA_FDONE = 9

_OP_FE_SEG_DONE :: Int
_OP_FE_SEG_DONE = 2

_OP_DATA_ADDR :: Int
_OP_DATA_ADDR = 3

_OP_DMA_REQ :: Int
_OP_DMA_REQ = 1

_OP_CHANNEL_GRANT :: Int
_OP_CHANNEL_GRANT = 7

_OP_CHANNEL_RESERVE :: Int
_OP_CHANNEL_RESERVE = 0

_OP_CHANNEL_DENY :: Int
_OP_CHANNEL_DENY = 8

_OP_BE_SEG_DONE :: Int
_OP_BE_SEG_DONE = 6

--
-- in the original, these appear to rely on Microblaze-specific,
-- built-in constants; the values here are arbitrarily chosen
--
_DMA_BASEADDR_F :: Int
_DMA_BASEADDR_F = 0


_DMA_BASEADDR_B :: Int
_DMA_BASEADDR_B = 0

_DMAMIR :: Int
_DMAMIR = 8


_DMACR :: Int
_DMACR = 16

_SRCADDR :: Int
_SRCADDR = 24

_DSTADDR :: Int
_DSTADDR = 32

_DMALENGTH :: Int
_DMALENGTH = 40

_DMASTATUS :: Int
_DMASTATUS = 48

_DMAISR :: Int
_DMAISR = 56

_DMAIER :: Int
_DMAIER = 64


_DMA_RESET :: Int
_DMA_RESET = 127

--
-- TYPES
--

data Req = BRead | NBRead | Valid | Cont

data Rsp = RspBread Int | RspNBR Int | RspValid Bool | Ack Int

data Bit = Zero | One

type Bitstring = [Bit]

--
-- the signals:
--

monad K =

-- variables used in 'main':

  StateT(Bool) Invalid +
  StateT(Req) Arg +

-- the 'back-end status' structure:

  StateT(Int) ChanReqStatus1 +
  StateT(Int) ChanReqStatus2 +
  StateT(Int) ActiveChannel1 +
  StateT(Int) ActiveChannel2 +

  StateT(Bool) CurrTransferValid_F +
  
  StateT(Bool) Exists_B +
  StateT(Bool) Ready_B +
  StateT(Int) MaxTransferSize_B +
  StateT(Int) CurrTransferSize_B +
  StateT(Int) DestAddr_B +

  -- the DMA signal register addresses (FE -> BE):

  StateT(Int) DMAMir_F +
  StateT(Int) DMACtrl_F +
  StateT(Int) SrcAddr_F +
  StateT(Int) DestAddr_F +
  StateT(Int) DMALength_F +
  StateT(Int) DMAStatus_F +
  StateT(Int) DMA_ISR_F +
  StateT(Int) DMA_IER_F +

  -- the DMA signal register addresses (BE -> FE):

  StateT(Int) DMAMir_B +
  StateT(Int) DMACtrl_B +
  StateT(Int) SrcAddr_B +
  StateT(Int) DestAddr_B +
  StateT(Int) DMALength_B +
  StateT(Int) DMAStatus_B +
  StateT(Int) DMA_ISR_B +
  StateT(Int) DMA_IER_B +

  -- request queue (FE -> BE):

  StateT(Int) QHead_F +
  StateT(Int) QTail_F +

    -- the DMA request portion of the queue (FE -> BE):
    --
    -- these components hold either a new item to be enqueued
    -- (i.e. copied) into QF, or a newly dequeued item just removed from QF
    --
    StateT(Int) ChanId_F +
    StateT(Int) TransType_F +
    StateT(Int) ReqCtrl_F +
    StateT(Int) ReqSrcAddr_F +
    StateT(Int) ReqDestAddr_F +
    StateT(Int) ReqLength_F +

  -- queue itself is implemented as a memory:

  StateT(Mem) QF +

  -- request queue (BE -> FE):

  StateT(Int) QHead_B +
  StateT(Int) QTail_B +

    -- the DMA request portion of the queue (BE -> FE):
    --
    -- these components hold either a new item to be enqueued
    -- (i.e. copied) into QF, or a newly dequeued item just removed from QF
    --
    StateT(Int) ChanId_B +
    StateT(Int) TransType_B +
    StateT(Int) ReqCtrl_B +
    StateT(Int) ReqSrcAddr_B +
    StateT(Int) ReqDestAddr_B +
    StateT(Int) ReqLength_B +

  -- queue itself is implemented as a memory:

  StateT(Mem) QB +

  --
  -- pointers to PEIP interfaces;
  -- these are momentarily hard-coded as two separate sets
  -- of signals; the original C version has an array
  --
  StateT(Int) PEIP_CMD_Header_In1 +
  StateT(Int) PEIP_CMD_Header_Out1 +
  StateT(Int) PEIP_Data_In1 +
  StateT(Int) PEIP_Data_Out1 +

  StateT(Int) PEIP_CMD_Header_In2 +
  StateT(Int) PEIP_CMD_Header_Out2 +
  StateT(Int) PEIP_Data_In2 +
  StateT(Int) PEIP_Data_Out2 +

-- variables used in 'init':

  StateT(Int) Counter +
  StateT(Int) DMA_Cfg_F +  -- base address of the DMA core (FE -> BE)
  StateT(Int) DMA_Cfg_B +  -- base address of the DMA core (BE -> FE)

-- variables used in 'handle_reply':

  StateT(Int) Flags +
  StateT(Int) FlagPointer +
  StateT(Bool) IsResponse1 +
  StateT(Bool) IsResponse2 +

-- variables used in 'handle_response':

  StateT(Int) HRspFlags +
  StateT(Int) CmdReq +

-- variables used in 'advance_fe_to_be_queue'

  StateT(Int) DMA_FDone_Msg +

-- variables used in 'advance_be_to_fe_queue'

  StateT(Int) DMA_BDone_Msg +

-- variables used in 'process_request':

  StateT(Int) OpCode +

-- variables used in 'reserve_channel':

  StateT(Int) RCChannelId +
  StateT(Int) RCMsg +

-- variables used in 'fe_dma_request':

  StateT(Int) FDRMsg1 +
  StateT(Int) FDRMsg2 +
  StateT(Int) FDRChannelId +
  StateT(Int) FDR_DMALength +
  StateT(Int) FDR_DMAOffset +
  StateT(Int) FDR_DMAAddress +

-- variables used in 'fe_segment_done':

  StateT(Int) FSD_ChannelId +
  StateT(Int) FSD_Msg1 +
  StateT(Int) FSD_Msg2 +
  StateT(Int) FSD_Msg3 +
  StateT(Int) FSD_Msg4 +
  StateT(Int) FSD_Msg5 +
  StateT(Int) FSD_CMDHeaderPtr +
  StateT(Int) FSD_OriginalMsg +

-- variables used in 'fe_data_addr':

  StateT(Int) FDA_Msg1 +
  StateT(Int) FDA_DMALength +
  StateT(Int) FDA_DestAddr +
  StateT(Int) FDA_ChannelId +

-- IO ports:

  StateT(InPort) FSL_IN +
  StateT(OutPort) FSL_OUT +
  StateT(InPort) MSR_IN +    -- input from the MSR, i.e. 'Valid' bit
  StateT(OutPort) MSR_OUT +  -- write-out to the MSR, i.e. to clear 'Valid'

-- the PEIP is a shared memory:

  StateT(Mem) PEIP

--
-- CODE BEGINS:
-- 

main :: R ()
main =

  init >>

  -- do indefinitely:
  fix (\k ->
  

    step(putInvalidK(True)) >>

    -- while data is invalid, keep trying
    semifix (InvalidK)
    (\k0 ->

      -- non-blocking read:
      nbread_fsl >>    -- puts result of the read in 'Arg'
      fsl_isinvalid >> -- puts result in 'Valid'

    -- if invalid, do background processing and go around again

      background >> k0)


    -- otherwise, acknowledge service request and then do background

    step(getArgK >>= \n -> return n) >>= \n' -> 
    process_request n >>
    background >>
    k

  ) >>

  return ()

-- end main


--
-- nbread_fsl:
--
-- non-blocking read from the FSL input port
--
-- as in Jason's code, we assume that 'Arg' may serve
-- as a source or sink for the FSL operation; this is standard
-- in the Xilinx built-in macro referenced in the original
--
-- (see Xilink EDK 9.2i OS Libraries reference manual)
--

nbread_fsl :: Re Rsp
nbread_fsl = (signal FSL_IN NBRead) >>= \rsp -> stepRe(putArgK rsp)


fsl_isinvalid :: Re Bool
fsl_isinvalid =
  (signal MSR_IN Valid) >>= \rsp ->
  stepRe(putValidK rsp >>= \v -> return (1 == v))


--
-- queue operations:
--

enqueue_F :: Re ()
enqueue_F =
  step(
    getQTail_FK >>= \t ->
    getChanId_FK >>= \i ->
    (write QF t i) >>
    getTransType_FK >>= \y ->
    (write QF (t + _sizeOfInt) y) >>
    getReqCtrl_FK >>= \c ->
    (write QF (t + (2 * _sizeOfInt)) c) >>
    getReqSrcAddr_FK >>= \s ->
    (write QF (t + (3 * _sizeOfInt)) s) >>
    getReqDestAddr_FK >>= \d ->
    (write QF (t + (4 * _sizeOfInt)) d) >>
    getReqLength_FK >>= \l ->
    (write QF (t + (5 * _sizeOfInt)) l) >>
    return t
  ) >>= \t' ->

  step(putQTail_BK(t' + _sizeOfQItem)) >> return ()

enqueue_B :: Re ()
enqueue_B =
  step(
    getQTail_BK >>= \t ->
    getChanId_BK >>= \i ->
    (write QB t i) >>
    getTransType_BK >>= \y ->
    (write QB (t + _sizeOfInt) y) >>
    getReqCtrl_BK >>= \c ->
    (write QB (t + (2 * _sizeOfInt)) c) >>
    getReqSrcAddr_BK >>= \s ->
    (write QB (t + (3 * _sizeOfInt)) s) >>
    getReqDestAddr_BK >>= \d ->
    (write QB (t + (4 * _sizeOfInt)) d) >>
    getReqLength_BK >>= \l ->
    (write QB (t + (5 * _sizeOfInt)) l) >>
    return t
  ) >>= \t' ->

  step(putQTail_BK(t' + _sizeOfQItem)) >> return ()


dequene_F :: Re ()
dequeue_F =
  step(
    getQHead_FK >>= \h ->
    (read QF h) >>= \i ->
    putChanId_FK(i) >>
    (read QF (h + _sizeOfInt)) >>= \y ->
    putTransType_FK(y) >>
    (read QF (h + (2 * _sizeOfInt))) >>= \c ->
    putReqCtrl_FK(c) >>
    (read QF (h + (3 * _sizeOfInt))) >>= \s ->
    putReqSrcAddr_FK(s) >>
    (read QF (h + (4 * _sizeOfInt))) >>= \d ->
    putReqDestAddr_FK(d) >>
    (read QF (h + (5 * _sizeOfInt))) >>= \l ->
    putReqLength_FK(l) >>
    return h
  ) >>
  step(putQHead_FK(h + _sizeOfQItem)) >> return ()

dequene_B :: Re ()
dequeue_B =
  step(
    getQHead_BK >>= \h ->
    (read QB h) >>= \i ->
    putChanId_BK(i) >>
    (read QB (h + _sizeOfInt)) >>= \y ->
    putTransType_BK(y) >>
    (read QB (h + (2 * _sizeOfInt))) >>= \c ->
    putReqCtrl_BK(c) >>
    (read QB (h + (3 * _sizeOfInt))) >>= \s ->
    putReqSrcAddr_BK(s) >>
    (read QB (h + (4 * _sizeOfInt))) >>= \d ->
    putReqDestAddr_BK(d) >>
    (read QB (h + (5 * _sizeOfInt))) >>= \l ->
    putReqLength_BK(l) >>
    return h
  ) >>
  step(putQHead_BK(h + _sizeOfQItem)) >> return ()



--
-- background:
--
-- do background processing for each time around the main loop,
-- i.e. for those times when when the back-end is not handling active
-- requests
--

background :: R ()
background =

  --
  -- Poll active channels for PEIP replies:
  --
  semifix (ActiveChannel1 == _CHANNEL_USED)
  (\k3 ->
    handle_reply1 >>
    step(putActiveChannel1K(_CHANNEL_NOT_USED))
  ) >>

  semifix (ActiveChannel2 == _CHANNEL_USED)
  (\k4 ->
    handle_reply2 >>
    step(putActiveChannel2K(_CHANNEL_NOT_USED))
  ) >>


  --
  -- Poll active channels for PEIP "responses"
  --
  -- (still unclear how 'reply' is different from 'response' 2009.12.01)
  -- 
  --

  is_response1 >>
  semifix (IsResponse1)
  (\k5 ->
    handle_response1
  ) >>

  is_response2 >>
  semifix (IsResponse2)
  (\k6 ->
    handle_response2
  ) >>
  
  advance_dma_transfers() >>

  return ()

--
-- handle_reply:
--

handle_reply1 :: Re ()
handle_reply1 =

  -- setup the request:
  step(
    getPEIP_CMD_Header_In1K >>= \v -> 
    putFlagPointerK(v + _CMD_HEADER_WORD_WITH_FLAGS) >>
    putChanId_BK(1) >>
    putTransType_BK(_NORMAL_TYPE) >>
    putReqCtrl_BK(_DMA_SINC ||| _DMA_DINC ||| _DMA_DSIZE_WORD) >>
    getPEIP_CMD_Header_In1K >>= \a ->
    putSrcAddr_BK(a) >>
    putReqDestAddr_BK(9 * 256 + 9 * 16 + 9) >>
    putReqLength_BK(5 * _sizeOfHuInt)
  ) >>

  -- enqueue it:
  enqueue_B >>

  semifix (0 == (FlagPointer &&& _DATA_INCL_MASK))
  (\k7 ->

    step(
      putChanId_BK(1) >>
      putTransType_BK(_NORMAL_TYPE) >>
      putReqCtrl_BK(_DMA_SINC ||| _DMA_DINC ||| _DMA_DSIZE_WORD) >>
      getPEIP_CMD_Header_In1K >>= \a' ->
      putReqSrcAddr_BK(a') >>
      putReqDestAddr_BK(9 * 256 + 9 * 16 + 9) >>
      (read PEIP (a' + _CMD_HEADER_WORD_WITH_LENGTH)) >>= \l ->
      putReqLength_BK(l)
    ) >>

    enqueue_B
  ) >>
  return ()

--
-- once again, easier for our purposes to just make these
-- particular to signals
--

handle_reply2 :: R ()
handle_reply2 =

  -- setup the request:
  step(
    getPEIP_CMD_Header_In2K >>= \v -> 
    putFlagPointerK(v + _CMD_HEADER_WORD_WITH_FLAGS) >>
    putChanId_BK(2) >>
    putTransType_BK(_NORMAL_TYPE) >>
    putReqCtrl_BK(_DMA_SINC ||| _DMA_DINC ||| _DMA_DSIZE_WORD) >>
    getPEIP_CMD_Header_In2K >>= \a ->
    putSrcAddr_BK(a) >>
    putReqDestAddr_BK(9 * 256 + 9 * 16 + 9) >>
    putReqLength_BK(5 * _sizeOfHuInt)
  ) >>

  -- enqueue it:
  enqueue_B >>

  semifix (0 == (FlagPointer &&& _DATA_INCL_MASK))
  (\k8 ->

    step(
      putChanId_BK(2) >>
      putTransType_BK(_NORMAL_TYPE) >>
      putReqCtrl_BK(_DMA_SINC ||| _DMA_DINC ||| _DMA_DSIZE_WORD) >>
      getPEIP_CMD_Header_In2K >>= \a' ->
      putReqSrcAddr_BK(a') >>
      putReqDestAddr_BK(9 * 256 + 9 * 16 + 9) >>
      (read PEIP (a' + _CMD_HEADER_WORD_WITH_LENGTH)) >>= \l ->
      putReqLength_BK(l)
    ) >>

    enqueue_B
  ) >>
  return ()


--
-- is_response:
--

is_response1 :: Re Bool
is_response1 = 
  stepRe(
    getPEIP_CMD_Header_Out1K
  ) >>= \cmd ->

  semifix (not (0 == ((cmd + _CMD_HEADER_WORD_WITH_FLAGS) &&& _MSG_AVAIL_MASK)))
  (\k9 ->
    step(putIsResponse1K(True))
  ) >>

  semifix (0 == ((cmd + _CMD_HEADER_WORD_WITH_FLAGS) &&& _MSG_AVAIL_MASK))
  (\k10 ->
    step(putIsResponse1K(False))
  )

{-
    putIsResponse1K(
      if (not (0 == ((cmd + _CMD_HEADER_WORD_WITH_FLAGS) &&& _MSG_AVAIL_MASK)))
      then
        True
      else
        False
    )
-}

is_response2 :: Re Bool
is_response2 = 
  stepRe(
    getPEIP_CMD_Header_Out2K
  ) >>= \cmd ->

  semifix (not (0 == ((cmd + _CMD_HEADER_WORD_WITH_FLAGS) &&& _MSG_AVAIL_MASK)))
  (\k11 ->
    putIsResponse1K(True)
  ) >>

  semifix (0 == ((cmd + _CMD_HEADER_WORD_WITH_FLAGS) &&& _MSG_AVAIL_MASK))
  (\k12 ->
    putIsResponse1K(False)
  )
{-
    putIsResponse2K(
      if (not (0 == ((cmd + _CMD_HEADER_WORD_WITH_FLAGS) && _MSG_AVAIL_MASK)))
      then
        True
      else
        False
    )
-}

--
-- handle_response:
--

handle_response1 :: Re ()
handle_response1 =

  step(
    getPEIP_CMD_Header_Out1K >>= \v ->
    putHRspFlagsK(v + _CMD_HEADER_WORD_WITH_FLAGS) >>= \v' ->
    putChanId_BK(1) >>
    putReqCtrl_BK(_DMA_SINC ||| _DMA_DINC ||| _DMA_DSIZE_WORD) >>
    putReqSrcAddr_BK(v) >>
    putReqDestAddr_BK(9 + 9 * 16 + 9 * 256) >>
    putReqLength_BK(5 * _sizeOfHuInt) >>

    putTransType_BK(
      if (0 == (v' &&& _DATA_INCL_MASK))
      then _FINAL_TYPE
      else _NORMAL_TYPE
    )

  ) >>

  -- enqueue the command header, which is always done:
  enqueue_B >>

  -- then check to see if data is included as well, and
  -- if so, enqueue it too
  semifix (0 == HRspFlags)
  (\k13 -> 

    step(
      putTransType_BK(_FINAL_TYPE) >>
      putReqCtrl_BK(_DMA_SINC ||| _DMA_DINC ||| _DMA_DSIZE_WORD) >>

      getPEIP_Data_Out1K >>= \a ->
      putReqSrcAddr_BK(a) >>

      putReqDestAddr_BK(9 * 256 + 9 * 16 + 9) >>    -- i.e. 0x999

      putReqLength_BK(a + _CMD_HEADER_WORD_WITH_LENGTH)
    ) >>

    enqueue_B

  ) >>

  return ()
  -- end of function

handle_response2 :: Re ()
handle_response2 =

  step(
    getPEIP_CMD_Header_Out2K >>= \v ->
    putHRspFlagsK(v + _CMD_HEADER_WORD_WITH_FLAGS) >>= \v' ->
    putChanId_BK(2) >>
    putReqCtrl_BK(_DMA_SINC ||| _DMA_DINC ||| _DMA_DSIZE_WORD) >>
    putReqSrcAddr_BK(v) >>
    putReqDestAddr_BK(9 + 9 * 16 + 9 * 256) >>
    putReqLength_BK(5 * _sizeOfHuInt) >>

    putTransType_BK(
      if (0 == (v' &&& _DATA_INCL_MASK))
      then _FINAL_TYPE
      else _NORMAL_TYPE
    )

  ) >>

  -- enqueue the command header, which is always done:
  enqueue_B >>

  -- then check to see if data is included as well, and
  -- if so, enqueue it too
  semifix (0 == HRspFlags)
  (\k14 -> 

    step(
      putTransType_BK(_FINAL_TYPE) >>
      putReqCtrl_BK(_DMA_SINC ||| _DMA_DINC ||| _DMA_DSIZE_WORD) >>

      getPEIP_Data_Out2K >>= \a ->
      putReqSrcAddr_BK(a) >>

      putReqDestAddr_BK(9 * 256 + 9 * 16 + 9) >>    -- i.e. 0x999

      putReqLength_BK(a + _CMD_HEADER_WORD_WITH_LENGTH)
    ) >>

    enqueue_B

  ) >>

  return ()
  -- end of function



--
-- advance_dma_transfers:
--

advance_dma_transfers :: Re ()
advance_dma_transfers =
  advance_fe_to_be_queue >>
  advance_be_to_fe_queue >>
  return ()


advance_fe_to_be_queue :: Re () 
advance_fe_to_be_queue =
  is_dma_available >>= \b ->
  is_dma_error >>= \b' ->

  --
  -- if device is idle, and the current transfer is valid,
  -- and there was an error:
  --

  step(getCurrTransferValid_FK) >>= \b'' ->
  semifix (b && b' && b'')
  (\k15 ->

    -- if error, retry with the signals already in place
    perform_dma_transfer

  ) >>

  is_dma_done >>= \b'' ->

  --
  -- otherwise, if no error and the transfer is done:
  --
  semifix (b && (not b') && b'' && CurrTransferValid_F)
  (\k16 ->

    -- form the DMA message : 

    step(
      putDMA_FDone_MsgK(0) >>= \v ->
      putDMA_FDone_MsgK(_set_opcode _OP_DMA_FDONE v) >>= \v' ->
      putDMA_FDone_MsgK(_set_channel 1 v') >>= \v'' ->
      return v''
    ) >>= \v0 ->

    -- send it
    (signal FSL_OUT (Ack v0)) >>

    -- invalidate current transfer, since it is now complete
    step(
      putCurrTransferValid_FK(False)
    )
  ) >>

  -- check for any queued requests;
  -- if any, dequeue the first and start a new transfer
  not_empty_F >>= \e ->
  semifix ((not CurrTranfserValid_F) && e)
  (\k17 ->

    dequeueDataReq >>
    step(putCurrTransferValid_FK(True)) >>
    perform_dma_transfer

  ) >> return ()
  -- end of the function


advance_be_to_fe_queue :: Re ()
advance_be_to_fe_queue =
  is_dma_available >>= \b ->
  is_dma_error >>= \b' ->

  --
  -- if device is idle, and the current transfer exists,
  -- and there was an error:
  --
  semifix (b && b' && Exists_B)
  (\k18 ->

    -- if there was an error, retry
    perform_dma_transfer

  ) >>

  --
  -- otherwise, if no error and the transfer is done:
  --
  semifix (b && (not b') && b'' && CurrTransferValid_F)
  (\k19 ->

    --
    -- for the acknowledgment to the DMA:
    --
    step(
      putDMA_BDone_MsgK(0) >>= \v ->
      putDMA_BDone_MsgK(_set_opcode _OP_DMA_BDONE v) >>= \v' ->
      putDMA_BDone_MsgK(_set_channel 1 v') >>= \v'' ->
      getCurrTransferSize_BK >>= \u ->
      putDMALength_BK(u) >>
      return v''
    ) >>= \v0 ->

    -- send it
    (signal FSL_OUT (Ack v0)) >>

    -- transfer the first chunk of data:
    step(
      getDMALength_BK >>= \w ->
      getCurrTransferSize_BK >>= \w' ->
      putDMALength_BK(w - w')
    )

  ) >>

  --
  -- if more data remains, leave request valid but "not ready":
  --
  semifix (0 < DMALength_B)
  (\k20 ->

    step(
      putReady_BK(False) >>

      putDMA_Data_Out_MsgK(0) >>= \t ->
      putDMA_Data_Out_MsgK(_set_opcode _OP_DATA_OUT t) >>= \t' ->
      putDMA_Data_Out_MsgK(_set_channel 1 t') >>= \t'' ->
      return t''
    ) >>= \t''' ->

    (signal FSL_OUT (Ack t'''))
  ) >>

  -- else if final message:
  semifix((not (0 < DMALength_B)) && _FINAL_TYPE == TransType_B)
  (\k21 ->

    -- invalidate current transfer so another can take place
    step(
      putExists_BK(False) >>

      getChanId_BK >>= \i ->
      return i
    )

  ) >>= \i' ->

  --
  -- what you see here is a really awkward way of dealing with the
  -- limited language constructs available:
  --
  semifix ((not (0 < DMALength_B)) && (_FINAL_TYPE == TransType_B) && 1 == i')
  (\k22 ->
     step(
       getPEIP_CMD_Header_Out1K >>= \a ->
       putPEIP_CMD_Header_Out1K(a + _CMD_HEADER_WORD_WITH_FLAGS) >>= \a' ->
       putPEIP_CMD_Header_Out1K(a' ||| _MSG_READ_MASK)
     )
  ) >>

  semifix ((not (0 < DMALength_B)) && (_FINAL_TYPE == TransType_B) && 2 == i')
  (\k23 ->
     getPEIP_CMD_Header_Out2K >>= \a ->
     putPEIP_CMD_Header_Out2K(a + _CMD_HEADER_WORD_WITH_FLAGS) >>= \a' ->
     putPEIP_CMD_Header_Out2K(a' ||| _MSG_READ_MASK)
  ) >>

  -- continuing,

  not_empty_B >>= \e ->
  semifix (not (0 == (Exists_B &&& e)))
  (\k24 ->

    dequeueDataReq >>

    step(
      putExists_BK(True) >>
      putDMA_Data_Out_MsgK(0) >>= \m ->
      putDMA_Data_Out_MsgK(_set_opcode _OP_DATA_OUT t) >>= \m' ->
      putDMA_Data_Out_MsgK(_set_channel 1 m') >>= \m'' ->
      return m''
    ) >>= \m''' ->

    (signal FSL_OUT (Ack m'''))

  ) >> return ()
  -- end function



--
-- this assumes that the appropriate signals are
-- already in place; the function only starts the transfer
--
perform_dma_transfer :: Re Int
perform_dma_transfer =
  step(

    -- transfer starts as soon as non-zero value
    -- appears in the DMA length register
    getReqLength_FK >>= \l ->
    putDMALength_FK(l)

  )

  

not_empty_F :: Re Bool
not_empty_F =
  step(
    getQHead_FK >>= \h ->
    getQTail_FK >>= \t ->
    return(
      if (h == t)
      then False
      else True
    )
  )


is_dma_available :: Re Bool
is_dma_available =
  step(
    getDMAStatus_BK >>= \s ->
    return (_DMA_BUSY_MASK) >>= \m ->
    return(
      if (0 == (s &&& m))
      then True
      else False
    )
  )

is_dma_error :: Re Bool
is_dma_error =
  step(
    getDMA_ISR_FK >>= \v ->
    return(
      if (0 == (v &&& _DMA_ERROR_MASK))
      then False
      else True
    )
  )

is_dma_done :: Re Bool
is_dma_done =
  step(
    getDMA_ISR_FK >>= \v ->
    return(
      if (0 == (v &&& _DMA_DONE_MASK))
      then False
      else True
    )
  )

--
-- init:
--
--
-- there are four things to initialize:
--
--  + the direct memory access (DMA) deviceA
--  + the DMA queue
--  + the PEIP interface
--  + the channel data
--

init :: Re ()
init =

--
-- CALL TO 'dma_create':
--
  -- initialize DMA (FE -> BE)
  step(
    putDMA_CFG_FK(_DMA_BASEADDR_F) >>
    putDMAMir_FK(_DMA_BASEADDR_F + _DMAMIR) >>
    putDMACtrl_FK(_DMA_BASEADDR_F + _DMACR) >>
    putSrcAddr_FK(_DMA_BASEADDR_F + _SRCADDR) >>
    putDestAddr_FK(_DMA_BASEADDR_F + _DSTADDR) >>
    putDMALength_FK(_DMA_BASEADDR_F + _DMALENGTH) >>
    putDMAStatus_FK(_DMA_BASEADDR_F + _DMASTATUS) >>
    putDMA_ISR_FK(_DMA_BASEADDR_F + _DMAISR) >>
    putDMA_IER_FK(_DMA_BASEADDR_F + _DMAIER)
  ) >>


  --
  -- NOTE:
  -- 
  -- in the original, something like this is used to 'reset' the
  -- the device; this appears to be playing on some highly specific
  -- convention that I'm not sure I fully understand.
  --
  -- I attempt to simulate it here using three different ticks
  -- to do the three separate assignments
  --

  step(putDMAMir_FK(0)) >>
  step(putDMAMir_FK(_DMA_RESET)) >>
  step(putDMAMir_FK(0)) >>

-- end call to 'dma_create'


--
-- CALL TO 'dma_create':
--

  -- initialize DMA (BE -> FE):
  step(
    putDMA_CFG_BK(_DMA_BASEADDR_F) >>
    putDMAMir_BK(_DMA_BASEADDR_F + _DMAMIR) >>
    putDMACtrl_BK(_DMA_BASEADDR_F + _DMACR) >>
    putSrcAddr_BK(_DMA_BASEADDR_F + _SRCADDR) >>
    putDestAddr_BK(_DMA_BASEADDR_F + _DSTADDR) >>
    putDMALength_BK(_DMA_BASEADDR_F + _DMALENGTH) >>
    putDMAStatus_BK(_DMA_BASEADDR_F + _DMASTATUS) >>
    putDMA_ISR_BK(_DMA_BASEADDR_F + _DMAISR) >>
    putDMA_IER_BK(_DMA_BASEADDR_F + _DMAIER)
  ) >>

  -- the reset; see note above
  step(putDMAMir_FK(0)) >>
  step(putDMAMir_FK(_DMA_RESET)) >>
  step(putDMAMir_FK(0)) >>

-- end call to 'dma_create'


  step(
    putCurrTransferValid_FK(False) >>
    putQHead_FK(0) >>
    putQTail_FK(0)
  ) >>


  step(
    putExists_BK(False) >>
    putReady_BK(False) >>
    putQHead_BK(0) >>
    putQTail_BK(0)
  ) >>

--
-- CALL TO 'initialize_peip_interface':
--
-- ('for' loop has been unrolled into two separate sets of actions)
--

  step(
    putPEIP_CMD_HEADER_In1K(get_command_header_in 1) >>
    putPEIP_CMD_HEADER_Out1K(get_command_header_out 1) >>
    putPEIP_CMD_HEADER_Data_In1K(get_data_in_address 1) >>
    putPEIP_CMD_HEADER_Data_Out1K(get_data_out_address 1) >>

    putPEIP_CMD_HEADER_In1K(get_command_header_in 2) >>
    putPEIP_CMD_HEADER_Out2K(get_command_header_out 2 ) >>
    putPEIP_CMD_HEADER_Data_In1K(get_data_in_address 2) >>
    putPEIP_CMD_HEADER_Data_Out1K(get_data_out_address 2)
  ) >>


  step(
    putChanReqStatus1(_CHANNEL_NOT_USED) >>
    putActiveChannel1(_CHANNEL_NOT_USED) >>

    putChanReqStatus2(_CHANNEL_NOT_USED) >>
    putActiveChannel2(_CHANNEL_NOT_USED)
  ) >>

  return ()

-- end init --


--
-- process_request:
--
-- handle a service request to the back-end;
--
--

process_request :: Int -> Re ()
process_request n =

  step(
    putOpCode(_get_opcode n) >>= \c ->
    return c
  ) >>= \c' ->

  --
  -- cheap substitute for a 'switch' expression;
  --
  semifix (_OP_CHANNEL_RESERVE == c')
  (\k25 ->
    reserve_channel n
  ) >>

  semifix (_OP_DMA_REQ == c')
  (\k26 ->
    fe_dma_request n
  ) >>

  semifix (_OP_FE_SEG_DONE == c')
  (\k27 ->
    fe_segment_done n
  ) >>

  semifix (_OP_DATA_ADDR == c')
  (\k28 ->
    (fe_data_addr n)
  ) >>
  
  --
  -- the default case:
  --
  semifix (not ((_OP_CHANNEL_RESERVE == c') ||
                (_OP_DMA_REQ == c') ||
                (_OP_FE_SEG_DONE == c') ||
                (_OP_DATA_ADDR == c')))
  (\k29 ->
    return ()
  ) >>
  return ()



reserve_channel :: Int -> Re ()
reserve_channel n =
  step(
    return (_get_channel n)
  ) >>= \i' ->


  step(getChanReqStatus1K) >>= \t ->
  semifix (_CHANNEL_NOT_USED == t)
  (\k30 ->
    step(
      putChanReqStatus1(_CHANNEL_USED) >>
      putRCMsg(0) >>
      putRCMsg(form_channel_grant i')
    )
  ) >>


  semifix (_CHANNEL_USED == t)
  (\k31 ->

    step(
      putRCMsg(0) >>
      putRCMsg(form_channel_deny i')
    )

  ) >>

  semifix (_CHANNEL_NOT_USED == t)
  (\k32 ->
    step(
      putChanReqStatus2(_CHANNEL_USED) >>
      putRCMsg(0) >>
      putRCMsg(form_channel_grant i')
    )

  ) >>


  semifix (_CHANNEL_USED == t)
  (\k33 ->
    step(
      putRCMsg(0) >>
      putRCMsg(form_channel_deny i')
    )
  ) >>

  step(getRCMsgK) >>= \m ->
  (signal FSL_OUT  (Ack m)) >>
  return ()
  -- end function


fe_dma_request :: Int -> Re ()
fe_dma_request n =

  step(
    putFDRChannelId(n) >>
    putFDR_DMALength(0) >>
    putFDR_DMAOffset(0) >>
    putFDR_DMAAddress(0)
  ) >>

  step(
    getFDRChannelIdK >>= \i ->
    putFDRChannelIdK(_get_channel i)
  ) >>

  (signal FSL_IN BRead) >>= \m ->
  step(putFDRMsg1(m)) >>
  (signal FSL_IN BRead) >>= \m' ->
  step(putFDRMsg2(m')) >>

  step(
    getFDRMsg1K >>= \l ->
    putFDR_DMALengthK(_get_dma_length l) >>
    putFDR_DMAOffsetK(_get_dma_offset l) >>
    getFDRMsg2K >>= \l' ->
    putFDR_DMAAddressK(_get_dma_address l')
  ) >>

  -- form the new request to enqueue:

  step(
    getFDRChannelIdK >>= \c ->
    putChanId_FK(c) >>
    putTransType_FK(_NORMAL_TYPE) >>
    putReqCtrl_FK(_DMA_SINC ||| _DMA_DINC ||| _DMA_DSIZE_WORD) >>
    getFDRMsg1K(a) >>= \a ->
    putReqSrcAddr_FK(_get_dma_address a) >>
    getFDR_DMALengthK >>= \l' ->
    putReqLength_F(l') >>
    return c
  ) >>= \c' ->

  semifix (1 == c')
  (\k34 ->
    getPEIP_Data_In1K >>= \d ->
    getFDR_DMAOffsetK >>= \o ->
    putReqDestAddr_F(d + o)
  ) >>

  semifix (2 == c')
  (\k35 ->
    getPEIP_Data_In2K >>= \d ->
    getFDR_DMAOffsetK >>= \o ->
    putReqDestAddr_F(d + o)
  ) >>

  enqueue_F >>
  return ()
  -- end function


fe_segment_done :: Int -> Re ()
fe_segment_done n =
  (signal FSL_IN BRead) >>= \m1 ->
  step(putFSD_Msg1(m1)) >>
  (signal FSL_IN BRead) >>= \m2 ->
  step(putFSD_Msg2(m2)) >>
  (signal FSL_IN BRead) >>= \m3 ->
  step(putFSD_Msg2(m3)) >>
  (signal FSL_IN BRead) >>= \m4 ->
  step(putFSD_Msg2(m4)) >>
  (signal FSL_IN BRead) >>= \m5 ->
  step(putFSD_Msg2(m5)) >>

  step(putFSD_ChannelIdK(_get_channel n)) >>= \c ->

  semifix (1 == c)
  (\k36 ->
    step(
      putActiveChannel1K(_CHANNEL_USED) >>
      getPEIP_Data_In1K >>= \a ->
      putFSD_CMDHeaderPtrK(a)
    )
  ) >>

  semifix (2 == c)
  (\k37 ->
    putActiveChannel1K(_CHANNEL_USED) >>
    getPEIP_Data_In2K >>= \a ->
    putFSD_CMDHeaderPtr(a)
  ) >>

  step(
    getFSD_Msg3K >>= \m3 ->
    putFSD_OriginalMsgK(m3) >>
    putFSD_Msg3K(m3 &&& (bwnot _MSG_AVAIL_MASK))
  ) >>

  step(
    getFSD_CMDHeaderPtrK >>= \a' ->
    getFSD_Msg1K >>= \m1 ->
    (write PEIP (a' + 1) m1) >>
    getFSD_Msg2K >>= \m2 ->
    (write PEIP (a' + 2) m2) >>
    getFSD_Msg3K >>= \m3 ->
    (write PEIP (a' + 3) m3) >>
    getFSD_Msg4K >>= \m4 ->
    (write PEIP (a' + 4) m4) >>
    getFSD_Msg5K >>= \m5 ->
    (write PEIP (a' + 5) m4) >>
    return a'
  ) >>= \a'' ->

  step(
    getFSD_OriginalMsgK >>= \o -> 
    (write PEIP (a'' + _CMD_HEADER_WORD_WITH_FLAGS) o)
  ) >>

  (signal FSL_OUT (form_be_segment_done c)) >>

  return ()
  -- end function



fe_data_addr :: Int -> Re ()
fe_data_addr n =
  step(
    putFDA_ChannelIdK(_get_channel n) >>
    putFDA_DMALengthK(_get_dma_length n)
  ) >>

  (signal FSL_OUT BRead) >>= \m ->
  step(
    putFDA_Msg1K(m) >>
    putFDA_DestAddrK(_get_dma_address m) >>= \a ->

    getFDA_DMALengthK >>= \l ->
    putMaxTransferSize_B(l) >>
    putDestAddr_B(a) >>
    putReady_B(True)
  ) >>


  semifix (Exists_B && (DMALength_B > MaxTransferSize_B))
  (\k38 ->

    getFDA_DestAddrK >>= \a' ->
    putDestAddr_B(a') >>

    getMaxTransferSize_BK >>= \x ->
    putCurrTransferSize_B(x)

  ) >>

  semifix (Exists_B && (not (DMALength_B > MaxTransferSize_B)))
  (\k39 ->

    getFDA_DestAddrK >>= \a' ->
    putDestAddr_B(a') >>

    getCurrTransferSize_BK >>= \x ->
    putCurrTransferSize_B(x)

  ) >>

  return ()
  -- end function




 
--
-- a few (pure) helper functions translated more or less from the original code:
--

--
-- in peip_interface.h :
--

get_command_header_in :: Int -> Int
get_command_header_in n =
  if n > 9 then _PEIP_BASE_ADDRESS - 9999
  else
     _PEIP_BASE_ADDRESS + ((n &&& 255) <<< 12)


get_command_header_out :: Int -> Int
get_command_header_out n =
  if n > 9 then _PEIP_BASE_ADDRESS - 9999
  else
     _PEIP_BASE_ADDRESS + ((n &&& 255) <<< 12) + (8 * 16 * 16)

get_data_in_address :: Int -> Int
get_data_in_address n =
  if n > 9 then _PEIP_BASE_ADDRESS - 9999
  else
    _PEIP_BASE_ADDRESS + (10 * 16 * 16 * 16) + ((n &&& 255) * (2 * 16 * 16 * 16))


get_data_out_address :: Int -> Int
get_data_out_address n =
  if n > 9 then _PEIP_BASE_ADDRESS - 9999
  else
    _PEIP_BASE_ADDRESS + (11 * 16 * 16 * 16) + ((2 * 16 * 16 * 16) * (n &&& 255))

--
-- note to self: add the pertinent bit-wise logical operations
-- as builtins to the defunctionalizer
--
-- note also that using '|' for bitwise-or is going to upset the Haskell parser
--


--
-- some more simple macros:
--

_set_opcode :: Int -> Int -> Int
_set_opcode op x = (((op &&& _OP_MASK) <<< _OP_SHIFT) ||| x)

_set_channel :: Int -> Int -> Int
_set_channel ch x = (((ch &&& _CHAN_MASK) <<< _CHAN_SHIFT) ||| x)

_get_opcode :: Int -> Int
_get_opcode x = ((x >>> _OP_SHIFT) &&& _OP_MASK)

_get_channel :: Int -> Int
_get_channel x = ((x >>> _CHAN_SHIFT) &&& _CHAN_MASK)

form_channel_grant :: Int -> Int
form_channel_grant i = _set_channel i (_set_opcode _OP_CHANNEL_GRANT 0)

form_channel_deny :: Int -> Int
form_channel_deny i = _set_channel i (_set_opcode _OP_CHANNEL_DENY 0)

_get_dma_length :: Int -> Int
_get_dma_length x = ((x >>> _DMA_LENGTH_SHIFT) &&& _DMA_LENGTH_MASK)

_get_dma_offset :: Int -> Int
_get_dma_offset x = ((x >>> _DMA_OFFSET_SHIFT) &&& (_DMA_OFFSET_MASK))

_get_dma_address :: Int -> Int
_get_dma_address x = x

form_be_segment_done :: Int -> Int
form_be_segment_done n = _set_channel n (_set_opcode _OP_BE_SEG_DONE 0)
