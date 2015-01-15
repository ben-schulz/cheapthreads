--
-- this is ~/cheapthreads/CTC/CT-1.0/TestPrograms/backend.ct.hs
--
-- a CT implementation of Jason's IO module, i.e. the NRL back-end
--
-- or,
--
-- a remodeling.
--
-- put here 2010.03.08
--
-- Schulz
--

monad K = StateT(Bool) Invalid +
          StateT(Int) Arg +

          -- persistent back-end status states:

          -- channels between FE and BE:
          MemT 2 (Int) ChanReqStatus +          -- flag channels as active
          MemT 2 (Int) ActiveChannels +         -- active messages from FE

          --
          -- simulated DMA devices, each of which consists of the following
          -- integer registers:
          --
          --  + mir
          --  + control
          --  + src_addr
          --  + length
          --  + status
          --  + isr
          --  + ier

          -- DMA device (FE -> BE)
          StateT(Int) DMA_mir_F +
          StateT(Int) DMA_control_F +
          StateT(Int) DMA_src_addr_F +
          StateT(Int) DMA_length_F +
          StateT(Int) DMA_status_F +
          StateT(Int) DMA_isr_F +
          StateT(Int) DMA_ier_F +

          -- DMA device (BE -> FE)
          StateT(Int) DMA_mir_B +
          StateT(Int) DMA_control_B +
          StateT(Int) DMA_src_addr_B +
          StateT(Int) DMA_length_B +
          StateT(Int) DMA_status_B +
          StateT(Int) DMA_isr_B +
          StateT(Int) DMA_ier_B +

          --
          -- components for setting up DMA requests:
          --

          -- current DMA transfer details:
          StateT(Bool) CurrDMATransferValid_F +  -- validate DMA req (FE -> BE)
          StateT(Int) DMA_Req_channel_id_F +     -- channel being used
          StateT(Int) DMA_Req_type_F +           -- type of transfer

          -- DMA request parameters:
          StateT(Int) DMA_Req_control_F +
          StateT(Int) DMA_Req_src_addr_F +
          StateT(Int) DMA_Req_dst_addr_F +
          StateT(Int) DMA_Req_length_F +

          -- a slot for forming new DMA requests:
          StateT(Int) New_DMA_Req_channel_id +
          StateT(Int) New_DMA_Req_type +
          StateT(Int) New_DMA_Req_control +
          StateT(Int) New_DMA_Req_src_addr +
          StateT(Int) New_DMA_Req_dst_addr +
          StateT(Int) New_DMA_Req_length +

          -- queue for holding outstanding DMA requests (FE -> BE):
          StateT(Int) QHead_F +
          StateT(Int) QTail_F +

          StateT(Bool) Q_Empty_F +

          -- until aggregate types are fully up and running,
          -- we use parallel, base-type queues to hold the components
          -- of the outsanding DMA requests:
          MemT 128 (Int) Q_channel_id_F +
          MemT 128 (Int) Q_type_F +
          MemT 128 (Int) Q_control_F +
          MemT 128 (Int) Q_src_addr_F +
          MemT 128 (Int) Q_dst_addr_F +
          MemT 128 (Int) Q_length_F +

          -- queue for holding outstanding DMA requests (BE -> FE):
          StateT(Int) QHead_B +
          StateT(Int) QTail_B +

          StateT(Bool) Q_Empty_B +

          -- until aggregate types are fully up and running,
          -- we use parallel, base-type queues to hold the components
          -- of the outsanding DMA requests:
          MemT 128 (Int) Q_channel_id_B +
          MemT 128 (Int) Q_type_B +
          MemT 128 (Int) Q_control_B +
          MemT 128 (Int) Q_src_addr_B +
          MemT 128 (Int) Q_dst_addr_B +
          MemT 128 (Int) Q_length_B +

          StateT(Bool) CurrDMATransferValid_B + -- validate DMA req (BE -> FE)

          -- the PEIP interface:
          MemT 5 (Int) PEIP_Header +
          MemT 2 (Int) Cmd_Header_In_Addr +
          MemT 2 (Int) Cmd_Header_Out_Addr +
          MemT 2 (Int) Data_Header_In_Addr +
          MemT 2 (Int) Data_Header_Out_Addr +


          StateT(()) Nothing  -- this is just a place-holder while I code

monad Re = ReactT Q K

signal Q = (IsValid, Valid Bool)       -- query the validity of current input
         | (FSLRead, FSLRsp Int)       -- read off the FSL
         | (DMA_Free, DMA_Avail Bool)  -- check whether the DMA device is idle
         | (DMA_Done, DMA_Done_Ack)    -- signal current DMA transfer done

         -- check for a message from the PEIP;
         -- req argument is the channel number
         | (Msg_Avail1, Msg_Avail_Rsp1 Bool)
         | (Msg_Avail2, Msg_Avail_Rsp2 Bool)


         -- signals for interfacing with the PEIP;
         -- (one set for each channel)

         -- channel 1:
         | (Rd_Cmd_Header_In1, Cmd_Header_In1 Bool)
         | (Rd_Cmd_Header_Out1, Cmd_Header_Out1 Bool)
         | (Rd_Data_Header_In1, Data_Header_In1 Bool)
         | (Rd_Data_Header_Out1, Data_Header_Out1 Bool)

         -- channel 2:
         | (Rd_Cmd_Header_In2, Cmd_Header_In2 Bool)
         | (Rd_Cmd_Header_Out2, Cmd_Header_Out2 Bool)
         | (Rd_Data_Header_In2, Data_Header_In2 Bool)
         | (Rd_Data_Header_Out2, Data_Header_Out2 Bool)


--
-- MAIN FUNCTION --
--               --

main :: Re ()
main =


  -- MAIN LOOP
  -- run indefinitely
  ((fix
    (\k -> \nothing ->

      -- check for new data:
      signal(IsValid) >>= \valid -> 

      if (valid)

      -- if nothing new, go around again:
      then
        background >>
        k ()


      else
        -- otherwise, grab it and process:
        signal(FSLRead) >>= \rsp ->
        step_Re(put Arg rsp) >>

        processreq >>
        background >>

        k ()

      -- end 'else'
   )
  ) ()) >>  -- end main loop

  return ()


--
-- process a request arriving over the FSL:
--
processreq :: Re ()
processreq =

  -- grab the opcode out of the message and decode the request:
  step_Re(get Arg >>= \arg -> opcode_of arg) >>= \opcode -> 

  -- opcode == _OP_CHANNEL_RESERVE
  if (opcode == 0)
  then
    reserve_channel

  -- opcode == _OP_DMA_REQ
  else if (opcode == 1)
  then
    fe_dma_request

  --  opcode == _OP_FE_SEG_DONE
  else if (opcode == 2)
  then
    fe_segment_done

  -- opcode == _OP_DATA_ADDR
  else if (opcode == 3)
  then
    fe_data_addr

  else
    return ()

  

--
-- do background processing:
--
background :: Re ()
background =

  (
    -- poll active channels for PEIP replies:
    (fix
      (\k -> \n ->

        if (n < 2)
        then

          -- check to see if the channel has an active message:
          step_Re(get ActiveChannels[n]) >>= \b ->

          -- if channel used, then it has an active message;
          -- check for a reply
          if(b == 1)
          then
            (handle_reply n) >>                    -- handle the reply
            step_Re(put ActiveChannels[n] 0) >>    -- clear the activity
            k (n + 1)

          else
            k (n + 1)  -- if no message, go around again

        else
          return ()
      )

    ) 0  -- end fix

  ) >>


  -- poll all channels for PEIP responses:
  (
    (fix
      (\k -> \n ->

        if (n < 2)
        then

          -- query for the presence of a response to channel 'n':
          (is_response n) >>= \b ->

          if b
          then
            (handle_response n) >>
            k (n + 1)
          else
            k (n + 1)

        else
          return ()
      )

    ) 0  -- end fix

  ) >>

  -- monitor and advance DMA processing:
  advance_dma_transfers >>

  return ()


--
-- check for a response on the given channel:
--
is_response :: Int -> Re Bool
is_response n =

  if (n == 1)
  then
    signal Msg_Avail1 >>= \b -> return b
  else
    signal Msg_Avail2 >>= \b -> return b
  

--
-- handle a reply arriving on the given channel:
--
handle_reply :: Int -> Re ()
handle_reply ch =

  -- get the command header from the PEIP:
  (

    if (ch == 1)
    then
      signal Rd_Cmd_Header_In1 >>= \cmd_hd -> return cmd_hd
    else
      signal Rd_Cmd_Header_In2 >>= \cmd_head -> return cmd_hd

  ) >>= \cmd_hd ->


  -- form a DMA request for the received header:
  step_Re(

    put New_DMA_Req_channel_id ch >>       -- set channel id to argument
    put New_DMA_Req_type 0 >>              -- set type to NORMAL


    -- "(DMA_SINC | DMA_DINC | DMA_DSIZE_WORD)"
    put New_DMA_Req_control (12 * (16^7) + 4) >>    -- another magic constant

    put New_DMA_Req_src_addr (15*16 + 15) >>        -- somewhere arbitrary

    put New_DMA_Req_dst_addr (9*16^2 + 9*16 + 9) >> -- address filled in later

    put New_DMA_Req_length 20 >>  -- i.e. request is 20 bytes long

    return ()

  ) >>

  enqueue_new_req_F >>  -- enqueue the new request


  -- if data is included with the request, include that as well:

  return ()



--
-- handle a PEIP response arriving over the channel:
--
handle_response :: Int -> Re ()
handle_response ch =

  -- get the command header from the PEIP:
  (

    if (ch == 1)
    then
      signal Rd_Cmd_Header_Out1 >>= \cmd_hd -> return cmd_hd
    else
      signal Rd_Cmd_Header_Out2 >>= \cmd_hd -> return cmd_hd

  ) >>= \cmd_hd ->


  -- form a DMA request for the received header:
  step_Re(

    put New_DMA_Req_channel_id ch >>       -- set channel id to argument
    put New_DMA_Req_type 1 >>              -- set type to FINAL


    -- "(DMA_SINC | DMA_DINC | DMA_DSIZE_WORD)"
    put New_DMA_Req_control (12 * (16^7) + 4) >>    -- another magic constant

    put New_DMA_Req_src_addr (15*16 + 15) >>        -- somewhere arbitrary

    put New_DMA_Req_dst_addr (9*16^2 + 9*16 + 9) >> -- address filled in later

    put New_DMA_Req_length 20 >>  -- i.e. request is 20 bytes long

    return ()

  ) >>

  enqueue_new_req_B >>  -- enqueue the new request


  -- if data is included with the request, include that as well:
  if (cmd_hd)
  then
    step_Re(

      -- this is right now just a stub, duplicating the above block:

      put New_DMA_Req_channel_id ch >>       -- set channel id to argument
      put New_DMA_Req_type 0 >>              -- set type to NORMAL


      -- "(DMA_SINC | DMA_DINC | DMA_DSIZE_WORD)"
      put New_DMA_Req_control (12 * (16^7) + 4) >>    -- another magic constant

      put New_DMA_Req_src_addr (15*16 + 15) >>        -- somewhere arbitrary

      put New_DMA_Req_dst_addr (9*16^2 + 9*16 + 9) >> -- address filled in later

      put New_DMA_Req_length 20 >>  -- i.e. request is 20 bytes long

      return ()

    ) >>

    enqueue_new_req_B  -- enqueue the request

  -- otherwise, just submit the command header
  else
    step_Re(
      put New_DMA_Req_type 1    -- set type to final
    ) >>

    enqueue_new_req_B



reserve_channel :: Re ()
reserve_channel = return ()


fe_dma_request :: Re ()
fe_dma_request = return ()


fe_segment_done :: Re ()
fe_segment_done = return ()


fe_data_addr :: Re ()
fe_data_addr = return ()


advance_dma_transfers :: Re ()
advance_dma_transfers =

  --
  -- advance the FE to BE queue:
  --
  signal DMA_Free >>= \avail ->

  if (avail)
  then
    step_Re(get CurrDMATransferValid_F) >>= \valid ->

    -- if the DMA is done, send an acknowledgment:
    if (valid)
    then
      signal DMA_Done >> return ()

    -- if not valid and not empty, send the next request:
    else

      step_Re(get Q_Empty_F) >>= \empty ->


      if (empty)
      then
--        dequeue_dma_req_F >>
        step_Re(put CurrDMATransferValid_F True) >>
--        perform_dma_request_fe_to_be >>
        return ()

      -- if the queue is empty, do nothing:
      else
        return ()

  -- if the DMA is not free, don't do anything:
  else
    return ()


--
-- advance the BE to FE queue:
--




--
-- dequeue from the DMA req queue:
--
dequeue_dma_req_F :: Re ()
dequeue_dma_req_F = return ()

perform_dma_request_fe_to_be :: Re ()
perform_dma_request_fe_to_be = return ()

--
-- enqueue the DMA request data in the 'New_DMA_Req' components
--

--
-- (FE to BE)
--
enqueue_new_req_F :: Re ()
enqueue_new_req_F =

  step_Re(

    --
    -- get the new DMA req data:
    --
    get New_DMA_Req_channel_id >>= \ch ->
    get New_DMA_Req_type >>= \ty ->
    get New_DMA_Req_control >>= \ctrl ->
    get New_DMA_Req_src_addr >>= \src ->
    get New_DMA_Req_dst_addr >>= \dst ->
    get New_DMA_Req_length >>= \len ->

    --
    -- put it into the queue:
    --
    get QTail_F >>= \t ->

    put Q_channel_id_F[t] ch >>
    put Q_type_F[t] ty >>
    put Q_control_F[t] ctrl >>
    put Q_src_addr_F[t] src >>
    put Q_dst_addr_F[t] dst >>
    put Q_length_F[t] len >>

    -- lengthen the queue, wrapping around the indices:
    put QTail_F (if t < 128 then t + 1 else 0) >>

    return ()
  )

--
-- BE to FE
--
enqueue_new_req_B :: Re ()
enqueue_new_req_B =

  step_Re(

    --
    -- get the new DMA req data:
    --
    get New_DMA_Req_channel_id >>= \ch ->
    get New_DMA_Req_type >>= \ty ->
    get New_DMA_Req_control >>= \ctrl ->
    get New_DMA_Req_src_addr >>= \src ->
    get New_DMA_Req_dst_addr >>= \dst ->
    get New_DMA_Req_length >>= \len ->

    --
    -- put it into the queue:
    --
    get QTail_B >>= \t ->

    put Q_channel_id_B[t] ch >>
    put Q_type_B[t] ty >>
    put Q_control_B[t] ctrl >>
    put Q_src_addr_B[t] src >>
    put Q_dst_addr_B[t] dst >>
    put Q_length_B[t] len >>

    -- lengthen the queue, wrapping around the indices:
    put QTail_B (if t < 128 then t + 1 else 0) >>

    return ()
  )




--
-- UTILITY AND HELPER FUNCTIONS:
--

--
-- opcode sits at the first eight bits:
--
opcode_of :: Int -> K Int
opcode_of n = return (slice n 0 8)


--
-- CONSTANTS:
--

_CHANNEL_USED :: Int
_CHANNEL_USED = 1

_OP_SHIFT :: Int
_OP_SHIFT = 24

_INT_WIDTH :: Int
_INT_WIDTH = 32

--
-- the request opcodes:
--
_OP_CHANNEL_RESERVE :: Int
_OP_CHANNEL_RESERVE = 0

_OP_DMA_REQ :: Int
_OP_DMA_REQ = 1

_OP_FE_SEG_DONE :: Int
_OP_FE_SEG_DONE = 2

_OP_DATA_ADDR :: Int
_OP_DATA_ADDR = 3
