/*


   BACK END (.h)

   This file contains many of the useful functions for the back-end

*/

#include <httype.h>
#include <htconst.h>
#include "comm_lib.h"
#include "queue.h"
#include "dma.h"
#include "peip_interface.h"
#include <xparameters.h>

// Define base address of DMA device
#define DMA_BASEADDR_FE_TO_BE		(XPAR_OPB_CENTRAL_DMA_0_BASEADDR)
#define DMA_BASEADDR_BE_TO_FE		(XPAR_OPB_CENTRAL_DMA_1_BASEADDR)

// Channel status definitions
#define CHANNEL_USED        1
#define CHANNEL_NOT_USED    0

// Structure used for holding all BE status info
typedef struct
{
    // Array used to hold request/open data for channels
    int channel_request_status[NUM_CHANNELS];

    // Array used to hold data for "active" channels (active messages in place from the front-end)
    int active_channels[NUM_CHANNELS];

    // DMA device (FE->BE)
    dma_t dma_fe_to_be;

    // DMA device (BE->FE)
    dma_t dma_be_to_fe;

    // PEIP interface
    peip_interface_t peip_interface;

    // Queue to hold outstanding DMA transfer requests (FE->BE)
    queue_t         dma_queue_fe_to_be;                  // Queue of DMA requests
    dma_request_t   current_dma_transfer_fe_to_be;       // Variable to hold current transfer details
    Hbool           current_dma_transfer_fe_to_be_valid; // Flag to signify validity of current transfer

    // Queue to hold outstanding DMA transfer requests (BE->FE)
    queue_t         dma_queue_be_to_fe;                  // Queue of DMA requests
    dma_request_t   current_dma_transfer_be_to_fe;       // Variable to hold current transfer details
    Hbool           current_dma_transfer_be_to_fe_exists; // Flag to signify that a current transfer exists (but may not yet be ready)
    Hbool           be_to_fe_transfer_ready;             // Flag to signify that all BE->FE parameters exist, and are ready to begin a transfer
    Huint           be_to_fe_max_transfer_size;          // Max. number of bytes that can be transferred at a time (BE->FE)
    Huint           be_to_fe_current_transfer_size;      // Current number of bytes that will be transferred at a time (BE->FE)
    Huint           be_to_fe_destination_address;        // Max. number of bytes that can be transferred at a time (BE->FE)

} back_end_status;

// *********************************************************************************************
// Function : initialize_back_end_status
// Purpose  : Initializes the back_end_status structure
// *********************************************************************************************
void initialize_back_end_status(back_end_status * be)
{
    int counter = 0;
    dma_config_t    dma_config_fe_to_be;
    dma_config_t    dma_config_be_to_fe;

    // Initialize DMA device (FE->BE)
    dma_config_fe_to_be.base = DMA_BASEADDR_FE_TO_BE;
    dma_create(&be->dma_fe_to_be, &dma_config_fe_to_be);

    // Initialize DMA device (BE->FE)
    dma_config_be_to_fe.base = DMA_BASEADDR_BE_TO_FE;
    dma_create(&be->dma_be_to_fe, &dma_config_be_to_fe);

    // Initialize DMA queue (FE->BE)
    be->current_dma_transfer_fe_to_be_valid = Hfalse;
    initialize_queue(&be->dma_queue_fe_to_be); 

    // Initialize DMA queue (BE->FE)
    be->current_dma_transfer_be_to_fe_exists = Hfalse;
    be->be_to_fe_transfer_ready              = Hfalse;
    initialize_queue(&be->dma_queue_be_to_fe);

    // Initialize PEIP interface
    initialize_peip_interface(&be->peip_interface);

    // Initialize all channel data
    for (counter = 0; counter < NUM_CHANNELS; counter++)
    {
        be->channel_request_status[counter] = CHANNEL_NOT_USED;
        be->active_channels[counter]        = CHANNEL_NOT_USED;
    }

    return;
}

// *********************************************************************************************
// Function : is_reply
// Purpose  : Checks to see if a a reply exists for a given channel
// *********************************************************************************************
Hbool is_reply(int channel, back_end_status * be)
{
    volatile Huint * command_pointer = be->peip_interface.command_header_in_address[channel];
    Huint flags = 0;

    // Checks a given channel's command header to see if a reply is available by 
    // Grab the command header in for the channel
    flags = *(command_pointer + CMD_HEADER_WORD_WITH_FLAGS);

    // Extract the MSG_READ flag
    flags = flags & MSG_READ_MASK;

    // If MSG_READ is set, then return TRUE, else FALSE
    if (flags)
        return Htrue;
    else
        return Hfalse;
}

// *********************************************************************************************
// Function : is_response
// Purpose  : Checks to see if a a response exists for a given channel
// *********************************************************************************************
Hbool is_response(int channel, back_end_status * be)
{
    volatile Huint * command_pointer = be->peip_interface.command_header_out_address[channel];
    Huint flags = 0;

    // Checks a given channel's response header to see if a response is available by
    // Grab the command header out for the channel
    flags = *(command_pointer + CMD_HEADER_WORD_WITH_FLAGS);

    // Extract the MSG_AVAIL flag
    flags = flags & MSG_AVAIL_MASK;

    // If MSG_AVAIL is set, then return TRUE, else FALSE
    if (flags)
        return Htrue;
    else
        return Hfalse;
}

// *********************************************************************************************
// Function : handle_reply
// Purpose  : Handles a reply (pulls reply and sends it to front-end).  Assumes a reply is ready
// *********************************************************************************************
void handle_reply(int channel, back_end_status * be)
{
    // Extracts a reply from a given channel and sets up the proper DMA transfers to send
    // the reply to the front-end
    // FIXME - which data should be DMA'ed first command header or data (and in what order)
    //
    // Lookup "length" of reply (and if data is included)
    // Create a DMA request (normal type) for the command header
    // Create a DMA request (normal type) for all of the data (if needed)
    // Put DMA requests in the BE->FE queue
    //

    Huint flags;
    volatile Huint * flag_pointer;

    // Initialize flag pointer
    flag_pointer = (be->peip_interface.command_header_in_address[channel] + CMD_HEADER_WORD_WITH_FLAGS);
	
    // Read in command header word with flags
	flags = *flag_pointer;

    // Setup a DMA request for the command header (always done)
    dma_request_t   cmd_request;
    cmd_request.channel_id  = channel;
    cmd_request.type        = NORMAL_TYPE;
    cmd_request.control     = (DMA_SINC | DMA_DINC | DMA_DSIZE_WORD); // Increment both srcAddr and dstAddr, with 32-bit transfers
    cmd_request.srcAddr     = (Huint)be->peip_interface.command_header_in_address[channel];
    cmd_request.dstAddr     = 0x999;   // This will be filled in by a DATA_OUT request later
    cmd_request.length      = 5*sizeof(Huint);  // 5, 32-bit words = 5 * 4 bytes = 20 bytes

    // Add this request to the BE->FE queue
    enqueue(&be->dma_queue_be_to_fe, cmd_request);

    // Check to see if data is included with this
    if (flags & DATA_INCL_MASK)
    {
        // Yes, data is included
        // Now setup a DMA request for the data
	    dma_request_t   data_request;
	    data_request.channel_id  = channel;
	    data_request.type        = NORMAL_TYPE;
	    data_request.control     = (DMA_SINC | DMA_DINC | DMA_DSIZE_WORD); // Increment both srcAddr and dstAddr, with 32-bit transfers
	    data_request.srcAddr     = (Huint)be->peip_interface.data_in_address[channel];
	    data_request.dstAddr     = 0x999;   // This will be filled in by a DATA_OUT request later
	    data_request.length      = *(be->peip_interface.command_header_in_address[channel] + CMD_HEADER_WORD_WITH_LENGTH);
	
	    // Add this request to the BE->FE queue
	    enqueue(&be->dma_queue_be_to_fe, data_request);
    }
	
    return;
}

// *********************************************************************************************
// Function : handle_response
// Purpose  : Handles a response (pulls response and sends it to front-end). Assumes a response is ready
// *********************************************************************************************
void handle_response(int channel, back_end_status * be)
{
    // Extracts a response from a given channel and sets up the proper DMA transfers to send
    // the response to the front-end
    // FIXME - which data should be DMA'ed first command header or data (and in what order)
    //
    // Lookup "length" of response (and if data is included)
    // Create a DMA request (all normal, last one is final)
    // If no data:
    //   Then command header DMA request is final
    // Else:
    //   Then command header is (normal) and data section is final
    // Put DMA requests in the BE->FE queue
    //

    Huint flags;
    volatile Huint * flag_pointer;

    // Initialize flag pointer
    flag_pointer = (be->peip_interface.command_header_out_address[channel] + CMD_HEADER_WORD_WITH_FLAGS);
	
    // Read in command header word with flags
	flags = *flag_pointer;

    // Setup a DMA request for the command header (always done)
    dma_request_t   cmd_request;
    cmd_request.channel_id  = channel;
    cmd_request.type        = FINAL_TYPE;
    cmd_request.control     = (DMA_SINC | DMA_DINC | DMA_DSIZE_WORD); // Increment both srcAddr and dstAddr, with 32-bit transfers
    cmd_request.srcAddr     = (Huint)be->peip_interface.command_header_out_address[channel];
    cmd_request.dstAddr     = 0x999;   // This will be filled in by a DATA_OUT request later
    cmd_request.length      = 5*sizeof(Huint);  // 5, 32-bit words = 5 * 4 bytes = 20 bytes


    // Check to see if data is included with this
    if (flags & DATA_INCL_MASK)
    {
        // Yes, data is included, this means that the command header request should be set to NORMAL not FINAL
        cmd_request.type        = NORMAL_TYPE;
        
        // Now setup a DMA request for the data
	    dma_request_t   data_request;
	    data_request.channel_id  = channel;
	    data_request.type        = FINAL_TYPE;
	    data_request.control     = (DMA_SINC | DMA_DINC | DMA_DSIZE_WORD); // Increment both srcAddr and dstAddr, with 32-bit transfers
	    data_request.srcAddr     = (Huint)be->peip_interface.data_out_address[channel];
	    data_request.dstAddr     = 0x999;   // This will be filled in by a DATA_OUT request later
	    data_request.length      = *(be->peip_interface.command_header_out_address[channel] + CMD_HEADER_WORD_WITH_LENGTH);
	
        // Add this request to the BE->FE queue
        enqueue(&be->dma_queue_be_to_fe, cmd_request);
	
        // Add this request to the BE->FE queue
	    enqueue(&be->dma_queue_be_to_fe, data_request);
    }
    else
    {
        // Just submit the command header request as final
        cmd_request.type        = FINAL_TYPE;
        enqueue(&be->dma_queue_be_to_fe, cmd_request);
    }


    return;
}

// *********************************************************************************************
// Function : perform_dma_request_fe_to_be
// Purpose  : Begins a DMA transaction of the request located in the current_dma_transfer_fe_to_be variable
// *********************************************************************************************
void perform_dma_request_fe_to_be(back_end_status * be)
{

    // Unpack the DMA request structure, and start the DMA process
    perform_dma_transfer(
        &be->dma_fe_to_be,
        be->current_dma_transfer_fe_to_be.control,
        be->current_dma_transfer_fe_to_be.srcAddr,
        be->current_dma_transfer_fe_to_be.dstAddr,
        be->current_dma_transfer_fe_to_be.length
        );
}

// *********************************************************************************************
// Function : perform_dma_request_be_to_fe
// Purpose  : Begins a DMA transaction of the request located in the current_dma_transfer_be_to_fe variable
// *********************************************************************************************
void perform_dma_request_be_to_fe(back_end_status * be)
{

    // Unpack the DMA request structure, and start the DMA process
    perform_dma_transfer(
        &be->dma_be_to_fe,
        be->current_dma_transfer_be_to_fe.control,
        be->current_dma_transfer_be_to_fe.srcAddr,
        be->current_dma_transfer_be_to_fe.dstAddr,
        be->be_to_fe_current_transfer_size              // This is the # of bytes currently being transferred   (Use this)
//        be->current_dma_transfer_be_to_fe.length      // This is the current # of bytes left in this transfer (Don't use)
        );
}

// *********************************************************************************************
// Function : advance_fe_to_be_queue
// Purpose  : Performs all background DMA operations for the FE->BE DMA device and queue
// *********************************************************************************************
void advance_fe_to_be_queue(back_end_status * be)
{
    // Check to see if the DMA device (FE->BE) is idle
    if (is_dma_available(&be->dma_fe_to_be))
    {
        // If idle, first check the current transfer (if there is one)
        if (be->current_dma_transfer_fe_to_be_valid)
        {
            // DMA transfer encountered an error, then...
            if (is_dma_error(&be->dma_fe_to_be))
            {
                // Should it be retried or dropped???
                // Re-start the DMA transfer process
                xil_printf("[[ BE ]] !!!! DMA ERROR (FE->BE) !!!!!\r\n");
                perform_dma_request_fe_to_be(be); 

            }
            // DMA transfer is done, send proper ACK (look at DMA type)
            else if (is_dma_done(&be->dma_fe_to_be))
            {
                // Send the proper acknowledgement to the FE (dma_fdone)
                message_t dma_fdone_msg;
                dma_fdone_msg = form_dma_fdone(be->current_dma_transfer_fe_to_be.channel_id);
                send_messages(&dma_fdone_msg,1);
     
      
                // Invalidate the current transfer, as it is now complete
                be->current_dma_transfer_fe_to_be_valid = Hfalse;
            }
        }

        // Next check if there are any requests in the queue (and the current transfer is invalid), and if so, dequeue the first element
        // and set it as the current transfer element, and start a new DMA transfer of this element
        if ((!be->current_dma_transfer_fe_to_be_valid) & (not_empty(&be->dma_queue_fe_to_be)))
        {
            // Setup current dma transfer 
            be->current_dma_transfer_fe_to_be = dequeue(&be->dma_queue_fe_to_be);
            be->current_dma_transfer_fe_to_be_valid = Htrue;

            // Start the DMA transfer process
            perform_dma_request_fe_to_be(be); 
        }
        
    }
    // If not idle, then no DMA processing can be accomplished
}

// *********************************************************************************************
// Function : advance_be_to_fe_queue
// Purpose  : Performs all background DMA operations for the BE->FE DMA device and queue
// *********************************************************************************************
void advance_be_to_fe_queue(back_end_status * be)
{
    Huint flags;
    volatile Huint * flag_pointer;

    // Check to see if the DMA device (BE->FE) is idle
    if (is_dma_available(&be->dma_fe_to_be))
    {
        // If idle, first check the current transfer (if there is one)
        if ((be->current_dma_transfer_be_to_fe_exists) & (be->be_to_fe_transfer_ready))
        {
            // DMA transfer encountered an error, then...
            if (is_dma_error(&be->dma_be_to_fe))
            {
                // Should it be retried or dropped???
                // Re-start the DMA transfer process
                xil_printf("[[ BE ]] !!!! DMA ERROR (BE->FE) !!!!!\r\n");
                perform_dma_request_be_to_fe(be); 

            }
            // DMA transfer is done, send proper ACK (look at DMA type)
            else if (is_dma_done(&be->dma_be_to_fe))
            {
                // Send the proper acknowledgement to the FE (dma_bdone)
                message_t dma_bdone_msg;
                dma_bdone_msg = form_dma_bdone(be->current_dma_transfer_be_to_fe.channel_id, be->be_to_fe_current_transfer_size);
                send_messages(&dma_bdone_msg,1);
     
                // This is a BE->FE transfer, which can only be done in "chunks".
                // This means that more "chunks" for this transfer may still remain.
                // Check here to see if more data needs to be transferred, if so, then...

                // Adjust DMA request length based on current completed transaction
                be->current_dma_transfer_be_to_fe.length =- be->be_to_fe_current_transfer_size;

                // Check to see if more data remains to be transferred for this DMA request
                if (be->current_dma_transfer_be_to_fe.length > 0)
                {
                    // More data needs to be transferred so leave this request as valid, but make it "not ready"
                    be->be_to_fe_transfer_ready             = Hfalse;

                    
                    // Re-request a data/addr from the FE (using a DATA_OUT msg.)
                    message_t data_out_msg;
                    data_out_msg = form_data_out(be->current_dma_transfer_be_to_fe.channel_id);
                    send_messages(&data_out_msg,1);

                }
                else
                {
                    // No more data is to be transferred, now invalidate the current transfer so another can take it's place
                    be->current_dma_transfer_be_to_fe_exists = Hfalse;
                    
                    // Check DMA type to see if this transfer needs to be finalized
	                // Check the type of the DMA transfer (normal or final)
	                // If final then set MSG_READ to '1' on peip interface
	                // If normal, then do nothing extra
	                if (be->current_dma_transfer_be_to_fe.type == FINAL_TYPE)
	                {
	                    // Setup flag pointer
	                    flag_pointer = (be->peip_interface.command_header_out_address[be->current_dma_transfer_be_to_fe.channel_id] + CMD_HEADER_WORD_WITH_FLAGS);
	
	                    // Read in command header word with flags
	                    flags = *flag_pointer;
	
	                    // Set MSG_READ flag to '1'
	                    flags = flags | MSG_READ_MASK;
	
	                    // Write the flag back out to the peip interface
	                    *flag_pointer = flags;
	                }
                }
            }
        }

        // Next check if there are any requests in the queue (and the current transfer is invalid), and if so, dequeue the first element
        // and set it as the current transfer element, and setup the DMA (as much as possible)
        if ((!be->current_dma_transfer_be_to_fe_exists) & (not_empty(&be->dma_queue_be_to_fe)))
        {
            // Setup current dma transfer 
            be->current_dma_transfer_be_to_fe = dequeue(&be->dma_queue_be_to_fe);
            be->current_dma_transfer_be_to_fe_exists = Htrue;

            // Request destination address and data length from the FE
            // When this message comes in, the ready flag will be set, and the DMA
            // transfer will be started
            message_t data_out_msg;
            data_out_msg = form_data_out(be->current_dma_transfer_be_to_fe.channel_id);
            send_messages(&data_out_msg,1);
        }
        
    }
    // If not idle, then no DMA processing can be accomplished 
}

// *********************************************************************************************
// Function : advance_dma_transfers
// Purpose  : Performs all background DMA operations (advancing the queue)
// *********************************************************************************************
void advance_dma_transfers(back_end_status * be)
{
    // Handle FE->BE transfers
    advance_fe_to_be_queue(be);

    // Handle BE->FE transfers
    advance_be_to_fe_queue(be);
    return;
}

// *********************************************************************************************
// Function : background_processing
// Purpose  : Performs all "background" processing when back-end does not have active requests
// *********************************************************************************************
void background_processing(back_end_status * be)
{
    int i = 0;

    // *******************************************
    // Poll active channels for PEIP "replies"
    // *******************************************
    for (i = 0; i < NUM_CHANNELS ; i++)
    {
        // Check to see if the channel has an active message
        if (be->active_channels[i] == CHANNEL_USED)
        {
            // Check to see if there is a reply
            //if (is_reply(i, be))
            if (Htrue)  // FIXME: PEIP emulation
            {
                // Process the reply
                handle_reply(i, be);

                // Clear activity
                be->active_channels[i] = CHANNEL_NOT_USED;
            }
        }
    }

    // *******************************************
    // Poll all channels for PEIP "responses"
    // *******************************************
    for (i = 0; i < NUM_CHANNELS ; i++)
    {
        // Check for PEIP response
        if (is_response(i, be))
        {
            // Process the response
            handle_response(i, be);
        }

    }

    // *******************************************
    // Monitor and advance DMA processing
    // *******************************************
    advance_dma_transfers(be);

    return;
}

// ***********************************************************
// Function : _reserve_channel
// Purpose  : Handles the reserve channel command (0 additional messages)
// Expected Message(s):
//  0) (OPCODE, channel_id)
// ***********************************************************
void _reserve_channel(message_t argument, back_end_status * be)
{
    message_t message   = 0;    // Variable to hold the message
    int channel_id      = 0;    // Variable to hold channel ID
    int num_messages    = 1;    // Variable to hold the number of messages to send

    // Extract channel ID
    channel_id = get_channel(argument);

    // Check to see if the channel is free (not already in use)
    if (be->channel_request_status[channel_id] == CHANNEL_NOT_USED)
    {
        // It is free, so it can be reserved
        be->channel_request_status[channel_id] = CHANNEL_USED;

        // Send a successful reservation message (GRANT)
        message = 0;
        message = form_channel_grant(channel_id);
    }
    else
    {
        // Send an unsuccessful reservation message (DENY)
        message = 0;
        message = form_channel_deny(channel_id);
    }

    // Send the message to the front-end
    num_messages = 1;
    send_messages(&message,num_messages);
}

// ***********************************************************
// Function : _fe_dma_request
// Purpose  : Handles the front-end DMA request message (2 additional messages)
// Expected Message(s):
//  0) (OPCODE, channel_id)
//  1) (dma_offset, dma_length)
//  2) (dma_address)
// ***********************************************************
void _fe_dma_request(message_t argument, back_end_status * be)
{
    // Message parameters
    int channel_id = 0;
    int num_messages = 2;
    message_t additional_messages[2];

    // DMA parameters
    int dma_length = 0;
    int dma_offset = 0;
    int dma_address = 0;

    // Extract channel ID
    channel_id = get_channel(argument);

    // Extract the additional DMA request messages
    num_messages = 2;
    get_messages(additional_messages, num_messages);

    // Extract DMA parameters
    dma_length = get_dma_length(additional_messages[0]);
    dma_offset = get_dma_offset(additional_messages[0]);
    dma_address = get_dma_address(additional_messages[1]);

    // Form the DMA request
    dma_request_t the_request;

    the_request.channel_id  = channel_id;
    the_request.type        = NORMAL_TYPE;  // All FE2BE DMAs are "normal" as there is no final ACK needed for the PEIP interface
    the_request.control     = (DMA_SINC | DMA_DINC | DMA_DSIZE_WORD); // Increment both srcAddr and dstAddr, with 32-bit transfers
    the_request.srcAddr     = dma_address;
    the_request.dstAddr     = (int)be->peip_interface.data_in_address[channel_id] + dma_offset;    // Calculated as the pointer into this channel's data section + offset
    the_request.length      = dma_length;

    // Add DMA request to the DMA queue (FE->BE)
    enqueue(&be->dma_queue_fe_to_be, the_request);

    return;
}

// ***********************************************************
// Function : _fe_segment_done
// Purpose  : Handles the front-end segment done message (5 additional messages)
// Expected Message(s):
//  0) (OPCODE, channel_id)
//  1) Word 0 of command header
//  2) Word 1 of command header
//  3) Word 2 of command header
//  4) Word 3 of command header
//  5) Word 4 of command header
// ***********************************************************
void _fe_segment_done(message_t argument, back_end_status * be)
{
    // Channel ID
    int channel_id      = 0;

    // Message parameters
    int num_messages    = 5;
    message_t additional_messages[5];

    // Outgoing message
    message_t out_message   = 0;    // Variable to hold the message
    int num_out_messages    = 1;    // Variable to hold the number of messages to send

    // Pointer to cmd header data section
    volatile Huint *cmd_header_pointer;

    // Extract channel ID
    channel_id = get_channel(argument);

    // Extract the additional messages
    num_messages = 5;
    get_messages(additional_messages, num_messages);

    // Should we check for "already active" here???
    
    // Commit this channel's command/data to the PEIP by:
    //  * Writing all command words to the command header in portion for that channel (making sure that important flags remain unset)
    //  * Writing in the "commit" flags, namely MSG_AVAIL

    // Indicate that this channel now has an active message
    be->active_channels[channel_id] = CHANNEL_USED;

    // Setup pointer to command header in section of the peip interface
    cmd_header_pointer = (Huint *)be->peip_interface.command_header_in_address[channel_id];

    // Clear MSG_AVAIL flag
    int original_word = additional_messages[CMD_HEADER_WORD_WITH_FLAGS];
    additional_messages[CMD_HEADER_WORD_WITH_FLAGS] = additional_messages[CMD_HEADER_WORD_WITH_FLAGS] & (~MSG_AVAIL_MASK);

    // Write in each command header word
    int counter = 0;
    for (counter = 0; counter < 5; counter ++)
    {
        *(cmd_header_pointer + counter) = additional_messages[counter];
    }

    // Write in the original word containing the MSG_AVAIL flag thus "committing" the command
    *(cmd_header_pointer + CMD_HEADER_WORD_WITH_FLAGS) = original_word;

    // Now acknowledge the FE with a BE_SEG_DONE command
    out_message = form_be_segment_done(channel_id);
    num_out_messages = 1;
    send_messages(&out_message,num_out_messages);
   
    return;
}

// ***********************************************************
// Function : _fe_data_addr
// Purpose  : Handles the front-end data address message (1 additional message)
// Expected Message(s):
//  0) (OPCODE, channel_id, dma_length)
//  1) (dma address)
// ***********************************************************
void _fe_data_addr(message_t argument, back_end_status * be)
{
    // Message parameters
    int channel_id      = 0;    // Variable to hold channel ID
    int num_messages    = 1;
    message_t additional_messages[1];

    // Data address parameters
    int max_dma_length = 0;
    int dest_address = 0;

    // Extract channel ID
    channel_id = get_channel(argument);

    // Extract max. DMA length
    max_dma_length = get_dma_length(argument);

    // Extract the additional data address messages
    num_messages = 1;
    get_messages(additional_messages, num_messages);

    // Extract DMA destination address
    dest_address = get_dma_address(additional_messages[0]);

    // Setup DMA parameters for the current transfer, and indicate that the transfer is now ready
    be->be_to_fe_max_transfer_size      = max_dma_length; 
    be->be_to_fe_destination_address    = dest_address; 
    be->be_to_fe_transfer_ready         = Htrue;

    // Check to see if the a current transfer exists, and if so, start it up
    if (be->current_dma_transfer_be_to_fe_exists)
    {
        // Adjust current DMA transfer parameters using the new data (dest. address)
        be->current_dma_transfer_be_to_fe.dstAddr = dest_address;

        //  Setup current transfer size -
        //   * If data to be transferred is greater than max transfer size --> do max transfer size
        //   * Otherwise just transfer the amount of data specified.
        if (be->current_dma_transfer_be_to_fe.length > be->be_to_fe_max_transfer_size)
        {
            be->be_to_fe_current_transfer_size = be->be_to_fe_max_transfer_size; 
        }
        else
        {
            be->be_to_fe_current_transfer_size = be->current_dma_transfer_be_to_fe.length; 
        }
        
        // Start the DMA process
        perform_dma_request_be_to_fe(be);
    }

    return;
}

// *********************************************************************************************
// Function : process_request
// Purpose  : Performs all processing for requests from the front-end
// *********************************************************************************************
void process_request(message_t argument, back_end_status * be)
{
    int opcode;
/*
    // ********************************************************************
    // This is just stub processing and should be removed later
    // Perform request processing
    // Perform some processing
    argument = argument + 1;
    // Write data to the front-end
    bwrite_fsl(argument,MY_FSL_ID);
    return;
    // ********************************************************************
*/
    // Decode request (each handler function will grab additional messages as necessary, per request)
    opcode = get_opcode(argument);
    switch(opcode)
    {
    case OP_CHANNEL_RESERVE :
        _reserve_channel(argument, be);
 		 break;
    case OP_DMA_REQ         :
         _fe_dma_request(argument, be);
 		 break;
    case OP_FE_SEG_DONE     :
         _fe_segment_done(argument, be);
 		 break;
    case OP_DATA_ADDR       :
         _fe_data_addr(argument, be);
 		 break;
    default :
         // Anything else should be ignored, as it is malformed (i.e. not a valid "starter" message)
 		 break;
    }
    
    return;
}

