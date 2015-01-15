/*

  BE <--> FE Communication library

  This file contains the data and function definitions used to
  communicate over the FSL links between the FE and the BE.

*/

#include "mb_interface.h"

// Channel ID for FSL communication
#define MY_FSL_ID   0

// Number of PEIP channels
#define NUM_CHANNELS    10

// Message type definitions
#define MSG_FE_2_BE     0
#define MSG_BE_2_FE     1

// Type definitions
typedef unsigned int    message_t;

// Rename the FSL functions
#define bread_fsl(val,id)     getfsl(val,id)
#define bwrite_fsl(val,id)    putfsl(val,id)
#define nbread_fsl(val,id)    ngetfsl(val,id)
#define nbwrite_fsl(val,id)   nputfsl(val,id)

// Communication opcodes (8-bits = 256 possible opcodes)
#define OP_CHANNEL_RESERVE  0
#define OP_DMA_REQ          1
#define OP_FE_SEG_DONE      2
#define OP_DATA_ADDR        3
#define OP_DATA_OUT         4
#define OP_DMA_BDONE        5
#define OP_BE_SEG_DONE      6
#define OP_CHANNEL_GRANT    7
#define OP_CHANNEL_DENY     8
#define OP_DMA_FDONE        9

// Opcode macros
// (upper 8-bits)
#define OP_SHIFT    24
#define OP_MASK     0x000000FF
#define get_opcode(x)       ((x >> OP_SHIFT) & OP_MASK)
#define set_opcode(op,x)    (((op & OP_MASK) << OP_SHIFT) | x)

// Channel macros
// (upper-middle 8-bits)
#define CHAN_SHIFT    16
#define CHAN_MASK     0x000000FF
#define get_channel(x)          ((x >> CHAN_SHIFT) & CHAN_MASK)
#define set_channel(ch,x)       (((ch & CHAN_MASK) << CHAN_SHIFT) | x)

// DMA offset macros
// (upper 16-bits)
#define DMA_OFFSET_SHIFT    16
#define DMA_OFFSET_MASK     0x0000FFFF
#define get_dma_offset(x)          ((x >> DMA_OFFSET_SHIFT) & DMA_OFFSET_MASK)
#define set_dma_offset(off,x)       (((off & DMA_OFFSET_MASK) << DMA_OFFSET_SHIFT) | x)

// DMA length macros
// (lower 16-bits)
#define DMA_LENGTH_SHIFT    0
#define DMA_LENGTH_MASK     0x0000FFFF
#define get_dma_length(x)          ((x >> DMA_LENGTH_SHIFT) & DMA_LENGTH_MASK)
#define set_dma_length(len,x)       (((len & DMA_LENGTH_MASK) << DMA_LENGTH_SHIFT) | x)

// DMA address macros
// (all 32-bits)
#define get_dma_address(x)       (x)
#define set_dma_address(x)       (x)

// **********************************************************************************
// Function : form_channel_request
// Purpose  : Used to form a message used for requesting a channel (FE -> BE)
// **********************************************************************************
message_t form_channel_request(int channel)
{
    message_t message = 0;
    message = set_opcode(OP_CHANNEL_RESERVE, message);
    message = set_channel(channel, message);

    return message;
}

// **********************************************************************************
// Function : form_channel_grant
// Purpose  : Used to form a response message for a granted channel (BE -> FE)
// **********************************************************************************
message_t form_channel_grant(int channel)
{
    message_t message = 0;
    message = set_opcode(OP_CHANNEL_GRANT, message);
    message = set_channel(channel, message);

    return message;
}

// **********************************************************************************
// Function : form_channel_deny
// Purpose  : Used to form a response message for a denied channel (BE -> FE)
// **********************************************************************************
message_t form_channel_deny(int channel)
{
    message_t message = 0;
    message = set_opcode(OP_CHANNEL_DENY, message);
    message = set_channel(channel, message);

    return message;
}

// **********************************************************************************
// Function : form_be_segment_done
// Purpose  : Used to form a response message for segment done (BE->FE)
// **********************************************************************************
message_t form_be_segment_done(int channel)
{
    message_t message = 0;
    message = set_opcode(OP_BE_SEG_DONE, message);
    message = set_channel(channel, message);

    return message;
}

// **********************************************************************************
// Function : form_dma_fdone
// Purpose  : Used to form a response message for FE DMA done (BE->FE)
// **********************************************************************************
message_t form_dma_fdone(int channel)
{
    message_t message = 0;
    message = set_opcode(OP_DMA_FDONE, message);
    message = set_channel(channel, message);

    return message;
}

// **********************************************************************************
// Function : form_dma_bdone
// Purpose  : Used to form a response message for BE DMA done (BE->FE)
// **********************************************************************************
message_t form_dma_bdone(int channel, int length)
{
    message_t message = 0;
    message = set_opcode(OP_DMA_BDONE, message);
    message = set_channel(channel, message);
    message = set_dma_length(length, message);

    return message;
}

// **********************************************************************************
// Function : form_data_out
// Purpose  : Used to form a response message for a DATA OUT msg (BE->FE)
// **********************************************************************************
message_t form_data_out(int channel)
{
    message_t message = 0;
    message = set_opcode(OP_DATA_OUT, message);
    message = set_channel(channel, message);

    return message;
}

// **************************************************************
// Function : send_messages
// Purpose  : Sends (writes) a set of messages to the FSLs.
//            The send is done in order from index 0 up
// **************************************************************
void send_messages(message_t messages[], int num_messages)
{
    int counter = 0;

    for (counter = 0; counter < num_messages; counter++)
    {
        bwrite_fsl(messages[counter],MY_FSL_ID);
    }
}

// **************************************************************
// Function : get_messages
// Purpose  : Gets (reads) a set of messages from the FSLs
//            The get is done in order from index 0 up
// **************************************************************
void get_messages(message_t messages[], int num_messages)
{
    int counter = 0;

    for (counter = 0; counter < num_messages; counter++)
    {
        bread_fsl(messages[counter],MY_FSL_ID);
    }
}

// **************************************************************
// Function : display_message
// Purpose  : Displays a message
// **************************************************************
void display_message(int type, message_t msg)
{
    if (type == MSG_FE_2_BE)
    {
        print("FE -> BE msg =");
    }
    else
    {
        print("BE -> FE msg =");
    }

    switch(get_opcode(msg))
    {
    case OP_CHANNEL_RESERVE :
        xil_printf(" OP_CHANNEL_RESERVE (%d)\r\n",get_opcode(msg));
        break;
    case OP_DMA_REQ :
        xil_printf(" OP_DMA_REQ (%d)\r\n",get_opcode(msg));
        break;
    case OP_FE_SEG_DONE :
        xil_printf(" OP_FE_SEG_DONE (%d)\r\n",get_opcode(msg));
        break;
    case OP_DATA_ADDR :
        xil_printf(" OP_DATA_ADDR (%d)\r\n",get_opcode(msg));
        break;
    case OP_DATA_OUT :
        xil_printf(" OP_DATA_OUT (%d)\r\n",get_opcode(msg));
        break;
    case OP_DMA_BDONE :
        xil_printf(" OP_DMA_BDONE (%d)\r\n",get_opcode(msg));
        break;
    case OP_BE_SEG_DONE :
        xil_printf(" OP_BE_SEG_DONE (%d)\r\n",get_opcode(msg));
        break;
    case OP_CHANNEL_GRANT :
        xil_printf(" OP_CHANNEL_GRANT (%d)\r\n",get_opcode(msg));
        break;
    case OP_CHANNEL_DENY :
        xil_printf(" OP_CHANNEL_DENY (%d)\r\n",get_opcode(msg));
        break;
    case OP_DMA_FDONE :
        xil_printf(" OP_DMA_FDONE (%d)\r\n",get_opcode(msg));
        break;
    default:
        xil_printf("Unknown message (OP = %d)\r\n",get_opcode(msg));
    }
    xil_printf("\t--> 0x%08x\r\n",msg);
}


