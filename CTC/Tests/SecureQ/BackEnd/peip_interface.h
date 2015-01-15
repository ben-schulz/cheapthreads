/*
 PEIP Interface (.h)

 This file defines the PEIP interface (dual-port memory)

*/

//#include "comm_lib.h" 

// Definition for the base address of the PEIP's interface
#define PEIP_BASE_ADDRESS  (0x60000000)

// Definition for the number of 32-bit words that comprise a command header
#define HEADER_SIZE_IN_WORDS  5

// Definition for the word index in a command header for various fields
#define CMD_HEADER_WORD_WITH_LENGTH     2  
#define CMD_HEADER_WORD_WITH_FLAGS      3

// Type definition for a command header structure
typedef struct
{
    Huint header[HEADER_SIZE_IN_WORDS];     // each command header is composed of 5 (32-bit) words
} command_header_t;

// Type definition for the peip interface structure
typedef struct
{
    volatile Huint * command_header_in_address[NUM_CHANNELS];   // Pointers to command header in entries
    volatile Huint * command_header_out_address[NUM_CHANNELS];  // Pointers to command header out entries
    volatile Huint * data_in_address[NUM_CHANNELS];             // Pointers to data in entries
    volatile Huint * data_out_address[NUM_CHANNELS];            // Pointers to data out entries
} peip_interface_t;


// Macros used to retrieve channel ID from a command header (word 1)
#define CMD_HEADER_CHANNEL_MASK         0x0000ff00
#define CMD_HEADER_CHANNEL_SHIFT        8
#define cmd_header_get_channel_id(x)    ((x & CMD_HEADER_CHANNEL_MASK) >> CMD_HEADER_CHANNEL_SHIFT)

// Macros used to retrieve data length from a command header (word 2)
#define cmd_header_get_data_length(x)    (x)

// Macros used to retrieve flags from a command header (word 3)
#define CMD_HEADER_FLAG_MASK         0xffff0000
#define CMD_HEADER_FLAG_SHIFT        16
#define cmd_header_get_flags(x)    ((x & CMD_HEADER_FLAG_MASK) >> CMD_HEADER_FLAG_SHIFT)

// Macros used to retrieve error codes from a command header (word 3)
#define CMD_HEADER_ERROR_CODES_MASK         0x0000ffff
#define CMD_HEADER_ERROR_CODES_SHIFT        0
#define cmd_header_get_error_codes(x)    ((x & CMD_HEADER_ERROR_CODES_MASK) >> CMD_HEADER_ERROR_CODES_SHIFT)

// Useful masks (for 32-bit words from a command header)
#define MSG_AVAIL_MASK          (0x10000000)
#define MSG_READ_MASK           (0x08000000)
#define DATA_INCL_MASK          (0x04000000)

// *******************************************************
// Function : initialize_header
// Purpose  : Clears all data within a command header
// *******************************************************
void create_header(command_header_t * cmd_header)
{
    int i;

    // Setup all header words to ZERO
    for (i = 0; i < HEADER_SIZE_IN_WORDS; i++)
    {
        cmd_header->header[i] = 0;
    }
}

// *************************************************************************
// Function : get_command_channel
// Purpose  : Retrieves the channel identifier from a command header
// *************************************************************************
Huint get_command_channel(command_header_t * cmd_header)
{
    Huint word1;
    Huint channel_id;

    // Extract word1 as channel ID is located here
    word1 = cmd_header->header[1];

    // Channel ID is in bits 48 to 55 (which is in word1)
    channel_id = 0;
    channel_id = cmd_header_get_channel_id(word1);

    return channel_id;
}

// *************************************************************************
// Function : get_command_data_length
// Purpose  : Retrieves the data length from a command header
// *************************************************************************
Huint get_command_data_length(command_header_t * cmd_header)
{
    Huint word2;
    Huint data_length;

    // Extract word2 as data length is located here
    word2 = cmd_header->header[2];

    // Data length is this entire word
    data_length = 0;
    data_length = cmd_header_get_data_length(word2);

    return data_length;
}

// *************************************************************************
// Function : get_command_flags
// Purpose  : Retrieves the flags from a command header
// *************************************************************************
Huint get_command_flags(command_header_t * cmd_header)
{
    Huint word3;
    Huint flags;

    // Extract word3 as the flags are located here
    word3 = cmd_header->header[3];

    // Data length is this entire word
    flags = 0;
    flags = cmd_header_get_flags(word3);

    return flags;
}

// *************************************************************************
// Function : get_command_error_codes
// Purpose  : Retrieves the error_codes from a command header
// *************************************************************************
Huint get_command_error_codes(command_header_t * cmd_header)
{
    Huint word3;
    Huint codes;

    // Extract word3 as the error codes are located here
    word3 = cmd_header->header[3];

    // Data length is this entire word
    codes = 0;
    codes = cmd_header_get_error_codes(word3);

    return codes;
}

// ************************************************************************************************
// Function : get_command_header_in_address
// Purpose  : Returns the base address of the command header in portion of the dual-port memory
// ************************************************************************************************
Huint get_command_header_in_address(Huint channel_id)
{
    Huint address = 0;
    Huint channelByte = 0;

    // Command header in address is...
    // 0x0000 for channel 0
    // 0x1000 for channel 1
    // 0x2000 for channel 2
    // 0x3000 for channel 3
    // 0x4000 for channel 4
    // 0x5000 for channel 5
    // 0x6000 for channel 6
    // 0x7000 for channel 7
    // 0x8000 for channel 8
    // 0x9000 for channel 9
    
    // Check the range of the channel ID
    if (channel_id > 9)
    {
        // Invalid channel ID, return an invalid address
        address = PEIP_BASE_ADDRESS - 9999;
    }
    else
    {
        // Create address by trimming channel ID to a single byte and shifting the byte upwards
        channelByte = (channel_id & 0x000000ff);
        address = PEIP_BASE_ADDRESS + (channelByte << 12);
    }
   
    return address;
}

// ************************************************************************************************
// Function : get_command_header_out_address
// Purpose  : Returns the base address of the command header out portion of the dual-port memory
// ************************************************************************************************
Huint get_command_header_out_address(Huint channel_id)
{
    Huint address = 0;
    Huint channelByte = 0;

    // Command header in address is...
    // 0x0800 for channel 0
    // 0x1800 for channel 1
    // 0x2800 for channel 2
    // 0x3800 for channel 3
    // 0x4800 for channel 4
    // 0x5800 for channel 5
    // 0x6800 for channel 6
    // 0x7800 for channel 7
    // 0x8800 for channel 8
    // 0x9800 for channel 9
    
    // Check the range of the channel ID
    if (channel_id > 9)
    {
        // Invalid channel ID, return an invalid address
        address = PEIP_BASE_ADDRESS - 9999;
    }
    else
    {
        // Create address by trimming channel ID to a single byte and shifting the byte upwards
        channelByte = (channel_id & 0x000000ff);
        address = PEIP_BASE_ADDRESS + (channelByte << 12) + 0x800;
    }
   
    return address;
}

// ************************************************************************************************
// Function : get_data_in_address
// Purpose  : Returns the base address of the data in portion of the dual-port memory
// ************************************************************************************************
Huint get_data_in_address(Huint channel_id)
{
    Huint address = 0;
    Huint channelByte = 0;

    // Data in address is...
    // 0x0a000 for channel 0
    // 0x0c000 for channel 1
    // 0x0e000 for channel 2
    // 0x10000 for channel 3
    // 0x12000 for channel 4
    // 0x14000 for channel 5
    // 0x16000 for channel 6
    // 0x18000 for channel 7
    // 0x1a000 for channel 8
    // 0x1c000 for channel 9
    
    // Check the range of the channel ID
    if (channel_id > 9)
    {
        // Invalid channel ID, return an invalid address
        address = PEIP_BASE_ADDRESS - 9999;
    }
    else
    {
        // Create address by starting at PEIP + 0x0a000 + offset
        channelByte = (channel_id & 0x000000ff);
        address = PEIP_BASE_ADDRESS + 0x0a000 + (0x2000 * channelByte);
    }
   
    return address;
}

// ************************************************************************************************
// Function : get_data_out_address
// Purpose  : Returns the base address of the data out portion of the dual-port memory
// ************************************************************************************************
Huint get_data_out_address(Huint channel_id)
{
    Huint address = 0;
    Huint channelByte = 0;

    // Data in address is...
    // 0x0b000 for channel 0
    // 0x0d000 for channel 1
    // 0x0f000 for channel 2
    // 0x11000 for channel 3
    // 0x13000 for channel 4
    // 0x15000 for channel 5
    // 0x17000 for channel 6
    // 0x19000 for channel 7
    // 0x1b000 for channel 8
    // 0x1d000 for channel 9
    
    // Check the range of the channel ID
    if (channel_id > 9)
    {
        // Invalid channel ID, return an invalid address
        address = PEIP_BASE_ADDRESS - 9999;
    }
    else
    {
        // Create address by starting at PEIP + 0x0b000 + offset
        channelByte = (channel_id & 0x000000ff);
        address = PEIP_BASE_ADDRESS + 0x0b000 + (0x2000 * channelByte);
    }
   
    return address;
}

// *******************************************************
// Function : initialize_peip_interface
// Purpose  : Sets up the peip interface structure
// *******************************************************
void initialize_peip_interface(peip_interface_t * p)
{
    int i = 0;

    // Setup pointers for each channel
    for (i = 0; i < NUM_CHANNELS; i++)
    {
        p->command_header_in_address[i]     = (Huint *)(get_command_header_in_address(i)); 
        p->command_header_out_address[i]    = (Huint *)(get_command_header_out_address(i)); 
        p->data_in_address[i]               = (Huint *)(get_data_in_address(i)); 
        p->data_out_address[i]              = (Huint *)(get_data_out_address(i));

/*        xil_printf("Channel %d:\r\n",i);
        xil_printf("Command header in   = 0x%08x\r\n",p->command_header_in_address[i]);
        xil_printf("Command header out  = 0x%08x\r\n",p->command_header_out_address[i]);
        xil_printf("Command data in     = 0x%08x\r\n",p->data_in_address[i]);
        xil_printf("Command data out    = 0x%08x\r\n",p->data_out_address[i]);
*/
    }
}


