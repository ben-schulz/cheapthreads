/*


   BACK END (.c)

   Contains the "main program" of the back-end MicroBlaze.
   This code manages:

   * All FSL communication
   * All DMA device control
   * All multi-port memory communication

*/

#include <stdio.h>
#include <string.h>
#include <httype.h>
#include <htconst.h>
#include "mb_interface.h"
#include "back_end.h"

// *************
// Main Program
// *************
int main( )
{
    // Message from front-end
    message_t arg;

    // Flag to test invalidity of front-end data
    int invalid;

    // Back-end status structure
    back_end_status be;

    // ************************
    // Initialize BE data
    // ************************
    initialize_back_end_status(&be);
	
    // ************************
    // Infinitely process
    // ************************
	while(1)
	{
        // Grab data from the front-end (asynchronously)
        //read_fsl(arg,MY_FSL_ID);  // Synchronous way
        while(1)
        {

             // Perform a non-blocking read
             nbread_fsl(arg,MY_FSL_ID);

             // Check the validity of the data (must be done after the read/write operation)
             fsl_isinvalid(invalid);   // 1 = invalid, 0 = valid

            // Check validity:
            // If valid, break out of loop and process request
            // If invalid, stay in loop
            if (!invalid)
                break;

            // ********************************************
            // Invalid, perform background processing
            // ********************************************
            background_processing(&be);
        }

        // ********************************************
        // Valid, service request and then perform
        // a round of background processing
        // ********************************************
        process_request(arg, &be);
        background_processing(&be);
	}

    return 0;
}



