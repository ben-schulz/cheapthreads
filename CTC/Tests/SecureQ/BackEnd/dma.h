/*
DMA (.h)

This file contains all of the defintions for the DMA device
(OPB Central DMA Controller)

*/


#include <httype.h>
#include <htconst.h>

// DMA Reset
#define DMA_RESET			(0x0000000A)

// DMA Control for Address Increments
#define DMA_SINC			(0x80000000)
#define DMA_DINC			(0x40000000)

// DMA Control for Data Size
#define DMA_DSIZE_BYTE	(0x00000001)
#define DMA_DSIZE_HWORD	(0x00000002)
#define DMA_DSIZE_WORD	(0x00000004)

// Offsets for DMA core
#define  DMAMIR      (0x0000)
#define  DMACR		 (0x0004)
#define  SRCADDR	 (0x0008)
#define  DSTADDR	 (0x000C)
#define  DMALENGTH	 (0x0010)
#define  DMASTATUS	 (0x0014)
#define  DMAISR		 (0x002C)
#define  DMAIER		 (0x0030)

// Masks for DMA status register
#define DMA_BUSY_MASK       (0x80000000)
#define DMA_BUS_ERROR_MASK  (0x40000000)
#define DMA_BUS_TOUT_MASK   (0x20000000)

// Masks for DMA ISR register
#define DMA_ERROR_MASK      (0x00000002)
#define DMA_DONE_MASK       (0x00000001)

// DMA configuration structure
typedef struct
{
    Huint   base;   // base address of DMA core
} dma_config_t;

// DMA device structure
typedef struct
{
    volatile    Huint   *dma_mir;       // Register addresses
    volatile    Huint   *dma_control;
    volatile    Huint   *src_address;
    volatile    Huint   *dst_address;
    volatile    Huint   *dma_length;
    volatile    Huint   *dma_status;
    volatile    Huint   *dma_isr;
    volatile    Huint   *dma_ier;
} dma_t;

// ******************************************************************
// Function : dma_create
// Purpose  : Initializes a DMA structure for a
// specific DMA device (init's. pointers and resets the device)
// ******************************************************************
void dma_create( dma_t *dma, dma_config_t *config )
{
    // Setup the addresses for the DMA registers
    dma->dma_mir        = (Huint*)(config->base + DMAMIR);
    dma->dma_control    = (Huint*)(config->base + DMACR);
    dma->src_address    = (Huint*)(config->base + SRCADDR);
    dma->dst_address    = (Huint*)(config->base + DSTADDR);
    dma->dma_length     = (Huint*)(config->base + DMALENGTH);
    dma->dma_status     = (Huint*)(config->base + DMASTATUS);
    dma->dma_isr        = (Huint*)(config->base + DMAISR);
    dma->dma_ier        = (Huint*)(config->base + DMAIER);

    // Reset the DMA device
    *dma->dma_mir = 0;
    *dma->dma_mir = DMA_RESET;
    *dma->dma_mir = 0;    
}

// ******************************************************************
// Function : setup_dma_transfer
// Purpose  : Initializes a DMA transfer (does not start it)
// ******************************************************************
void setup_dma_transfer( dma_t *dma, Huint control, Huint srcAddr, Huint dstAddr)
{
    // Setup transfer parameters (SINC, DINC, and DSIZE)
    *dma->dma_control = control;

    // Setup source and destination addresses
    *dma->src_address = srcAddr;
    *dma->dst_address = dstAddr;
}

// ******************************************************************
// Function : begin_dma_transfer
// Purpose  : Invokes a DMA transfer (does not check to see if device is free)
// ******************************************************************
void begin_dma_transfer( dma_t *dma, Huint length)
{
    // Setup length (this causes the DMA transaction to begin)
    *dma->dma_length = length;
}

// ******************************************************************
// Function : perform_dma_transfer
// Purpose  : Sets up and invokes a DMA transfer (does not check to see if device is free)
// ******************************************************************
void perform_dma_transfer( dma_t *dma, Huint control, Huint srcAddr, Huint dstAddr, Huint length)
{
    // Setup transfer
    setup_dma_transfer(dma, control, srcAddr, dstAddr);

    // Start transfer
    begin_dma_transfer(dma, length);
}

// ******************************************************************
// Function : is_dma_available
// Purpose  : Checks to see if a DMA device is available (not busy)
// ******************************************************************
Hbool is_dma_available( dma_t *dma)
{
    // Check DMA status
    if ((*dma->dma_status) & DMA_BUSY_MASK)
    {
        return Hfalse;
    }
    else
    {
        return Htrue;
    }
}

// ******************************************************************
// Function : is_dma_done
// Purpose  : Checks to see if a DMA device is done
// ******************************************************************
Hbool is_dma_done( dma_t *dma)
{
    // Check DMA ISR
    if ((*dma->dma_isr) & DMA_DONE_MASK)
    {
        return Htrue;
    }
    else
    {
        return Hfalse;
    }
}

// ******************************************************************
// Function : is_dma_error
// Purpose  : Checks to see if a DMA device has an error
// ******************************************************************
Hbool is_dma_error( dma_t *dma)
{
    // Check DMA ISR
    if ((*dma->dma_isr) & DMA_ERROR_MASK)
    {
        return Htrue;
    }
    else
    {
        return Hfalse;
    }
}

