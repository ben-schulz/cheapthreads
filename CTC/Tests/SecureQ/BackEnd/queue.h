/*
 queue (.h)

 This file defines an array-based circular queue

*/

#include <stdio.h>

// DMA request types
#define  NORMAL_TYPE   0
#define  FINAL_TYPE    1

// Type definition for DMA request
typedef struct
{
    int channel_id;     // channel that is being DMAed
    int type;           // type of DMA transfer

    Huint control;      // DMA parameters: control, srcAddr, dstAddr, length
    Huint srcAddr;
    Huint dstAddr;
    Hint length;
} dma_request_t;

// Definition for the individual elements in the queue
typedef dma_request_t queue_element_t;

// Maximum queue size
#define MAX_QUEUE_SIZE  100

// Definition for the queue itself
typedef struct
{
    int head;
    int tail;
    queue_element_t contents[MAX_QUEUE_SIZE];
} queue_t;

// *******************************************************
// Function : initialize_queue
// Purpose  : Sets up the internal queue variables
// *******************************************************
void initialize_queue(queue_t * q)
{
    // Initialize queue pointers to 0
    q->head = 0;
    q->tail = 0;
}

// *******************************************************
// Function : is_empty
// Purpose  : Checks to see if a queue is empty
// *******************************************************
Hbool is_empty(queue_t * q)
{
    // Empty if head ptr. is the same as tail ptr.
    if (q->head == q->tail)
        return Htrue;
    else
        return Hfalse;
}

// *******************************************************
// Function : not_empty
// Purpose  : Checks to see if a queue is not empty
// *******************************************************
Hbool not_empty(queue_t * q)
{
    // Not empty if pointers are different
    if (q->head == q->tail)
        return Hfalse;
    else
        return Htrue;
}

// *******************************************************
// Function : is_full
// Purpose  : Checks to see if a queue is full
// *******************************************************
Hbool is_full(queue_t * q)
{
    // Full if tail will "meet" the head
    if (q->head == (q->tail+1))
        return Htrue;
    else
        return Hfalse;
}

// *******************************************************
// Function : enqueue
// Purpose  : Adds an element to a queue
// FIXME - should this check for overflow before or after
// *******************************************************
void enqueue(queue_t * q, queue_element_t e)
{
    // Place new element at the end of the queue
    q->contents[q->tail] = e;

    // Increment the tail pointer
    q->tail++;

    // Wrap tail pointer if needed
    if (q->tail >= MAX_QUEUE_SIZE)
    {
        if (q->head == 0)
        {
            printf("Queue Overflow!\n");
        }
        q->tail = 0;
    }
}

// *******************************************************
// Function : dequeue
// Purpose  : Removes the head element of a queue (and returns it)
// *******************************************************
queue_element_t dequeue(queue_t * q)
{
    if (is_empty(q))
    {
        printf("Error! Cannot perform a dequeue on an empty queue!\n");

        // Re-initialize queue (safe to do here)
        initialize_queue(q);
    }
    else
    {
        // Save the old head pointer
        int old_head = q->head;

        // Decrement the head pointer
        q->head++;

        // Wrap head pointer if needed
        if (q->head >= MAX_QUEUE_SIZE)
        {
            q->head = 0;
        }

        // Return the old head of the queue
        return q->contents[old_head];
    }
}

// *******************************************************
// Function : show_queue
// Purpose  : Displays the contents of a queue
// FIXME - make this more generic (for different elements)
// *******************************************************
void show_queue(queue_t * q)
{
    int counter = 0;

    printf("Showing queue (head = %d) (tail = %d)...\n", q->head, q->tail);

    if (q->tail < q->head)
    {
        for (counter = q->head; counter < MAX_QUEUE_SIZE; counter++)
        {
            printf("%d,\n",q->contents[counter]);
        }
        for (counter = 0; counter < q->tail; counter++)
        {
            printf("%d,\n",q->contents[counter]);
        }
    }
    else
    {
        for (counter = q->head; counter < q->tail; counter++)
        {
            printf("%d,\n",q->contents[counter]);
        }
    }
}

