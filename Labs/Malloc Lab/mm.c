/*

 My solution uses an explicit free list, a first-fit placement policy, and boundary tag coalescing.
 
 Blocks have this structure:
 
 FREE:
 ___________________________________________
 |        |      |      |         |        |
 | Header | Prev | Next | Payload | Footer |
 |________|______|______|_________|________|
 
 ALLOCATED:
 ________________________________________
 |        |      |      |      |        |
 | Header |       Payload      | Footer |
 |________|______|______|______|________|
 
 I have global pointers that can search through the whole heap list and the free list.
 
 
 Code is modified from the textbook, which I credit above the functions.
 
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "705512370",
    /* First member's full name */
    "Tyler Stovsky",
    /* First member's email address */
    "stovsky@ucla.edu",
    /* Second member's full name (leave blank if none) */
    "",
    
    /* Second member's email address (leave blank if none) */
    ""
};


/*
 These macros came from the book on page 857 (Figure 9.43).
 */

/* Basic constants and macros */
#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */
#define MINSIZE 24 /* 4 bytes for header + 16 for next and prev pointer + 4 for footer */
#define CHUNKSIZE (1<<16) /* Extend heap by this amount (bytes) */
#define ALIGNMENT 8 /* single word (4) or double word (8) alignment */


/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block bp bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block bp bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Get the next and previous free list pointers */
#define NEXT_FREE(bp) (*(char **)(bp + DSIZE))
#define PREV_FREE(bp) (*(char **)(bp))

/* Prototypes */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void removeFromList(void *bp);
static int mm_check(void);
static int check_overlap(void *bp);
static int check_coalesce(void *bp);
static int check_block(void *bp);
static int check_inheap(void *bp);


/* Global variables */
static char* heap_listp = 0; // This points to the first block
static char* free_listp = 0; // This points to the list of free blocks

/*
 
 * mm_init - Initializes the heap and sets up the free list.
 
*/

int mm_init(void)
{
    /* Create the initial empty heap */
    if((heap_listp = mem_sbrk(2 * MINSIZE)) == NULL){
        return -1;
    }

    /* Alignment Padding */
    PUT(heap_listp, 0);
    /* Prologue Header */
    PUT(heap_listp + WSIZE, PACK(MINSIZE, 1));
    /* Space for previous pointer */
    PUT(heap_listp + DSIZE, 0);
    /* Space for next pointer */
    PUT(heap_listp + DSIZE + WSIZE, 0);
    /* Prologue Footer */
    PUT(heap_listp + MINSIZE, PACK(MINSIZE, 1));
    /* Epilogue Header */
    PUT(heap_listp + WSIZE + MINSIZE, PACK(0, 1));
    
    /* Set the free block pointer */
    free_listp = heap_listp + DSIZE;

   
    /* Extend the heap */
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL){
        return -1;
    }

    return 0;
}


/*
 This code is modified from page 861 (Figure 9.47). It allocates a block in memory that is correctly aligned and is at least MINSIZE.
 */
void *mm_malloc(size_t size)
{
    size_t asize; 
    size_t extendsize;
    char *bp;

    if(size <= 0) return NULL;

    
    /* The size that we want is either the header and footer + payload, or if the desired size is too small then just use the minimum block size. */
    asize = MAX(ALIGN(size) + DSIZE, MINSIZE);

    /* If we can find a fit, then allocate */
    if((bp = find_fit(asize))){
        place(bp, asize);
        return bp;
    }

    /* If we can't find a fit, then we need to extend the heap and then allocate. */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    
    return bp;
}

/*
 * This code is from page 860 (Figure 9.46).  To free a block, all we need to do is set the allocated bit to 0 and then coalesce to merge free blocks together.
 */
void mm_free(void *bp)
{
    if(bp == NULL) return;

    size_t size = GET_SIZE(HDRP(bp));

    /* Set allocated bits to 0*/
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    /* Merge free blocks */
    coalesce(bp);
}

/*
 
 This code reallocates a block.  If the size is 0, it will free the block and return NULL.  If the pointer is NULL, then just allocate using malloc.  Otherwise, we need to allocate a new block and put the old contents into the new one.  We then need to return the address of the new block.
 
 */

void *mm_realloc(void *bp, size_t size)
{
    
    void *oldbp = bp;
    void *newbp;
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(oldbp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(oldbp)));
    size_t osize = GET_SIZE(HDRP(oldbp));


    int space = (osize < DSIZE + size) ? 1 : 0;

    /* If the size is 0, then this is a call to mm_free */
    if (size == 0) {
        mm_free(bp);
        newbp = 0;
        return NULL;
    }

    /* If the pointer is NULL, then this is a call to mm_malloc */
    if (oldbp == NULL) return mm_malloc(size);

    void *temp;
    size_t temp_size;
    size_t copy_size;

    
    /* If the new size is decreasing and we can't fit a free block afterwards */
    if (space == 0) {
        return bp;
    }
    
    /* If the new size is increasing */
    else {

        int next = GET_SIZE(HDRP(NEXT_BLKP(oldbp)));
        int prev = GET_SIZE(HDRP(PREV_BLKP(oldbp)));

        
        /* CASE 1: Previous and next are both unallocated and we can fit a block */
        if (next_alloc == 0 && prev_alloc == 0 && (prev + next + osize) >= (size + DSIZE)){
            newbp = PREV_BLKP(oldbp);
            temp = NEXT_BLKP(oldbp);
            temp_size = GET_SIZE(FTRP(newbp)) + GET_SIZE(FTRP(temp));
            size = temp_size + osize;
            copy_size = GET_SIZE(HDRP(oldbp));
            removeFromList(NEXT_BLKP(oldbp));
            removeFromList(PREV_BLKP(oldbp));
            PUT(HDRP(newbp), PACK(size, 1));
            memcpy(newbp, oldbp, copy_size);
            PUT(FTRP(newbp), PACK(size, 1));
            return newbp;
        }
        
        /* CASE 2: Previous is unallocated and we can fit a block */
        else if(prev_alloc == 0 && ((prev + osize) >= (size + DSIZE))){
           newbp = PREV_BLKP(oldbp);
           temp_size = GET_SIZE(FTRP(newbp));
           size = temp_size + osize;
           copy_size = GET_SIZE(HDRP(oldbp));
           removeFromList(PREV_BLKP(oldbp));
           PUT(HDRP(newbp), PACK(size, 1));
           memcpy(newbp, oldbp, copy_size);
           PUT(FTRP(newbp), PACK(size, 1));
           return newbp;
       }
        /* CASE 3: Next is unallocated and we can fit a block */
        else if(next_alloc == 0 && (next + osize) >= (size + DSIZE)){
            temp = NEXT_BLKP(oldbp);
            temp_size = GET_SIZE(FTRP(temp));
            size = temp_size + osize;
            removeFromList(NEXT_BLKP(bp));
            PUT(HDRP(oldbp), PACK(size, 1));
            PUT(FTRP(oldbp), PACK(size, 1));
            return oldbp;
        }

        /* CASE 4: Previous and next are both allocated */
        else {
            newbp = mm_malloc(size);
            copy_size = GET_SIZE(HDRP(oldbp));
            if (size < copy_size) copy_size = size;
            memcpy(newbp, oldbp, copy_size);
            mm_free(oldbp);
        }
        
    }
        return newbp;
    
}

/* This code is modified from page 860 (Figure 9.46).  It uses boundary-tag coalescing to merge free blocks together
 Additionally, this code will remove any blocks from the free list that were merged and it will add the new free block to the front of the free list*/
static void *coalesce(void *bp) {
    
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));


    /* CASE 1: Next block is free */
    if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removeFromList(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    
    /* CASE 2: Previous block is free */
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        removeFromList(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
    }

    /* CASE 3: Both previous and next block are free */
    else if(!prev_alloc && !next_alloc){

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        removeFromList(NEXT_BLKP(bp));
        removeFromList(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
    }

    /* Put the new coalesced block at the start of the free list */
    
    if (free_listp == NULL) {
        free_listp = bp;
        PREV_FREE(bp) = NULL;
        NEXT_FREE(bp) = NULL;
    }
    
    NEXT_FREE(bp) = free_listp;
    PREV_FREE(bp) = NULL;
    PREV_FREE(free_listp) = bp;
    free_listp = bp;
    
    
    return bp;
}


/* This function removes a block from the free list*/
static void removeFromList(void *bp) {

   
    if (free_listp == 0) return;
    
    /* If the pointer is in the middle of the list */
    if ((PREV_FREE(bp) != NULL) && (NEXT_FREE(bp) != NULL)) {
        PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);
        NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
    }
    
    /* If the pointer is at the beginning of the list */
    else if ((PREV_FREE(bp) == NULL) && (NEXT_FREE(bp) != NULL)) {
        free_listp = NEXT_FREE(bp);
        PREV_FREE(free_listp) = NULL;
    }
    
    /* If the pointer is at the end of the list */
    else if ((PREV_FREE(bp) != NULL) && (NEXT_FREE(bp) == NULL)) {
        NEXT_FREE(PREV_FREE(bp)) = NULL;
    }
    /* If the list is empty */
    else if ((PREV_FREE(bp) == NULL) && (NEXT_FREE(bp) == NULL)) {
        free_listp = 0;
    }
     
}


/* Extend the heap by the given amount of words
 Code is modified from page 858 (Figure 9.45) */

static void* extend_heap(size_t words){
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if(size < MINSIZE){
        size = MINSIZE;
    }

    if((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    
    /* Free block header */
    PUT(HDRP(bp), PACK(size, 0));
    /* Free block footer */
    PUT(FTRP(bp), PACK(size, 0));
    /* New epilogue header */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}



/* This is modified from page 920 in the textbook.  This function uses a first fit approach to find a free block that is big enough to hold the desired size*/
static void *find_fit(size_t size){
    void *bp;

    /* Iterate through the free list in order to find a block that is big enough*/
    for(bp = free_listp; bp != NULL; bp = NEXT_FREE(bp)){

        if(size <= GET_SIZE(HDRP(bp)) && !GET_ALLOC(HDRP(bp))){
            return bp;
        }
    }
    /* If no block exists that is big enough return NULL */
    return NULL;
}




/* This is modified from page 920 in the textbook.  It will place a block of the desired size in the free block.
 We need to check if the remainder of the free block size minus the size of the block we want to allocate would be greater than or equal to the minimum block size.  If it is, then we need to split the block into the allocated block and the rest of the free block.  Otherwise we can't split so we just allocate the whole block.*/
static void place(void *bp, size_t size){
    
    size_t asize = GET_SIZE(HDRP(bp));


    /* Splitting is needed */
    if((asize - size) >= MINSIZE){
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        removeFromList(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(asize - size, 0));
        PUT(FTRP(bp), PACK(asize - size, 0));
        coalesce(bp);
    }
    /* No splitting is needed */
    else{
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        removeFromList(bp);
    }
}

static int mm_check(void) {

    char* bp;
    int res = 1;
    
    /* Iterate through every block in the heap */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        
        /* If the block is allocated, check if it overlaps a different block */
        if (GET_ALLOC(HDRP(bp))) res = check_overlap(bp);
        
        /* If the block is not allocated, check if it is coalesced correctly */
        if (!GET_ALLOC(HDRP(bp))) res = check_coalesce(bp);
        
        /* Check block alignment and that header and footer match */
        res = check_block(bp);
        
        /* Check if the block is in the heap */
        res = check_inheap(bp);
        
    }
    return res;
}

/* This function checks if two blocks overlap each other */
static int check_overlap(void *bp) {
    
    if (GET_SIZE(HDRP(bp)) + bp - WSIZE >= NEXT_BLKP(bp)) {
        printf("BLOCKS OVERLAP\n");
        return 0;
    }
    return 1;
}

/* This function checks the alignment of blocks and if the header and footer match */
static int check_block(void *bp) {
    
    /* Check alignment */
    if (ALIGN(GET_SIZE(HDRP(bp))) != GET_SIZE(HDRP(bp))) {
        printf("NOT ALIGNED\n");
        return 0;
    }
    
    /* Check if the header and footer sizes match */
    if (ALIGN(GET_SIZE(HDRP(bp))) != GET_SIZE(HDRP(bp))) {
        printf("HEADER AND FOOTER SIZE DO NOT MATCH\n");
        return 0;
    }
    
    /* Check if the header and footer allocation matches */
    if (GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))) {
        printf("HEADER AND FOOTER ALLOCATION DO NOT MATCH\n");
        return 0;
    }
    return 1;
}

/* This function checks that there are no free blocks next to each other */
static int check_coalesce(void *bp) {
    
    if (!GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
        printf("BLOCKS ARE NOT COALESCED\n");
        return 0;
    }
    return 1;
}

/* This function checks if the pointer is in the heap */
static int check_inheap(void *bp) {
    
    if (bp > mem_heap_hi() && bp < mem_heap_lo()) {
        printf("NOT IN HEAP\n");
        return 0;
    }
    
    return 1;
}
