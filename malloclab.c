  
/*  <Eugene Yu Jun Hao 1900094810>
 *  mm.c - Malloc Simulator
 *  Segregated Free List + First Fit
 *  Details:
 *  1. Free list structure - 
 *          previous ptr == heaplist_p : head
 *          next ptr == heaplist_p : tail
 *  2. Free list size increase by power of 2, starting from 16 bytes(Min block size)
 *  3. Be cautious at the insertion and removal of free list nodes!
 * 
 *  Extra Optimization:
 *  1. Relative Address (Maximum size of Heap is 2^32) -
 *     Method: Calculate the offset of address from heap_listp
 *     Result: reduce required bit for header and footer to 4 bytes each
 * 
 *  2. Footer only required for Free Blocks (for merging free blocks) -
 *     However, removal of footnote result to information loss of the previous
 *     block allocation (which is important in coalesce). 
 *     Solution: using the 2nd bit of header to record the allocation
 *     of previous block.
 *     Result: extra 4bytes for payloads
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/*=========================== variables, constants and macros ===========================*/
/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */  
/* Pointer to free list */
static char *root = 0;        /* default operator variable */
static char *root1 = 0;       /* root to free list 1 ~ 10 */
static char *root2 = 0;
static char *root3 = 0; 
static char *root4 = 0; 
static char *root5 = 0; 
static char *root6 = 0; 
static char *root7 = 0;
static char *root8 = 0;  
static char *root9 = 0;    
static char *root10 = 0;  

#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */  

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)      
#define GET_PREV_ALLOC(p) (GET(p) & 0x2)              

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

/* Relative address due to maximum size of heap is 2^32 */
#define ADDR2OF(address)    (size_t)(address) - (size_t)(heap_listp)    
#define OF2ADDR(offset)    (size_t)(offset) + (size_t)(heap_listp)

/* Store/Read previous and next free list node */
#define GET_PREV(bp)    (OF2ADDR(*((unsigned int *)(bp))))
#define GET_NEXT(bp)    (OF2ADDR(*((unsigned int *)(bp + WSIZE))))
#define SET_PREV(bp, val)   (*(unsigned int *)bp = (unsigned int)ADDR2OF(val))
#define SET_NEXT(bp, val)   (*(unsigned int *)(bp + WSIZE) = (unsigned int)ADDR2OF(val)) 

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void insert_list(void *bp, size_t size);
static void remove_list(void *bp, size_t size);
static void *size2ptr(size_t size);
static void update_root(size_t size);

/*=========================== MAIN FUNCTIONS ===========================*/

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) 
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 3)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 3)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 3));     /* Epilogue header, PREV_ALLOC = 1 */ 
    heap_listp += (2*WSIZE);
    root = heap_listp;
    root1 = root;
    root2 = root; 
    root3 = root; 
    root4 = root; 
    root5 = root; 
    root6 = root;  
    root7 = root; 
    root8 = root; 
    root9 = root; 
    root10 = root; 
 
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;  
}

/*
 * malloc - alloc block from heap
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if(heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if(size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if(size <= WSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);                  
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);                                 
    return bp;
}

/*
 * free - free block
 */
void free(void *bp){
    if(bp == 0) 
        return;
    size_t size = GET_SIZE(HDRP(bp));
    if(heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0) | GET_PREV_ALLOC(HDRP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * realloc - reallocate block(from mm-naive.c)
 * 
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0){
        mm_free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL){
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr){
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    mm_free(oldptr);

    return newptr;
}

/*
 * calloc - memset block to zero(from mm-naive.c)
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/*=========================== STANDARD HELPER FUNCTIONS ===========================*/
/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*=========================== HELPER FUNCTIONS TO WORK ON ===========================*/
/*
 * extend_heap - ask for more heap memory
 */
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp))));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}

/*
 * insert_list - insert bp to the front of free list (LIFO policy)
 * NOTES: Remember to choose free list of proper bucket size
 *        and update root afterwards 
 */
static void insert_list(void *bp, size_t size){ 
    /* start<-bp<->root->something */
    root = size2ptr(size);
    SET_PREV(bp, heap_listp);
    SET_NEXT(bp, root);
    if (root != heap_listp) /* free list not empty */
        SET_PREV(root, bp);
    root = bp;
    update_root(size);
}

/* 
 * remove_list
 * bp?
 * 1. Is root: heap_listp -> root -> b1
 * 2. Is tail: b1 -> tail -> heap_listp
 * 3. Both root and tail: heap_listp -> root -> heap_listp
 * 4. Other: b1 -> bp -> b2
 * 
 * NOTES: Remember to choose free list of proper bucket size
 *        and update root afterwards 
 */
static void remove_list(void *bp, size_t size){
    void *prev = (void *)GET_PREV(bp);
    void *next = (void *)GET_NEXT(bp);
    root = size2ptr(size);
    if(prev != heap_listp) /* bp is not root */
        SET_NEXT(prev,next);
    if(next != heap_listp) /* bp is not tail */
        SET_PREV(next,prev);
    if(bp == root)
        root = next;
    update_root(size);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp){
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        ;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_list(NEXT_BLKP(bp), GET_SIZE(HDRP(NEXT_BLKP(bp))));
        PUT(HDRP(bp), PACK(size,2));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_list(PREV_BLKP(bp), GET_SIZE(HDRP(PREV_BLKP(bp))));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,     
            GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_list(NEXT_BLKP(bp), GET_SIZE(HDRP(NEXT_BLKP(bp))));
        remove_list(PREV_BLKP(bp), GET_SIZE(HDRP(PREV_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 
            GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)))));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    insert_list(bp, size);
    PUT(HDRP(NEXT_BLKP(bp)), (GET(HDRP(NEXT_BLKP(bp))) & (~0x2)));
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));   
    remove_list(bp, csize);
    if ((csize - asize) >= (2 * DSIZE)) { 
        PUT(HDRP(bp), PACK(asize, 1+GET_PREV_ALLOC(HDRP(bp))));
        bp = NEXT_BLKP(bp);
        insert_list(bp, csize-asize);
        PUT(HDRP(bp), PACK(csize-asize, 2));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } 
    else{ 
        PUT(HDRP(bp), PACK(csize, 1+GET_PREV_ALLOC(HDRP(bp))));
        PUT(HDRP(NEXT_BLKP(bp)), (GET(HDRP(NEXT_BLKP(bp))) | (0x2)));
    }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize){ 
    /* First-fit search */
    void *bp;

    size_t size = 0x10;
    for(bp = size2ptr(size); size<=8192; bp = size2ptr(size)){
        size = size << 1;
        for(; bp != heap_listp; bp = (void *)GET_NEXT(bp)){
            if(asize <= GET_SIZE(HDRP(bp))) 
                return bp;
        }
    }
    return NULL; /* No fit */
}

/*
 * size2ptr - Select proper free list(bucket) according to size
 */
static void *size2ptr(size_t size){
    if(size <= 16) return root1;
    else if(size <= 32) return root2;
    else if(size <= 64) return root3;
    else if(size <= 128) return root4;
    else if(size <= 256) return root5;
    else if(size <= 512) return root6;
    else if(size <= 1024) return root7;
    else if(size <= 2048) return root8;
    else if(size <= 4096) return root9;
    else return root10;
}

/*
 * update_root: update roots of free list after used
 */
static void update_root(size_t size){
    if(size <= 16) root1 = root;
    else if(size <= 32) root2 = root;
    else if(size <= 64) root3 = root;
    else if(size <= 128) root4 = root;
    else if(size <= 256) root5 = root;
    else if(size <= 512) root6 = root;
    else if(size <= 1024) root7 = root;
    else if(size <= 2048) root8 = root;
    else if(size <= 4096) root9 = root;
    else root10 = root;
}

/*
 * mm_checkheap - Make debug easier
 * 1.Heap check for: 
 *      Block address alignment of 8, Block in heap, Heap exceed boundaries
 * 2.Free List check for:
 *      Next/Previous pointer error, Bucket range error,
 *      Record amount of free blocks
 */
void mm_checkheap(int verbose){
    void *ptr;
    /* Heap Check */
    for(ptr = heap_listp; GET_SIZE(ptr)>0; ptr = (void *)GET_NEXT(ptr)){
        if(!aligned(ptr)){
            printf("Alignment Error\n");
            exit(0); 
        }
        if(!in_heap(ptr)){
            printf("Block not in heap\n");
            exit(0);
        }
    }
    if((size_t)ptr - (size_t)heap_listp > ((size_t)(0x1)<<32)){ 
        printf("Heap Exceed Boundaries of 2^32\n");
        exit(0);
    }

    /* Free List Check */
    size_t size = 0x10;
    size_t cnt = 0;
    for(ptr = size2ptr(size); size<=8192; ptr = size2ptr(size)){
        for(; (void *)GET_NEXT(ptr) != heap_listp; ptr = (void *)GET_NEXT(ptr)){
            cnt++;
            if((void *)GET_PREV(GET_NEXT(ptr)) != ptr){
                printf("Next/Previous pointer error\n");
                exit(0);
            }
            if(GET_SIZE(HDRP(ptr)) > size || GET_SIZE(HDRP(GET_NEXT(ptr))) > size){
                printf("Exceed Bucket Range\n");
                exit(0);
            }
        }
        cnt++;
        size = size << 1;
    }
    if(verbose){
        printf("Free blocks count: %ld\n",cnt);
    }
}
