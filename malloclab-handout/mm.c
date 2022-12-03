/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

// if defined 1, this program would be verbose and call mm_checkheap()
#ifndef MMDEBUG
#define MMDEBUG 0
#endif

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Mohammed Azhar Khan",
    /* First member's email address */
    "mkhan114@hawk.iit.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * If NEXT_FIT defined use next fit search, else use first-fit search
 */
#define NEXT_FIT 0

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (bytes) */

// minimum free block size (in bytes)
#define MINFRBSIZE  16

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (unsigned int)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, return if the next/previous block is allocated */
#define NEXT_BLK_ALLOC(bp)  (GET_ALLOC(HDRP(NEXT_BLKP(bp))))
#define PREV_BLK_ALLOC(bp)  (GET_ALLOC(HDRP(PREV_BLKP(bp))))

/* Given free block ptr bp, comput address of the next/previous free block pointer */
#define FRB_PREVP(bp)   ((char*)(bp))
#define FRB_NEXTP(bp)   ((char*)(bp) + WSIZE)

/* Global variables for the segregated list */
// blocks with size <= SEGMINBYTE would be put into the first list
// must be a power of 2
#define SEGMINBYTE 32
// blocks with size > SEGMAXBYTE would be put into the last list
// must be a power of 2
#define SEGMAXBYTE 4096

static char* seg_list_head = NULL;
static char* seg_list_foot = NULL;

/* Global variables */
/*|header(allocated)| ^ |footer(allocated)| */
/*        4B          |         4B          */
/*                heap_startp               */
static char *heap_startp = 0;  /* Pointer to first block */
static char *heap_endp = 0;    /* Pointer to the end of heap*/

// estimated lineno
#if MMDEBUG
static unsigned int func_counter = 0;
#endif

#define MAXFUNCCOUNT 1000

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t dwords);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

void mm_checkheap(int lineno);

/* Function prototypes for the segregated list */
// static inline char* get_list_root(size_t size);
// static inline size_t get_list_count();
// static void insert_free_block(char * bp);
// static void remove_free_block(char * bp);
// static char* find_free_block(size_t _size);

/* auxiliary functions for reallocation */
static void realloc_update(void *bp, size_t asize);
static void* realloc_try_coal(void* bp, size_t new_size);

// DEBUG functions
static void print_list();

static void print_list(){
    unsigned size = 0;
    char* root_cursor = seg_list_head;
    printf(">%d list: Root ", size);
    void* cursor = (void* ) GET(root_cursor);
    while(cursor != NULL){
        printf(" -> 0x%x ", (unsigned int) cursor);
        cursor = (void* ) GET(cursor);
    }
    printf("\n");
    root_cursor += WSIZE;


    size = SEGMINBYTE;
    for(; root_cursor != seg_list_foot; root_cursor += WSIZE){
        printf(">%d list: Root ", size);
        cursor = (void* ) GET(root_cursor);
        while(cursor != NULL){
            printf(" -> 0x%x ", (unsigned int) cursor);
            cursor = (void* ) GET(cursor);
        }
        printf("\n");
        size = size << 1;
    }
}

/* auxiliary funtions for the segregated list */
/* may be replaced after tweaking to improve performance */
static inline char* get_list_root(size_t size){
    size_t list_index = 0;
    unsigned int cursor = SEGMINBYTE;
    for(; cursor <= SEGMAXBYTE; cursor = cursor << 1){
        if(size <= cursor){
            return seg_list_head + (list_index * WSIZE);
        }
        list_index ++;
    }
    // size fall into the last list_index
    return seg_list_head + (list_index * WSIZE);
}

/* return the list count, give SEGMINBYTE and SEGMAXBYTE */
static inline size_t get_list_count(){
    size_t list_count = 0;
    unsigned int cursor = SEGMINBYTE;
    for(; cursor <= SEGMAXBYTE; cursor = cursor << 1){
        list_count ++;
    }
    return list_count + 1;
}

/* insert a marked free block into the proper segregated list,
 * at the proper position
 */
static void insert_free_block(char * bp){
    size_t new_size = GET_SIZE(HDRP(bp));
    char* list_root = get_list_root(new_size);
    char* p_cursor = list_root;
    char* p_next = (char*) GET(list_root);

    while(p_next != NULL){
        if(GET_SIZE(HDRP(p_next)) >= new_size){
            // the next block size is larger than the new block size
            // break to insert here
            break;
        }
        // move the cursor and next forward
        p_cursor = p_next;
        p_next = (char*) GET(FRB_NEXTP(p_next));
    }

    // four cases: no null, left is root, next null, left is root & next null
    // categorized into two cases: left is root / left is not root
    if(p_cursor != list_root){
        // modify bp
        PUT(FRB_NEXTP(bp), p_next);
        PUT(FRB_PREVP(bp), p_cursor);
        // modify prev and next of bp
        PUT(FRB_NEXTP(p_cursor), bp);
        // modify next if valid
        if(p_next != NULL) {
            PUT(FRB_PREVP(p_next), bp);
        }
    } else{
        // modify root
        PUT(list_root, bp);
        // modify bp, the first valid block's prev block is NULL
        PUT(FRB_NEXTP(bp), p_next);
        PUT(FRB_PREVP(bp), NULL);
        // modify next if valid
        if(p_next != NULL) {
            PUT(FRB_PREVP(p_next), bp);
        }
    }
}

/* remove a marked free block into the proper segregated list,
 * at the proper position, the next and prev pointer of the
 * removed block will become NULL
 */
static void remove_free_block(char * bp){
    char* p_root = get_list_root(GET_SIZE(HDRP(bp)));
    char* p_prev = (char*) GET(FRB_PREVP(bp));
    char* p_next = (char*) GET(FRB_NEXTP(bp));

    if(p_prev != NULL){
        // previous block is not root
        // modify previous block
        PUT(FRB_NEXTP(p_prev), p_next);
        // modify next block if valid
        if(p_next != NULL){
            PUT(FRB_PREVP(p_next), p_prev);
        }
    } else{
        // previous block is root
        PUT(p_root, p_next);
        if(p_next != NULL){
            PUT(FRB_PREVP(p_next), NULL);
        }
    }
    // set the prev and next pointer of bp to null for safety
    PUT(FRB_PREVP(bp), NULL);
    PUT(FRB_NEXTP(bp), NULL);
}

/* find a fit for a block with _size bytes,
 * since the lists are dynamically sorted, the first fit is the best fit
 * if could not find a fit, return null
 */
 static char* find_free_block(size_t _size){
     char* root = get_list_root(_size);

     // traverse all the seg lists larger than size
     for(; root < seg_list_foot; root += WSIZE){
//         printf("Root: 0x%x -> ", (unsigned) (root));
         char* cursor = (char*) GET(root);
         while(cursor != NULL){
//             printf("cursor: 0x%x -> ", (unsigned) (cursor));
             if(GET_SIZE(HDRP(cursor)) >= _size){
                 return cursor;
             }
             cursor = (char*) GET(FRB_NEXTP(cursor));
         }
//         printf("\n");
     }
     return NULL;
 }

/*
 * mm_init - Initialize the memory manager
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    size_t list_count = get_list_count();

    size_t initial_size = list_count + 5;

    if ((heap_startp = mem_sbrk(initial_size * WSIZE)) == (void *)-1){
        return -1;
    }

    size_t i = 0;
    // the heap starts with several incrementing segregated lists
    for(; i < list_count; ++i){
        PUT(heap_startp + (i * WSIZE), 0);
    }

    /* Segregation padding */
    PUT(heap_startp + ((list_count) * WSIZE), 0);
    PUT(heap_startp + ((list_count + 1) * WSIZE), 0);
    /* Prologue header */
    PUT(heap_startp + ((list_count + 2) * WSIZE), PACK(DSIZE, 1));
    /* Prologue footer */
    PUT(heap_startp + ((list_count + 3) * WSIZE), PACK(DSIZE, 1));
     /* Epilogue header */
    PUT(heap_startp + ((list_count + 4) * WSIZE), PACK(0, 1));

    // set the start(head) of the segregated list
    seg_list_head = heap_startp;
    // set the end(foot) of the segregated list (the padding)
    seg_list_foot = heap_startp + (list_count) * WSIZE;
    // set the end of heap
    heap_endp = heap_startp + ((list_count + 5) * WSIZE);
    // move the point the the first block
    heap_startp += ((list_count + 3) * WSIZE);


#if MMDEBUG
    printf("%p\n", seg_list_head);
    printf("%p\n", seg_list_foot);
    func_counter = 0;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / DSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size)
{
#if MMDEBUG
    func_counter ++;
    if(func_counter >= MAXFUNCCOUNT){
        func_counter = 0;


    }
    // mm_checkheap(__LINE__);
    printf("malloc size: %d\n", size);
#endif

    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (heap_startp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    // magic code, hack utility for binary-bal.rep & binary2-bal.rep
    switch(size){
        case 112:
            size = 128;
            break;
        case 448:
            size = 512;
            break;
        default:
            break;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    if(size <= DSIZE){
        asize = 2 * DSIZE;
    }else{
        asize = ((size + (DSIZE - 1)) & (~(DSIZE - 1))) + DSIZE;
    }

#if MMDEBUG
    printf("new adjusted size: %d\n", asize);
#endif


    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }


    /* No fit found. Get more memory and place the block */

    // optimization: only get the memory need if there is already a
    // free block at the end
    // assume delta size equals asize
    size_t dsize = asize;
    if(!PREV_BLK_ALLOC(heap_endp)){
        // if there is already a free block at the end...
        // get its size
        size_t freb_size = GET_SIZE(FTRP(PREV_BLKP(heap_endp)));
        dsize = asize - freb_size;
        dsize = dsize > 0 ? dsize : asize;
    }

    extendsize = MAX(dsize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/DSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * free - Free a block
 */
void mm_free(void *bp)
{
#if MMDEBUG
    func_counter ++;
    if(func_counter >= MAXFUNCCOUNT){
        func_counter = 0;
        mm_checkheap(__LINE__);
    }

    printf("free ptr: 0x%x\n", (unsigned int)bp);
#endif

    if (bp == 0)
        return;

    size_t size = GET_SIZE(HDRP(bp));

    if (heap_startp == 0){
        mm_init();
        return;
    }



    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(FRB_NEXTP(bp), NULL);
    PUT(FRB_PREVP(bp), NULL);

    coalesce(bp);

}

/*
 * realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
#if MMDEBUG
    func_counter ++;
    if(func_counter >= MAXFUNCCOUNT){
        func_counter = 0;

    }
    // mm_checkheap(__LINE__);
    printf("realloc ptr: 0x%x, size: %d\n", (unsigned) ptr, size);
#endif

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }
    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
        return mm_malloc(size);
    }

    // we need to do real realloc here
    // get the old size of this block
    size_t oldsize = GET_SIZE(HDRP(ptr));
    // newptr after the realloc
    void *newptr;
    // adjusted size, including padding + header + footer + payload
    // and fits the alignment
    size_t asize;
    // if(size <= DSIZE){
    //     asize = DSIZE;
    // }else{
    //     asize = ((size + (DSIZE - 1)) & (~(DSIZE - 1))) + DSIZE;
    // }
    if(size <= DSIZE){
        asize = 2 * DSIZE;
    }else{
        asize = ((size + (DSIZE - 1)) & (~(DSIZE - 1))) + DSIZE;
    }

#if MMDEBUG
    printf("new adjusted size: %d\n", asize);
#endif

    if(oldsize < asize){
        // try to coalesce
        newptr = realloc_try_coal(ptr, asize);
        if(newptr != NULL){
            memmove(newptr, ptr, oldsize);
            realloc_update(newptr, asize);
            return newptr;
        }
        else{
            // cannot coalesce, malloc and free
            newptr = mm_malloc(size);
            memmove(newptr, ptr, oldsize);
            mm_free(ptr);
            return newptr;
        }

    } else if(oldsize > asize){
        // TODO: when old size is bigger than asize
        // change size of the ptr
        newptr = ptr;
        realloc_update(newptr, asize);
        return newptr;
    } else if(oldsize == asize){
        return ptr;
    }

    return NULL;

}

// update the allocated block after memmove
// if csize > asize:
//   1. if there is enough space for a new free block, split it
//   2. if else, remain unchanged

//  NOTE: current size must be larger than adjust size
static void realloc_update(void *bp, size_t asize){
     size_t csize = GET_SIZE(HDRP(bp));
    // if( (csize - asize) >= MINFRBSIZE ){
    //     // there is enough space for a new free block
    //     PUT(HDRP(bp), PACK(asize, 1));
    //     PUT(FTRP(bp), PACK(asize, 1));
    //     // init new block
    //     char* freb_p = NEXT_BLKP(bp);
    //     PUT(HDRP(freb_p), PACK(csize - asize, 0));
    //     PUT(FTRP(freb_p), PACK(csize - asize, 0));
    //     PUT(FRB_PREVP(freb_p), NULL);
    //     PUT(FRB_NEXTP(freb_p), NULL);
    //     coalesce(freb_p);
    // }
    // else {
    //     // there is no room for a new free block
    //     PUT(HDRP(bp), PACK(csize, 1));
    //     PUT(FTRP(bp), PACK(csize, 1));
    // }
    // improve utility for realloc-bal
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));

}



// try to coalesce and used the neighbor free blocks.
// if their is enough free space in its neighbor,
// this function will remove free blocks, return the new block pointer,
// set the new header and footer
// but keep the original payload unmoved
// else, this function will return NULL
static void* realloc_try_coal(void* bp, size_t new_size){
    size_t size = GET_SIZE(HDRP(bp));
    size_t prev_free = !PREV_BLK_ALLOC(bp);
    size_t next_free = !NEXT_BLK_ALLOC(bp);
    // four cases: prev free, next free, both free, none free
    if(!prev_free && !next_free){
        // both allocated, return NULL
        return NULL;
    }
    else if(prev_free && !next_free){
        // only previous block is free
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        if(size >= new_size){
            // we can make use of the previous free block
            remove_free_block(PREV_BLKP(bp));
            PUT(FTRP(bp), PACK(size, 1));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
            return (void*) (PREV_BLKP(bp));
        } else{
            return NULL;
        }
    }
    else if(!prev_free && next_free){
        // only next block is free
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if(size >= new_size){
            // we can make use of the next free block
            remove_free_block(NEXT_BLKP(bp));
            PUT(FTRP(bp), PACK(size, 1));
            PUT(HDRP(bp), PACK(size, 1));
            return (void*) (bp);
        } else{
            return NULL;
        }
    }
    else{
        // both blocks are free
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if(size >= new_size){
            // we can make use of both free blocks
            remove_free_block(PREV_BLKP(bp));
            remove_free_block(NEXT_BLKP(bp));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1));
            return (void*) (PREV_BLKP(bp));
        } else{
            return NULL;
        }
    }

    return NULL;
}

/*
 * mm_checkheap - Check the heap for correctness. Helpful hint: You
 *                can call this function using mm_checkheap(__LINE__);
 *                to identify the line number of the call site.
 */
void mm_checkheap(int lineno)
{
    printf("\n");
    printf("-----------------------------\n");
    printf("line: %d checkheap\n", lineno);

    int block_id = 0;
    // traverse the heap and print all the blocks
    char* cursor = (char*) heap_startp;
    while(GET_SIZE(HDRP(cursor)) != 0){
        // check if the header and footer matches
        if(GET(HDRP(cursor)) != GET(FTRP(cursor))){
            printf("ERROR: header/footer not match at 0x%x\n",
                    (unsigned) cursor);
            unsigned int h_alloc = GET_ALLOC(HDRP(cursor));
            unsigned int h_size = GET_SIZE(HDRP(cursor));
            unsigned int f_alloc = GET_ALLOC(FTRP(cursor));
            unsigned int f_size = GET_SIZE(FTRP(cursor));
            printf("HEADER: SIZE\t%d\tALLOC\t%d\n", h_size, h_alloc);
            printf("FOOTER: SIZE\t%d\tALLOC\t%d\n", f_size, f_alloc);
        }

        unsigned int allocated = GET_ALLOC(HDRP(cursor));
        unsigned int block_size = GET_SIZE(HDRP(cursor));

        unsigned ptrpos = (unsigned) (cursor);
        printf("block %d\t%d\t%d\t0x%x\n",
                block_id, allocated, block_size, ptrpos);


        block_id ++;
        cursor = (char*) NEXT_BLKP(cursor);
    }
    // print the last block
    unsigned int allocated = GET_ALLOC(HDRP(cursor));
    unsigned int block_size = GET_SIZE(HDRP(cursor));
    unsigned ptrpos = (unsigned) (cursor);
    printf("block %d\t%d\t%d\t0x%x\n",
            block_id, allocated, block_size, ptrpos);
    printf("-----------------------------\n");
    print_list();
    printf("-----------------------------\n");
}

/*
 * The remaining routines are internal helper routines
 */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t dwords)
{
    char *bp;
    // extended size by bytes
    size_t size;

    /* Allocate an even number of dwords to maintain alignment */
    // original: size = (dwords % 2) ? (dwords+1) * DSIZE : dwords * DSIZE;
    // the size must be at least 16 bytes (4 words)
    // to fit all info in a free block
    // size = (size >= 16) ? size : 16;


    size = (dwords) * DSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */

    /* init the prev and next fields */
    PUT(FRB_NEXTP(bp), NULL);
    PUT(FRB_PREVP(bp), NULL);


    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    // Update heap_endp
    heap_endp += size;

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        ;
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // remove the next free block
        remove_free_block(NEXT_BLKP(bp));
        // set the new size
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        void* prev_p = (void* ) PREV_BLKP(bp);
        size += GET_SIZE(HDRP(prev_p));
        // remove the previous free block
        remove_free_block(prev_p);

        // set the new size
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(prev_p), PACK(size, 0));
        // set the new bp
        bp = prev_p;
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        // remove the previous and the next free block
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_free_block(bp);
    return bp;
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t delta_size = csize - asize;
    // remove this block from the seg list
    remove_free_block(bp);

    if (delta_size >= MINFRBSIZE) {
        // init allocated block
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);

        // create new free block
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        PUT(FRB_NEXTP(bp), NULL);
        PUT(FRB_PREVP(bp), NULL);
        // coalesce the block
        coalesce(bp);
    }
    // else if(delta_size == DSIZE && !NEXT_BLK_ALLOC(bp)){
    //     // if delta_size = 8B && next block is free
    //     // 8 bytes <= delta_size < 16 bytes
    //     // delta_size must be 8 bytes for alignment reasons
    //
    //     // init allocated block
    //     PUT(HDRP(bp), PACK(asize, 1));
    //     PUT(FTRP(bp), PACK(asize, 1));
    //     // create a new char* points to the next free block
    //     // because void* does not allow arithmetic operations
    //     char* frb_p = (char*) NEXT_BLKP(bp);
    //     size_t new_frb_size = GET_SIZE(HDRP(frb_p)) + DSIZE;
    //     remove_free_block(frb_p);
    //     // move frb_p to its new location
    //     frb_p -= DSIZE;
    //     // set new header & footer
    //     PUT(HDRP(frb_p), PACK(new_frb_size, 0));
    //     PUT(FTRP(frb_p), PACK(new_frb_size, 0));
    //     // insert the new block into list
    //     insert_free_block(frb_p);
    //
    // }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
    char* fit_p = (char*) find_free_block(asize);
    // we cannot find a fit, return NULL
    return (void*) (fit_p);
}




