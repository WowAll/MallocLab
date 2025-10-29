#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "firstteam",
    "Yoonbeom Cho",
    "whdbsqja1@gmail.com",
    "",
    ""
};

#define WSIZE 4                          /* Word size in bytes */
#define DSIZE 8                          /* Double word size */
#define CHUNKSIZE (1 << 12)              /* Extend heap by this amount */
#define ALIGNMENT 8                      /* Alignment requirement */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read size and allocated field from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Offset-based free list to save space (8 bytes -> 4 bytes per pointer) */
/* Offset from heap start stored as unsigned int */
typedef unsigned int offset_t;
#define OFFSET_MASK 0x7fffffff
#define NULL_OFFSET 0x7fffffff

/* Convert pointer to offset from heap start */
#define PTR_TO_OFFSET(bp) ((bp) ? ((offset_t)((char *)(bp) - (char *)heap_start)) & OFFSET_MASK : NULL_OFFSET)

/* Convert offset to pointer */
#define OFFSET_TO_PTR(offset) ((offset == NULL_OFFSET) ? NULL : (void *)((char *)heap_start + offset))

/* Free list macros using offsets */
/* GET returns offset_t, SET takes pointer */
#define GET_PREV_FREE(bp) (*((offset_t *)(bp)))
#define GET_NEXT_FREE(bp) (*((offset_t *)((char *)(bp) + sizeof(offset_t))))
#define SET_PREV_FREE(bp, ptr) (*((offset_t *)(bp)) = PTR_TO_OFFSET(ptr))
#define SET_NEXT_FREE(bp, ptr) (*((offset_t *)((char *)(bp) + sizeof(offset_t))) = PTR_TO_OFFSET(ptr))

/* Minimum block size: header + prev_offset + next_offset + footer, aligned */
#define MIN_BLOCK_SIZE (ALIGN(DSIZE + 2 * sizeof(offset_t)))

/* Rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* Global variables */
static void *heap_listp = NULL;    /* Pointer to first block */
static void *heap_start = NULL;   /* Starting address of heap */
static offset_t free_list_offset = NULL_OFFSET;  /* Offset to first free block */

/* Function prototypes */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void add_to_free_list(void *bp);
static void remove_from_free_list(void *bp);
static void split_block(void *bp, size_t asize);

/*
 * mm_init - Initialize the malloc package.
 */
int mm_init(void) {
    /* Create initial empty heap */
    /* Allocate 4 words for alignment padding and prologue, plus epilogue */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    
    PUT(heap_listp, 0);                                      /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));          /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));          /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));              /* Epilogue header */
    
    /* Initialize pointers */
    heap_listp += (2 * WSIZE);  /* Point to prologue footer */
    heap_start = heap_listp;     /* Store heap start for offset calculations */
    free_list_offset = NULL_OFFSET;  /* Empty free list initially */
    
    /* Extend the empty heap with a free block */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    
    return 0;
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size) {
    size_t asize;        /* Adjusted block size */
    size_t extendsize;   /* Amount to extend heap if no fit */
    void *bp;
    
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment */
    if (size <= DSIZE)
        asize = MIN_BLOCK_SIZE;
    else
        asize = ALIGN(size + DSIZE);  /* Add space for header and footer */
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Free a block
 */
void mm_free(void *bp) {
    if (bp == NULL)
        return;
    
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Reallocate a block
 */
void *mm_realloc(void *ptr, size_t size) {
    if (ptr == NULL)
        return mm_malloc(size);
    
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    
    size_t oldsize = GET_SIZE(HDRP(ptr));
    size_t newsize = (size <= DSIZE) ? MIN_BLOCK_SIZE : ALIGN(size + DSIZE);
    
    /* If new size is the same, return same pointer */
    if (newsize == oldsize)
        return ptr;

    /* Case 1: Shrinking the block */
    if (newsize < oldsize) {
        size_t remain = oldsize - newsize;
        if (remain >= MIN_BLOCK_SIZE) {
            PUT(HDRP(ptr), PACK(newsize, 1));
            PUT(FTRP(ptr), PACK(newsize, 1));

            void *tail = NEXT_BLKP(ptr);
            PUT(HDRP(tail), PACK(remain, 0));
            PUT(FTRP(tail), PACK(remain, 0));

            coalesce(tail);
        }
        return ptr;
    }

    /* Case 2: Expanding - try to extend in place */
    void *next = NEXT_BLKP(ptr);
    void *prev = PREV_BLKP(ptr);
    int prev_free = !GET_ALLOC(HDRP(prev));
    int next_free = !GET_ALLOC(HDRP(next));

    /* Case 2-1: Try next block first (no memmove needed) */
    if (next_free) {
        size_t nsize = GET_SIZE(HDRP(next));
        size_t total = oldsize + nsize;

        if (total >= newsize) {
            remove_from_free_list(next);
            if (total - newsize < MIN_BLOCK_SIZE)
                newsize = total;
            
            /* Use split_block helper to handle allocation */
            PUT(HDRP(ptr), PACK(total, 0));
            split_block(ptr, newsize);
            
            return ptr;
        }
    }

    /* Case 2-2: Try merging with prev and/or next */
    if (prev_free || next_free) {
        size_t psize = prev_free ? GET_SIZE(HDRP(prev)) : 0;
        size_t nsize = next_free ? GET_SIZE(HDRP(next)) : 0;
        size_t total = psize + oldsize + nsize;

        if (total >= newsize) {
            /* Merge blocks - might need to move data left */
            void *start = prev_free ? prev : ptr;

            /* Remove neighbors from free list */
            if (prev_free)
                remove_from_free_list(prev);
            if (next_free)
                remove_from_free_list(next);

            /* Move data if expanding left */
            if (start == prev) {
                size_t payload = oldsize - DSIZE;
                memmove(prev, ptr, payload);
            }

            /* Use split_block helper to handle allocation */
            PUT(HDRP(start), PACK(total, 0));
            split_block(start, newsize);
            
            return start;
        }
    }

    /* Case 3: Can't extend in place - allocate new block */
    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    /* Copy minimum of old and new sizes */
    size_t copySize = oldsize - DSIZE;  /* payload size */
    if (size < copySize)
        copySize = size;
    memcpy(newptr, ptr, copySize);

    mm_free(ptr);
    return newptr;
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    
    /* Ensure minimum block size */
    if (size < MIN_BLOCK_SIZE)
        size = MIN_BLOCK_SIZE;
    
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  /* New epilogue header */
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * coalesce - Merge adjacent free blocks
*/
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) {            /* Case 1: Both allocated */
        add_to_free_list(bp);
        return bp;
    }
    
    else if (prev_alloc && !next_alloc) {      /* Case 2: Next is free */
        remove_from_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        add_to_free_list(bp);
    }
    
    else if (!prev_alloc && next_alloc) {      /* Case 3: Prev is free */
        remove_from_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        add_to_free_list(bp);
    }
    
    else {                                     /* Case 4: Both free */
        remove_from_free_list(PREV_BLKP(bp));
        remove_from_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        add_to_free_list(bp);
    }
    
    return bp;
}
 
/*
 * find_fit - Find a fit for a block with asize bytes (Best-fit search)
 */
static void *find_fit(size_t asize) {
    void *bp;

    void *best_bp = NULL;
    size_t best_size;
     
    /* Best-fit search */
    bp = OFFSET_TO_PTR(free_list_offset);
    while (bp != NULL) {
        if ((best_bp == NULL || GET_SIZE(HDRP(bp)) < best_size) && GET_SIZE(HDRP(bp)) >= asize) {
            best_bp = bp;
            best_size = GET_SIZE(HDRP(bp));
        }
        offset_t next_offset = GET_NEXT_FREE(bp);
        bp = OFFSET_TO_PTR(next_offset);
    }
    return best_bp;
}
 
/*
 * split_block - Split a block into allocated block of asize and free remainder
 *               Called by place() and realloc()
 */
static void split_block(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= MIN_BLOCK_SIZE) {
        /* Split the block */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
        
        /* Add remainder to free list */
        coalesce(next_bp);
    } else {
        /* Use entire block */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * place - Place block of asize bytes at start of free block bp
 *         Split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize) {
    /* Remove from free list first */
    remove_from_free_list(bp);
    
    /* Use split_block helper to handle allocation */
    split_block(bp, asize);
}
 
static void add_to_free_list(void *bp) {
    if (bp == NULL)
       return;
    
    void *first = OFFSET_TO_PTR(free_list_offset);
    
    SET_NEXT_FREE(bp, first);
    SET_PREV_FREE(bp, NULL);
    
    if (first != NULL)
       SET_PREV_FREE(first, bp);
    
    free_list_offset = PTR_TO_OFFSET(bp);
}

/*
 * remove_from_free_list - Remove block from free list
 */
static void remove_from_free_list(void *bp) {
    if (bp == NULL)
        return;
    
    offset_t prev_offset = GET_PREV_FREE(bp);
    offset_t next_offset = GET_NEXT_FREE(bp);
    
    void *prev = OFFSET_TO_PTR(prev_offset);
    void *next = OFFSET_TO_PTR(next_offset);
    
    if (prev_offset == NULL_OFFSET)
        free_list_offset = next_offset;
    else
        SET_NEXT_FREE(prev, next);
    
    if (next_offset != NULL_OFFSET)
        SET_PREV_FREE(next, prev);
}