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
 
 /* Explicit free list macros - works for both 32-bit and 64-bit */
 #define GET_PREV_FREE(bp) (*(void **)(bp))
 #define GET_NEXT_FREE(bp) (*(void **)((char *)(bp) + sizeof(void *)))
 #define SET_PREV_FREE(bp, ptr) (*(void **)(bp) = (ptr))
 #define SET_NEXT_FREE(bp, ptr) (*(void **)((char *)(bp) + sizeof(void *)) = (ptr))
 
 /* Minimum block size: header + prev_ptr + next_ptr + footer, aligned */
 #define MIN_BLOCK_SIZE (ALIGN(DSIZE + 2 * sizeof(void *)))
 
 /* Rounds up to the nearest multiple of ALIGNMENT */
 #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
 
 /* Global variables */
 static void *heap_listp = NULL;    /* Pointer to first block */
 static void *free_listp = NULL;    /* Pointer to first free block */
 
 /* Function prototypes */
 static void *extend_heap(size_t words);
 static void *coalesce(void *bp);
 static void *find_fit(size_t asize);
 static void place(void *bp, size_t asize);
 static void add_to_free_list(void *bp);
 static void remove_from_free_list(void *bp);
 
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
     free_listp = NULL;           /* Empty free list initially */
     
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
     size_t newsize;
     
     if (size <= DSIZE)
         newsize = MIN_BLOCK_SIZE;
     else
         newsize = ALIGN(size + DSIZE);
     
     /* If new size is smaller or equal, return same pointer */
     if (newsize <= oldsize)
         return ptr;
     
     /* Allocate new block */
     void *newptr = mm_malloc(size);
     if (newptr == NULL)
         return NULL;
     
     /* Copy old data */
     size_t copySize = oldsize - DSIZE;  /* Exclude header and footer */
     if (size < copySize)
         copySize = size;
     memcpy(newptr, ptr, copySize);
     
     /* Free old block */
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
         size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
         bp = PREV_BLKP(bp);
         add_to_free_list(bp);
     }
     
     return bp;
 }
 
 /*
  * find_fit - Find a fit for a block with asize bytes (First-fit search)
  */
 static void *find_fit(size_t asize) {
     void *bp;
     
     /* First-fit search */
     for (bp = free_listp; bp != NULL; bp = GET_NEXT_FREE(bp)) {
         if (GET_SIZE(HDRP(bp)) >= asize) {
             return bp;
         }
     }
     
     return NULL;  /* No fit found */
 }
 
 /*
  * place - Place block of asize bytes at start of free block bp
  *         Split if remainder would be at least minimum block size
  */
 static void place(void *bp, size_t asize) {
     size_t csize = GET_SIZE(HDRP(bp));
     
     /* Remove from free list first */
     remove_from_free_list(bp);
     
     if ((csize - asize) >= MIN_BLOCK_SIZE) {
         /* Split the block */
         PUT(HDRP(bp), PACK(asize, 1));
         PUT(FTRP(bp), PACK(asize, 1));
         
         void *next_bp = NEXT_BLKP(bp);
         PUT(HDRP(next_bp), PACK(csize - asize, 0));
         PUT(FTRP(next_bp), PACK(csize - asize, 0));
         
         /* Add remainder to free list */
         add_to_free_list(next_bp);
     } else {
         /* Use entire block */
         PUT(HDRP(bp), PACK(csize, 1));
         PUT(FTRP(bp), PACK(csize, 1));
     }
 }
 
 // 주소순 정렬 + 인접 free 병합(coalesce) 삽입
static void add_to_free_list(void *bp) {
    if (!bp) return;

    // 현재 bp는 헤더/푸터에 size|alloc비트가 이미 0으로 세팅되어 있다고 가정
    size_t size = GET_SIZE(HDRP(bp));

    // (1) 주소순 위치 탐색
    void *prev = NULL;
    void *current = free_listp;
    while (current && current < bp) {
        prev = current;
        current = GET_NEXT_FREE(current);
    }
    // now: prev < bp <= current (주소 기준)

    // (2) 좌/우 물리 이웃과 병합 시도
    // prev와 인접?
    if (prev && ((char *)prev + GET_SIZE(HDRP(prev)) == (char *)bp)) {
        // prev를 리스트에서 제거 후 병합
        void *prev_prev = GET_PREV_FREE(prev); // 삽입 재구성을 위해 저장
        remove_from_free_list(prev);

        size += GET_SIZE(HDRP(prev));
        bp = prev; // 병합 시 시작 주소는 prev로 이동

        // 병합된 새 prev 후보는 prev_prev (주소상 더 작은 쪽)
        prev = prev_prev;
    }

    // current와 인접?
    if (current && ((char *)bp + size == (char *)current)) {
        // current를 리스트에서 제거 후 병합
        void *current_next = GET_NEXT_FREE(current); // 이후 이어줄 대상
        remove_from_free_list(current);

        size += GET_SIZE(HDRP(current));
        current = current_next; // 오른쪽 이웃 다음 노드로 당겨옴
    }

    // (3) 병합 결과를 헤더/푸터에 반영
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // (4) 최종 블록을 주소순으로 prev와 current 사이에 삽입
    if (prev == NULL) {
        // head 삽입
        SET_PREV_FREE(bp, NULL);
        SET_NEXT_FREE(bp, current);
        if (current) SET_PREV_FREE(current, bp);
        free_listp = bp;
    } else {
        // 중간/꼬리 삽입
        SET_NEXT_FREE(bp, current);
        SET_PREV_FREE(bp, prev);
        SET_NEXT_FREE(prev, bp);
        if (current) SET_PREV_FREE(current, bp);
    }
}
 
 /*
  * remove_from_free_list - Remove block from free list
  */
 static void remove_from_free_list(void *bp) {
     if (bp == NULL)
         return;
     
     void *prev = GET_PREV_FREE(bp);
     void *next = GET_NEXT_FREE(bp);
     
     if (prev == NULL)
         free_listp = next;
     else
         SET_NEXT_FREE(prev, next);
     
     if (next != NULL)
         SET_PREV_FREE(next, prev);
 }