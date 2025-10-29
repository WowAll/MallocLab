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

typedef unsigned int offset_t;

#define WSIZE 4                          /* Word size in bytes */
#define DSIZE 8                          /* Double word size */
#define CHUNKSIZE (1 << 12)              /* Extend heap by this amount */
#define ALIGNMENT 8                      /* Alignment requirement */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* 블록의 헤더와 푸터를 설정하는 매크로 */
#define PACK(size, alloc) ((size) | (alloc))

/* 4바이트를 읽고 쓰는 매크로 */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* 주소값 p 블록의 크기와 할당 상태를 읽는 매크로 */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* 주소값 bp 블록의 헤더와 푸터의 주소값을 찾아주는 매크로 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 주소값 bp 블록의 다음 블록과 이전 블록의 주소를 찾아주는 매크로 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* NULL_OFFSET는 모든 비트가 1로 설정된 4바이트 값을 나타내며, 이는 메모리 할당 실패를 나타내는 데 사용된다. */
#define NULL_OFFSET 0xFFFFFFFF

/* 주소값 bp를 힙 시작 주소값에서부터 오프셋을 찾아주는 매크로*/
#define PTR_TO_OFFSET(bp) ((bp) ? ((offset_t)((char *)(bp) - (char *)heap_listp)) : NULL_OFFSET)

/* 오프셋을 주소값으로 변환하는 매크로 */
#define OFFSET_TO_PTR(offset) ((offset == NULL_OFFSET) ? NULL : (void *)((char *)heap_listp + offset))

/* 이전 Free 블록의 오프셋을 읽는 매크로 */
#define GET_PREV_FREE(bp) (*((offset_t *)(bp)))
/* 다음 Free 블록의 오프셋을 읽는 매크로 */
#define GET_NEXT_FREE(bp) (*((offset_t *)((char *)(bp) + sizeof(offset_t))))
/* 이전 Free 블록의 오프셋을 설정하는 매크로 */
#define SET_PREV_FREE(bp, ptr) (*((offset_t *)(bp)) = PTR_TO_OFFSET(ptr))
/* 다음 Free 블록의 오프셋을 설정하는 매크로 */
#define SET_NEXT_FREE(bp, ptr) (*((offset_t *)((char *)(bp) + sizeof(offset_t))) = PTR_TO_OFFSET(ptr))

/* 메모리 블록의 최소 크기 = 8 + 2 * 4 = 16바이트 */
#define MIN_BLOCK_SIZE (ALIGN(DSIZE + 2 * sizeof(offset_t)))

/* 주어진 크기를 ALIGNMENT의 배수로 올림하는 매크로 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* 전역 변수 */
static void *heap_listp = NULL;    /* 힙 리스트의 첫 번째 블록을 가리키는 포인터 */
static offset_t free_list_offset = NULL_OFFSET;  /* 첫 번째 Free 블록의 오프셋 */

/* 함수 프로토타입 */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void add_to_free_list(void *bp);
static void remove_from_free_list(void *bp);
static void split_block(void *bp, size_t asize);

/*
 * mm_init - 메모리 관리 패키지를 초기화하는 함수
 */
int mm_init(void) {
    /* 초기 빈 힙을 생성 */
    /* 정렬 패딩과 프로로그, 애플로그를 위해 4바이트를 할당 */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    
    PUT(heap_listp, 0);                                      /* 정렬 패딩 */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));          /* 프로로그 헤더 */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));          /* 프로로그 푸터 */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));              /* 애플로그 헤더 */
    
    /* Initialize pointers */
    heap_listp += (2 * WSIZE);  /* 프로로그 푸터를 가리키는 포인터 */
    free_list_offset = NULL_OFFSET;  /* 빈 Free 리스트 초기화 */
    
    /* 빈 힙을 확장하여 Free 블록을 추가 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    
    return 0;
}

/*
 * mm_malloc - 최소 size 바이트의 페이로드를 가진 블록을 할당하는 함수
 */
void *mm_malloc(size_t size) {
    size_t asize;        /* 조정된 블록 크기 */
    size_t extendsize;   /* 힙을 확장할 크기 */
    void *bp;
    
    /* 0바이트 요청을 무시 */
    if (size == 0)
        return NULL;
    
    /* 오버헤드와 정렬을 포함하여 블록 크기를 조정 */
    if (size <= DSIZE)
        asize = MIN_BLOCK_SIZE;
    else
        asize = ALIGN(size + DSIZE);  /* 헤더와 푸터를 위해 공간을 추가 */
    
    /* Free 리스트에서 적합한 블록을 찾음 */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }
    
    /* 적합한 블록을 찾지 못했습니다. 더 많은 메모리를 가져와서 블록을 배치 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    
    place(bp, asize);
    return bp;
}

/*
 * mm_free - 블록을 해제하는 함수
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
 * mm_realloc - 블록을 재할당하는 함수
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
    
    /* 같은 사이즈면 그대로 반환 */
    if (newsize == oldsize)
        return ptr;

    /* Case 1: 블록 축소의 경우 축소된 크기만큼 메모리를 해제하지만 만약 남은 메모리가 최소 블록 크기보다 작으면 해제하지 않는다. */
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

    /* Case 2: 블록 확장의 경우 확장된 크기만큼 메모리를 할당하지만 만약 남은 메모리가 최소 블록 크기보다 작으면 할당하지 않는다. */
    void *next = NEXT_BLKP(ptr);
    void *prev = PREV_BLKP(ptr);
    int prev_free = !GET_ALLOC(HDRP(prev));
    int next_free = !GET_ALLOC(HDRP(next));

    /* Case 2-1: 다음 블록을 먼저 시도 (memmove 필요 없음) */
    if (next_free) {
        size_t nsize = GET_SIZE(HDRP(next));
        size_t total = oldsize + nsize;

        if (total >= newsize) {
            remove_from_free_list(next);
            if (total - newsize < MIN_BLOCK_SIZE)
                newsize = total;
            
            /* split_block 함수를 사용하여 할당 처리 */
            PUT(HDRP(ptr), PACK(total, 0));
            split_block(ptr, newsize);
            
            return ptr;
        }
    }

    /* Case 2-2: 이전 블록과/또는 다음 블록을 병합하여 시도 */
    if (prev_free) {
        size_t psize = prev_free ? GET_SIZE(HDRP(prev)) : 0;
        size_t nsize = next_free ? GET_SIZE(HDRP(next)) : 0;
        size_t total = psize + oldsize + nsize;

        if (total >= newsize) {
            /* 만약 이전 블록이 할당되어 있지 않다면 이전 블록을 시작 블록으로 설정 */
            void *start = prev_free ? prev : ptr;

            /* 이전 블록과 다음 블록이 할당되어 있지 않다면 Free 리스트에서 제거 */
            if (prev_free)
                remove_from_free_list(prev);
            if (next_free)
                remove_from_free_list(next);

            /* 만약 이전 블록이 시작 블록으로 설정되어 있다면 데이터를 이전 블록으로 이동 */
            if (start == prev) {
                size_t payload = oldsize - DSIZE;
                memmove(prev, ptr, payload);
            }

            /* split_block 함수를 사용하여 할당 처리 */
            PUT(HDRP(start), PACK(total, 0));
            split_block(start, newsize);
            
            return start;
        }
    }

    /* Case 3: 확장할 수 없음 - 새로운 블록을 할당 */
    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    /* 이전 블록과 새로운 블록 중 작은 크기만큼 데이터를 복사 */
    size_t copySize = oldsize - DSIZE;  /* 페이로드 크기 */
    if (size < copySize)
        copySize = size;
    memcpy(newptr, ptr, copySize);

    mm_free(ptr);
    return newptr;
}

/*
 * extend_heap - Free 블록을 추가하여 힙을 확장하고 블록 포인터를 반환하는 함수
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    
    /* 정렬을 유지하기 위해 짝수 개의 바이트를 할당 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    
    /* 최소 블록 크기를 보장 */
    if (size < MIN_BLOCK_SIZE)
        size = MIN_BLOCK_SIZE;
    
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Free 블록 헤더와 푸터, 애플로그 헤더를 초기화 */
    PUT(HDRP(bp), PACK(size, 0));           /* Free 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));           /* Free 블록 푸터 */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  /* 새로운 애플로그 헤더 */
    
    /* 이전 블록이 Free 블록이면 병합 */
    return coalesce(bp);
}

/*
 * coalesce - 인접한 Free 블록을 병합하는 함수
*/
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) {            /* Case 1: 양 쪽 모두 할당된 블록 */
        add_to_free_list(bp);
        return bp;
    }
    
    else if (prev_alloc && !next_alloc) {      /* Case 2: 다음 블록이 Free 블록인 경우 */
        remove_from_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        add_to_free_list(bp);
    }
    
    else if (!prev_alloc && next_alloc) {      /* Case 3: 이전 블록이 Free 블록인 경우 */
        remove_from_free_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        add_to_free_list(bp);
    }
    
    else {                                     /* Case 4: 양 쪽 모두 Free 블록인 경우 */
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
 * find_fit - asize 바이트의 블록을 찾는 함수
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
            if (best_size == asize)
                break;
        }
        offset_t next_offset = GET_NEXT_FREE(bp);
        bp = OFFSET_TO_PTR(next_offset);
    }
    return best_bp;
}
 
/*
 * split_block - asize 바이트의 블록을 할당하고 남은 블록을 Free 리스트에 추가하는 함수
 *               place()와 realloc()에서 호출된다.
 */
static void split_block(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= MIN_BLOCK_SIZE) {
        /* 블록을 분할 */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        
        void *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
        
        /* 남은 블록을 Free 리스트에 추가 */
        coalesce(next_bp);
    } else {
        /* 블록을 할당 */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * place - asize 바이트의 블록을 Free 블록 bp의 시작 부분에 배치하는 함수
 *         남은 블록이 최소 블록 크기보다 크면 분할한다.
 */
static void place(void *bp, size_t asize) {
    /* Free 리스트에서 제거 */
    remove_from_free_list(bp);
    
    /* split_block 함수를 사용하여 할당 처리 */
    split_block(bp, asize);
}
 
/*
 * add_to_free_list - Free 리스트에 블록을 추가하는 함수
 */
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
 * remove_from_free_list - Free 리스트에서 블록을 제거하는 함수
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