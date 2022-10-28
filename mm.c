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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    "team7",
    "Suyeon Woo",
    "woosean999@gmail.com",
    "Rigyeong Hong",
    "ghdflrud96@gmail.com",
    "Jinseob Kim",
    "jinseob.kim91@gmail.com",
};

/* single word (4) or double word (8) alignment */

#define WSIZE 4                 // 워드, 헤더/푸터 사이즈(바이트)
#define DSIZE WSIZE * 2         // 더블 워드 사이즈(바이트)
#define ALIGNMENT DSIZE         // 더블 워드 얼라인 사용하기 위해 얼라인먼트 사이즈를 더블로 정의
#define CHUNKSIZE (1<<12)       // 한번에 늘릴 힙사이즈 (바이트)

/* rounds up to the nearest multiple of ALIGNMENT */

#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 매크로 함수 */

#define MAX(x, y) (x > y ? x : y)
#define PACK(size, alloc) (size | alloc)

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = val)

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* 
 * mm_init - initialize the malloc package.
 */

static void *extend_heap(size_t words);

static char *heap_listp = 0;  //첫번째 블록 영역의 포인터 

int mm_init(void)
{
    // 최초 힙 생성
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) //line:vm:mm:begininit
	    return -1;
    PUT(heap_listp, 0);                          // 얼라인먼트 패딩
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     // 에필로그 헤더
    heap_listp += (2*WSIZE);                     

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
	    return -1;
    return 0;
}

/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    // 더블 얼라인을 위해 짝수 홀수 분기 
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)  
	    return NULL;                                    

    // 가용 블록 헤더, 푸터, 에필로그 헤더 초기화
    PUT(HDRP(bp), PACK(size, 0));         // 헤더
    PUT(FTRP(bp), PACK(size, 0));         // 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 헤더

    // 이전 블록이 free라면 인접블록(이전 & 현재) 연결
    return coalesce(bp);                                         
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














