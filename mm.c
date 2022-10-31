/*
*mm.c
 *
 * - Explicit free list based malloc package with first fit / next fit placing and real time coalescing.
 *
 * 명시적 가용리스트를 이중 연결 포인터로 구현.
 * next fit 각각으로 배치장소를 찾는다. 
 * free 후 즉시연결을 수행한다.
 *
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
    "Jinseob Kim",
    "jinseob.kim91@gmail.com",
};

#define WSIZE 4
#define DSIZE 8
#define MINIMUM 16      // 헤더, 푸터, PREV, NEXT
#define CHUNKSIZE (1<<12)

#define ALIGNMENT DSIZE
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MAX(x, y) ((x) > (y) ? (x) : (y))  // 최댓값 구하는 함수 매크로

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p)          (*(unsigned int*)(p))
#define PUT(p, val)     (*(unsigned int*)(p) = (val))

#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* 블록 포인터 bp를 인자로 받아 블록의 header와 footer의 주소를 반환한다 */
#define HDRP(bp)    ((char*)(bp) - WSIZE) 
#define FTRP(bp)    ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 인접 앞, 인접 뒤
#define SUCC_BLKP(bp)   ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) 
#define PREC_BLKP(bp)   ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) 

/* Free List 상에서의 이전, 이후 블록의 포인터. */
#define PREV_FREEP(bp)  (*(void**)(bp))  
#define NEXT_FREEP(bp)  (*(void**)(bp + WSIZE))

#define SET_PREV_FREE(bp, prev) (*((void **)(bp)) = prev) /* Given block pointers ptr and prev, set the PREV pointer of ptr to *prev. */
#define SET_NEXT_FREE(bp, next) (*((void **)(bp + WSIZE)) = next) /* Given block pointers ptr and next, set the NEXT pointer of ptr to next*/


/* free 블록은 이중연결리스트로 관리하며 prev, next 가 있지만 allocated 블록에는 헤더와 푸터만 있다.*/
static char *heap_listp = NULL; // 힙의 프롤로그 블록을 가리키는 정적변수 포인터
static char *free_listp = NULL; // free list 의 첫 블록을 가리키는 정적변수 포인터

// #define INSERT_LIFO

// #define NEXT_FIT

#ifdef NEXT_FIT
    static char *last_bp;
#endif


static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t newsize);
static void insert_node(void* bp);
static void delete_node(void *bp);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* 미사용 패딩, 프롤로그 블록 헤더, 프롤로그 블록 PREV, 프롤로그 블록 NEXT, 프롤로그 블록 푸터,에필로그 푸터 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1)
        return -1;

    // 포인터 위치 지정
    PUT(heap_listp, 0);                             // unused
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1));  // prologue header => 초기화 과정에서 생성한다. 얼라인 포맷을 위해 사용하고 실제 메모리공간을 사용하지는 않는다.
    // PUT(heap_listp + (2*WSIZE), NULL);              // prologue block PREV =  NULL
    // PUT(heap_listp + (3*WSIZE), NULL);              // prologue block NEXT =  NULL
    // => TODO: 메모리 낭비 
    PUT(heap_listp + (2*WSIZE), PACK(MINIMUM, 1));  // prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // epliogue header

    heap_listp += + 2*WSIZE; // free_listp를 탐색의 시작점으로 둔다. 
    free_listp = NULL;
#ifdef NEXT_FIT
    last_bp = heap_listp;
#endif

    // 초기 가용블록 생성 
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) //실패하면 -1 리턴
        return -1;

    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;       // 새로 계산할 사이즈
    size_t extendsize;  // 힙 영역에서 늘려줄 사이즈
    char* bp;

    // 가짜 요청(spurious request) 처리
    if (size == 0)
        return NULL;

    // 요청 사이즈에 header와 footer를 위한 double words 공간(SIZE_T_SIZE)을 추가한 후 align해준다.
    // free 블록에는 prev, next 가 있지만 allocated 블록은 이중연결리스트로 관리되지 않으므로 헤더와 푸터공간만 만들어준다.
    asize = ALIGN(size + SIZE_T_SIZE);  

    // 할당할 가용 리스트를 찾는다.
    if ((bp = find_fit(asize)) != NULL){  
        place(bp, asize);  // place에서는 필요한 공간만 분할해서 써준다.
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);  // 둘 중 더 큰 값으로 사이즈를 정한다.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) 
        return NULL;
    place(bp, asize);
    return bp;
}

static void* find_fit(size_t asize){

#ifdef NEXT_FIT
    /* Next-fit */
    char *old_bp = last_bp;

    /* 초기화는 보통 평가문에서 참조할 변수가 없을까봐 넣어주는데, 만약에 전역으로 선언해둔 게 있다면 평가문에서 그걸 참조할 것이므로 첫번째부분을 생략하고 세미콜론만 넣어주면 된다.*/
    
    /* 로버(현재 힙 마지막)부터 힙 끝까지 서치한다 */
    for ( ; GET_SIZE(HDRP(last_bp)) > 0; last_bp = SUCC_BLKP(last_bp))
	if (!GET_ALLOC(HDRP(last_bp)) && (asize <= GET_SIZE(HDRP(last_bp))))
	    return last_bp;

    /* NEXT FIT SEARCH가 실패하면 다시 힙 앞부터 기존 로버 앞까지 탐색한다 */
    for (last_bp = heap_listp; last_bp < old_bp; last_bp = SUCC_BLKP(last_bp))
	if (!GET_ALLOC(HDRP(last_bp)) && (asize <= GET_SIZE(HDRP(last_bp))))
	    return last_bp;  // 로버는 마지막으로 탐색한 블록의 포인터이다. (last bp)

    return NULL;  /* no fit found */
#else
    /* First-fit */
    void* bp;

    for (bp = free_listp; bp != NULL && GET_ALLOC(HDRP(bp)) != 1; bp = NEXT_FREEP(bp)){
        if(asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }

    // 못 찾으면 NULL을 리턴한다.
    return NULL;
#endif
}

/*
    place(bp, size)
    : 요구 메모리를 할당할 수 있는 가용 블록을 할당한다. 이 때 분할이 가능하면 분할한다.
*/
static void place(void* bp, size_t asize){
    // 현재 할당할 수 있는 후보 가용 블록의 주소
    size_t csize = GET_SIZE(HDRP(bp));

    // 할당될 블록이므로 free list에서 없애준다.
    delete_node(bp);

    // 분할이 가능한 경우
    if ((csize - asize) >= (2*DSIZE)){
        // 앞의 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 뒤의 블록은 가용 블록으로 분할한다.
        bp = SUCC_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        // free list 에 분할된 블럭을 넣는다.
        insert_node(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
    extend_heap : 워드 단위 메모리를 인자로 받아 힙을 늘려준다.
*/
static void* extend_heap(size_t words){ // 워드 단위로 받는다.
    char* bp;
    size_t size;
    
    // 더블워드 정렬. 필요한 바이트를 8의 배수(2words)로 맞춰서 (1word * 2 = 2words. 1word = 4byte.) 할당받는다.
    size = (words % 2) ? (words + 1) * WSIZE : (words) * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1) // 새 메모리의 첫 부분을 bp로 둔다. 
        return NULL;
    
    /* 새 가용 블록의 header와 footer를 정해주고 epilogue block을 가용 블록 맨 끝으로 옮긴다. */
    PUT(HDRP(bp), PACK(size, 0));  // 헤더. 할당 안 해줬으므로 0으로.
    PUT(FTRP(bp), PACK(size, 0));  // 풋터.
    PUT(HDRP(SUCC_BLKP(bp)), PACK(0, 1));  // 새 에필로그 헤더

    /* 만약 이전 블록이 가용 블록이라면 연결시킨다. */
    return coalesce(bp);
}

static void* coalesce(void* bp){
    // 인접 앞 블록의 footer, 인접 뒤 블록의 header를 보고 가용 여부를 확인.
    size_t prev_alloc = GET_ALLOC(FTRP(PREC_BLKP(bp)));  // 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(SUCC_BLKP(bp)));  // 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 : 직전, 직후 블록이 모두 할당 -> 해당 블록만 free list에 넣어주면 된다.

    // case 2 : 직전 블록 할당, 직후 블록 가용
    if(prev_alloc && !next_alloc){
        delete_node(SUCC_BLKP(bp));    // free 상태였던 직후 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(SUCC_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3 : 직전 블록 가용, 직후 블록 할당
    else if(!prev_alloc && next_alloc){
        delete_node(PREC_BLKP(bp));    // 직전 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(PREC_BLKP(bp)));
        bp = PREC_BLKP(bp); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));  
    }

    // case 4 : 직전, 직후 블록 모두 가용
    else if (!prev_alloc && !next_alloc) {
        delete_node(PREC_BLKP(bp));
        delete_node(SUCC_BLKP(bp));
        size += GET_SIZE(HDRP(PREC_BLKP(bp))) + GET_SIZE(FTRP(SUCC_BLKP(bp)));
        bp = PREC_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));  
        PUT(FTRP(bp), PACK(size, 0));  
    }

    // 연결된 새 가용 블록을 free list에 추가한다.
    insert_node(bp);

#ifdef NEXT_FIT
    if ((last_bp > (char *)bp) && (last_bp < (char *)SUCC_BLKP(bp))) 
    last_bp = bp;
#endif
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // 해당 블록의 size를 알아내 header와 footer의 정보를 수정한다.
    size_t size = GET_SIZE(HDRP(bp));

    // header와 footer를 설정
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 만약 앞뒤의 블록이 가용 상태라면 연결한다.
    coalesce(bp);
}

/*
    insert_node(bp) : 새로 반환되거나 생성된 가용 블록을 free list 에 넣는다.
*/
void insert_node(void* bp){
#ifdef INSERT_LIFO    
    /* LIFO */
    NEXT_FREEP(bp) = free_listp;
    PREV_FREEP(bp) = NULL;
    PREV_FREEP(free_listp) = bp;
    free_listp = bp;
#else
    /* address order */
    void *curr = free_listp;
    void *saved = curr;
    void *prev = NULL;
    while (curr != NULL && bp < curr) {
        prev = PREV_FREEP(curr);
        saved = curr;
        curr = NEXT_FREEP(curr);
    }
    
    SET_PREV_FREE(bp, prev);
    SET_NEXT_FREE(bp, saved);
    if (prev != NULL) {
        SET_NEXT_FREE(prev, bp);
    } else { 
        free_listp = bp;/* Insert bp before current free list head*/
    }
    if (saved != NULL) {
        SET_PREV_FREE(saved, bp);
    }
#endif
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (size == 0) {
        mm_free(ptr);
        return;
    }
    void *oldptr = ptr;  // 크기를 조절하고 싶은 힙의 시작 포인터
    void *newptr;        // 크기 조절 뒤의 새 힙의 시작 포인터
    size_t copySize;     // 복사할 힙의 크기
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));

    // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안 된다. 
    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize);  // newptr에 oldptr를 시작으로 copySize만큼의 메모리 값을 복사한다.
    mm_free(oldptr);  // 기존의 힙을 반환한다.
    return newptr;
}

/*
    delete_node(bp) : 할당되거나 연결되는 가용 블록을 free list에서 없앤다.
*/
void delete_node(void *bp){
    // // free list의 첫번째 블록을 없앨 때
    // if (bp == free_listp){
    //     PREV_FREEP(NEXT_FREEP(bp)) = NULL;
    //     free_listp = NEXT_FREEP(bp);
    // }
    // // free list 안에서 없앨 때
    // else{
    //     NEXT_FREEP(PREV_FREEP(bp)) = NEXT_FREEP(bp);
    //     PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
    // }

    void *next = (void *) NEXT_FREEP(bp);
    void *prev = (void *) PREV_FREEP(bp);
    if (prev == NULL) { /* Start of the list */
        free_listp = next;
    } else {
        SET_NEXT_FREE(prev, next);
    }
    
    if (next != NULL) { /* Not the end of list */
        SET_PREV_FREE(next, prev);
    }
}