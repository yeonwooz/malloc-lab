/*
*mm.c
 *
 * 명시적 가용리스트를 이중 연결 포인터로 구현.
 * next fit 각각으로 배치장소를 찾는다. 
 * free 후 즉시연결을 수행한다.
 * 
 * Explicit free list based malloc package with first fit / next fit placing and real time coalescing.
 *
 */

#define INSERT_LIFO   // LIFO (삭제시 address order)
#define NEXT_FIT      // NEXT_FIT (삭제시 FIRST_FIT)

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    "team7",
    "Suyeon Woo",
    "woosean999@gmail.com",
    "Jinseob Kim",
    "jinseob.kim91@gmail.com",
};

/* 상수 매크로 (constant macro) */
#define WSIZE 4
#define DSIZE 8
#define MINIMUM 16      // 헤더, 푸터, PREV, NEXT
#define CHUNKSIZE (1<<12)     // test case optimized
#define INITCHUNKSIZE (1<<6)  // test case optimized
#define ALIGNMENT DSIZE

/* 유틸 함수 매크로 (util function macro) */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p)          (*(unsigned int*)(p))
#define PUT(p, val)     (*(unsigned int*)(p) = (val))
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* 
* 블록 포인터 bp를 인자로 받아 블록의 헤더와 푸터의 주소를 반환한다 
* Get header pointer, footer pointer
*/
#define HDRP(bp)    ((char*)(bp) - WSIZE) 
#define FTRP(bp)    ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 
* 물리적 인접 블록(앞, 뒤)
* physically front, next block
*/
#define PREC_BLKP(bp)   ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) 
#define SUCC_BLKP(bp)   ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) 

/* 
* Free List( 이중 연결리스트 ) 상에서의 이전, 이후 블록의 포인터. 
* previous, next block in free list (doubly linked list)
*/
#define PREV_FREEP(bp)  (*(void**)(bp))  
#define NEXT_FREEP(bp)  (*(void**)(bp + WSIZE))

/*
* 블록 포인터를 받아서 free list 상의 현재 bp 블록 앞, 뒤를 두번째 인자로 변경
* set PREV of bp as prev
* set NEXT of bp as next
*/
#define SET_PREV(bp, prev) (*((void **)(bp)) = prev) 
#define SET_NEXT(bp, next) (*((void **)(bp + WSIZE)) = next) 

/* free 블록: 이중연결리스트로 관리하며 prev, next 가 있다.
*  allocated 블록: 헤더와 푸터만 있다.
*/

static char *heap_listp = NULL; 
/*
묵시적 할당기 : 항상 힙의 프롤로그 헤더와 프롤로그 푸터 사이를 가리키는 정적변수 포인터
명시적 할당기 : 항상 힙의 프롤로그 (헤더 + PREV) 와 (NEXT + 푸터) 사이를 가리키는 정적변수 포인터
*/

static char *free_listp = NULL; // free list 의 첫 블록을 가리키는 정적변수 포인터

#ifdef NEXT_FIT
    static char *last_bp;
#endif

static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void* place(void* bp, size_t newsize);
static void insert_node(void* bp);
static void delete_node(void *bp);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);
int mm_checkheap(int lineno);

#define UINT_CAST(p) ((size_t)p)
#define DEBUG


#ifdef DEBUG
// #define CHECKHEAP(__LINE__)                                                 
//     // printf("\n==heap=checker=on==\n%s : %d\n", __func__, __LINE__); 
//     mm_checkheap(__LINE__);
#endif

int mm_checkheap(int lineno)
{
    char *heap_lo = mem_heap_lo();                      // pointing first word of the heap
    char *heap_hi = heap_lo + (mem_heapsize() - WSIZE); // pointing last word of the heap
    char *bp;
    /* heap level check*/
    assert(GET(heap_lo) == 0);                              // check unused
    assert(GET(heap_lo + 1 * WSIZE) == PACK(2 * DSIZE, 1)); // check Prologue header
    // assert(GET(heap_lo + 2*WSIZE) == 0);                   // check Prologue PRED
    // assert(GET(heap_lo + 3*WSIZE) == 0);                   // check Prologue SUCC
    assert(GET(heap_lo + 4 * WSIZE) == PACK(2 * DSIZE, 1)); // check Prologue footer
    assert(GET(heap_hi) == PACK(0, 1));                     // check Epilogue block
    printf("heap level ok\n");
    /* block level */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = SUCC_BLKP(bp))
    {
        assert(GET(HDRP(bp)) == GET(FTRP(bp)));                       // check header and footer match
        assert(!(UINT_CAST(bp) & 0x7));                               // check if payload area aligned
        assert(GET_ALLOC(HDRP(bp)) | GET_ALLOC(HDRP(SUCC_BLKP(bp)))); // check contiguous free blocks
        assert(heap_lo < HDRP(bp) && FTRP(bp) < heap_hi);             // check heap bound
        // check all free blocks are in the free list
        if (!GET_ALLOC(HDRP(bp)))
        {
            void *pred_free;
            for (pred_free = PREV_FREEP(free_listp); GET_ALLOC(HDRP(pred_free)) != 1; pred_free = PREV_FREEP(pred_free))
            {
                if (GET_ALLOC(HDRP(pred_free)) == 1)
                    break;
            }
            assert(pred_free);
        }
    }
    printf("block level ok\n");
    // detect cycle
    char *hare;
    char *tortoise;
    hare = tortoise = free_listp;
    printf("hare : %16p, tortoise: %16p\n", hare, tortoise);
    while (1)
    {
        if (GET_ALLOC(HDRP(hare)) == 1 || GET_ALLOC(HDRP(PREV_FREEP(hare))) == 1)
            break;
        hare = PREV_FREEP(PREV_FREEP(hare));
        tortoise = PREV_FREEP(tortoise);
        printf("hare : %16p, tortoise: %16p\n", hare, tortoise);
        assert(hare != tortoise);
    }
    printf("cycle check ok\n");
    printf("\n=======done=======\n");
    // /* list level check */
    // printf(“<<free block list>>\n”);
    // void * free = root;
    // void * next_free = (void *)GET(NEXT_FREE(root));
    // while (next_free != NULL) {
    //     printf(“free : %p, next free : %p\n”, free, next_free);
    //     assert(!GET_ALLOC(HDRP(next_free)));
    //     assert(free < next_free);
    //     free = next_free;
    //     next_free = (void *)GET(NEXT_FREE(next_free));
    // }
    return 1;
}

/* 
 * mm_init 
 * - 패키지 초기화
 * - initialize the malloc package.
 */
int mm_init(void)
{
    /* 미사용 패딩, 프롤로그 블록 헤더, 프롤로그 블록 PREV, 프롤로그 블록 NEXT, 프롤로그 블록 푸터,에필로그 푸터 */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void*)-1)
        return -1;

    // 포인터 위치 지정
    PUT(heap_listp, 0);                             // unused
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1));  // prologue header = '16'
    PUT(heap_listp + (2*WSIZE), NULL);              // prologue block PREV =  'NULL'
    PUT(heap_listp + (3*WSIZE), NULL);              // prologue block NEXT =  'NULL'
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM, 1));  // prologue footer = '16'
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));        // epliogue header = '1'
    free_listp = heap_listp + DSIZE;  // heap_listp (0) + 프롤로그 헤더 + 프롤로그 PREV가 가용블록의 시작점
    heap_listp = free_listp;

#ifdef NEXT_FIT
    last_bp = heap_listp;
#endif
    
    // 초기 가용블록 생성 
    if (extend_heap(INITCHUNKSIZE / WSIZE) == NULL) //실패하면 -1 리턴
        return -1;
    return 0;
}

/*
 * mm_malloc 
 * - 요청받은 사이즈에 맞는 블록을 (find_fit으로 찾아) 할당한 후 해당 블록의 포인터를 리턴한다
 * - allocate new block and return its pointer
 */
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
        bp = place(bp, asize);  // place에서는 필요한 공간만 분할해서 써준다.
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);  // 둘 중 더 큰 값으로 사이즈를 정한다.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) 
        return NULL;
    bp = place(bp, asize);
    return bp;
}

/*
 * find_fit
 * - 요청받은 사이즈에 맞는 블록을 찾아 포인터를 리턴한다 
 * - find an adequate block pointer for requested size  
 */
static void* find_fit(size_t asize){
#ifdef NEXT_FIT
    /* Next-fit */
    char *old_bp = last_bp;

    /* 초기화는 보통 평가문에서 참조할 변수가 없을까봐 넣어주는데, 만약에 전역으로 선언해둔 게 있다면 평가문에서 그걸 참조할 것이므로 첫번째부분을 생략하고 세미콜론만 넣어주면 된다.*/
    
    /* last_bp(현재 힙 마지막)부터 힙 끝까지 서치한다 */
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

    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = NEXT_FREEP(bp)){
        if(asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }

    // 못 찾으면 NULL을 리턴한다.
    return NULL;
#endif
}

/*
 * place(bp, size)
 * - 요구 메모리를 할당할 수 있는 가용 블록을 할당한다. 이 때 블록이 커서 분할이 가능하면 분할한다.
 * - allocate new size of block to current pointer.( split if the block is too big ) 
 */
static void *place(void* bp, size_t asize){
    // 현재 할당할 수 있는 후보 가용 블록의 주소
    size_t csize = GET_SIZE(HDRP(bp));

    // 할당될 블록이므로 free list에서 없애준다.
    delete_node(bp);

    // 분할할 수 없어 바로 할당
    if ((csize - asize) < (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        return bp;
    }   

    // 분할이 가능한 경우
    if (asize >= 120) {
        /*
        * https://github.com/mightydeveloper/Malloc-Lab 로부터 아이디어를 얻어서,
        * 현재 테스트케이스 기준으로 최적기준을 찾아냈다.
        * 무조건 '현재 블록'을 할당블록으로 만들고 다음 블록을 가용으로 넣는 게 아니라,
        * 특정 사이즈 이상이 요구되는 경우에 '다음 블록'을 할당블록으로 만들고 현재블록을 가용에 넣도록 하면 바이너리 테스트에서 메모리 효율이 많이(약 30%p) 오른다. (이유는 모르겠음)
        * 일일이 넣어본 결과, 그 기준이 되는 사이즈 범위는 73 ~ 120이다 
        * 
        * For current binary test cases(7,8), if asize is over a specific range of numbers it's more efficient to assign next block and put current block into freelist. util pointe arise around 30%p. (not sure why)
        * this specific range is from 73 to 120 
        * 
        */
        // 앞의 블록은 가용 블록으로 분할한다.
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        // 뒤의 블록은 할당 블록으로
        PUT(HDRP(SUCC_BLKP(bp)), PACK(asize, 1));
        PUT(FTRP(SUCC_BLKP(bp)), PACK(asize, 1));

        // free list 에 분할된 블럭을 넣는다.
        insert_node(bp);
        bp = SUCC_BLKP(bp);
    }
    else {
        // 앞의 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // 뒤의 블록은 가용 블록으로 분할한다.
        PUT(HDRP(SUCC_BLKP(bp)), PACK(csize-asize, 0));
        PUT(FTRP(SUCC_BLKP(bp)), PACK(csize-asize, 0));

        // free list 에 분할된 블럭을 넣는다.
        insert_node(SUCC_BLKP(bp));
    }

    return bp;
}

/*
 * extend_heap 
 * - 워드 단위 메모리를 인자로 받아 힙을 늘려준다.
 * - exptend heap size
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

/*
 * coalesce
 * - 인접 앞 블록과 뒷 블록이 가용이라면 현재 블록과 합친다 
 * - combine physically front or next blocks with current block if they are free
 */

static void* coalesce(void* bp){
    // 인접 앞 블록의 footer, 인접 뒤 블록의 header를 보고 가용 여부를 확인.
    size_t prev_alloc = GET_ALLOC(FTRP(PREC_BLKP(bp)));  // 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(SUCC_BLKP(bp)));  // 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 : 직전, 직후 블록이 모두 할당 -> 해당 블록만 free list에 넣어주면 된다. => 아래에서 바로 insert node

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
 * mm_free 
 * - 할당되었던 블록을 프리하고 아무것도 반환하지 않는다
 * - Free a block and returns nothing
 */
void mm_free(void *bp)
{
    // 해당 블록의 size를 알아내 header와 footer의 정보를 수정한다
    size_t size = GET_SIZE(HDRP(bp));

    // header와 footer를 설정
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 만약 앞뒤의 블록이 가용 상태라면 연결한다
    coalesce(bp);
}

/*
 * insert_node(bp)
 * - 새로 반환되거나 생성된 가용 블록을 free list 에 넣는다
 * - put newly freed block into the free list
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
    
    SET_PREV(bp, prev);
    SET_NEXT(bp, saved);
    if (prev != NULL) {
        SET_NEXT(prev, bp);
    } else { 
        free_listp = bp;    /* Insert bp before current free list head */
    }
    if (saved != NULL) {
        SET_PREV(saved, bp);
    }
#endif
}

/*
 * mm_realloc 
 * - malloc되어있는 포인터에 새로운 사이즈만큼 재할당한다(새 포인터의 영역이 줄어들거나 늘어날 수 있고 포인터가 변경될 수 있다)
 * - reallocate new size of block to the old pointer or just copy memory into new pointer
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

    // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안 된다
    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize);  // newptr에 oldptr를 시작으로 copySize만큼의 메모리 값을 복사한다
    mm_free(oldptr);  // 기존의 힙을 반환한다.
    return newptr;
}

/*
 * delete_node(bp) 
 * - 할당되거나 연결되는 가용 블록을 free list에서 없앤다
 * - remove pointed block from the free list
 */
void delete_node(void *bp){
    void *next = (void *) NEXT_FREEP(bp);
    void *prev = (void *) PREV_FREEP(bp);
    if (prev == NULL) { /* Start of the list */
        free_listp = next;
    } else {
        SET_NEXT(prev, next);
    }
    
    if (next != NULL) { /* Not the end of list */
        SET_PREV(next, prev);
    }
}
