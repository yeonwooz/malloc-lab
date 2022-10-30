// https://github.com/zhexinq/malloc/blob/master/mm-seglist.c
/*
 * mm.c
 *
 * Zhexin Qiu id: zhexinq
 * 
 * Allocator implemented based on segregated fits.
 * 
 * Block format: 
 * allocated block: [header][payload] minimum: 16 bytes 
 * free block: [header][prev][next][footer] minimum: 16 bytes
 * header: size + prev alloc state bit + alloc state bit
 *
 * Free policy: LIFO, free'd and coalesced block 
 * inserted to front of appropriate list.
 *
 * Allocation policy: first-search on appropriate list,
 * if found, split and insert the remainder to appropriate
 * list. Repeat on larger size class if not found. If no
 * fits on all size classes, request heap memory from OS,
 * coalesce with any previous free block, allocate
 * requested block out of this new block, and put remainder
 * into appropriate size class.
 *
 * Size classes (orgnized by free block size in bytes):
 * [2^4~2^5), [2^5~2^6), ..., [2^19~2^20), [2^20, inf]
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
#define DEBUGx
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

team_t team = {
    "team7",
    "Suyeon Woo",
    "woosean999@gmail.com",
    "Jinseob Kim",
    "jinseob.kim91@gmail.com",
};

#define DRIVER = 1

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

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define MIN_BLK_SIZE 16 /* minimum block size (bytes) */ 
#define NUM_SIZES 17 /* number of size classes */
#define MIN_PWR 4 /* power of 2 for the minimum size class */
#define MAX_PWR 20 /* power of 2 for the maximum size class */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
/* last 2 bits: 0x1 -- prev free, curr alloc */
/*              0x2 -- prev alloc, curr free */
/*              0x3 -- prev alloc, curr alloc*/
/*              0x0 -- prev free, curr free  */
#define PACK(size, prev_alloc, alloc)  ((size) | (prev_alloc << 1) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_PREV_ALLOC(p) ((GET(p) & 0x2) >> 1)                 

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                     
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Read and write a pointer at an address (64-bit) */
#define GET_PTR(addr) ((void *)(*(long *)(addr)))
#define PUT_PTR(addr, ptr) (*(long *)(addr) = (long)ptr)

/* Get the payload a block can provide */
#define GET_PAYLOAD(bp) (GET_SIZE(HDRP(bp)) - WSIZE)

/* Global variables */
static void *heap_listp = 0;
static void *free_lists_base = 0;
static void *free_lists_end = 0;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void deleteBlk(void *bp);
static void insertBlk(void *bp);
static void *hashBlkSize(size_t asize);
/* Internal routines for pointer arithmitic */
static unsigned int ptoi(void *bp);
static void *itop(unsigned int bpi);
static void *get_prev_free_bp(void *bp);
static void *get_next_free_bp(void *bp);
static size_t mm_log2(size_t n);
static void printHeap(int lineno);
static void printLists(int lineno);
static void printRaw(int lineno);
static int in_heap(const void *p);
/*
 * Initialize: return -1 on error, 0 on success.
 * Initial heap: 17 size class pointers + proplogue + epilogue
 */
int mm_init(void) {
	int i;
	void *bp;

	if ((heap_listp = mem_sbrk(NUM_SIZES*DSIZE+4*WSIZE)) == (void *)-1)
		return -1;
		/* Create the initial empty free lists */
	free_lists_base = heap_listp;
	/* Initialize all list pointers to NULL */
	for (i = 0; i < NUM_SIZES; i++) {
		PUT_PTR(heap_listp, 0);
		heap_listp += DSIZE;
	}
	free_lists_end = heap_listp;

	/* Add prologue and epilogue */
	PUT(heap_listp, 0); /* Zero padding */
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1, 1)); /* Prologue header */
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1, 1)); /* Prologue footer */
	PUT(heap_listp + (3*WSIZE), PACK(0, 1, 1)); /* Epilogue header */
	heap_listp += (2*WSIZE);

	/* Extend the empty heap with a CHUNKSIZE bytes */
	if ((bp = extend_heap(CHUNKSIZE/WSIZE)) == NULL)
		return -1;

    return 0;
}

/*
 * allocate at double-word aligned block of at lease size bytes to
 * user. Return pointer to the allocated block if success, otherwise
 * return NULL
 */
void *malloc (size_t size) {
	size_t asize; /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit found */
	void *bp;

	/* Ignore spurious requests */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs */
	if (size <= (DSIZE + WSIZE))
		asize = MIN_BLK_SIZE;
	else
		asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE);

	/* Search free lists for a fit */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}

	/* No fit. Ask more heap memory from OS */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL;
	place(bp, asize);

	return bp;
}

/*
 * free a block at given ptr
 */
void free (void *bp) {
	void *next_bp_hdrp;

	if (bp == 0)
		return;

	/* get the allocated block size */
	size_t size = GET_SIZE(HDRP(bp));

	/* free the block */
	PUT(HDRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp)), 0));
	PUT(FTRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp)), 0));
	/* set next block's prev_alloc state to 0 */
	next_bp_hdrp = HDRP(NEXT_BLKP(bp));
	PUT(next_bp_hdrp, GET(next_bp_hdrp) & ~0x2);

	/* coalesce with any ajacent blocks */
	bp = coalesce(bp);

}

/*
 * realloc - an naive implementation
 */
void *realloc(void *oldptr, size_t size) {
	size_t oldsize;
	void *newptr;
	
	if (size == 0) {
		free(oldptr);
		return NULL;
	}

	if (oldptr == NULL) {
		return malloc(size);
	}

	/* realloc() fails leave old ptr untouched */
	if (!(newptr = malloc(size))) {
		return NULL;
	}

	/* Copy the old data */
	oldsize = GET_SIZE(HDRP(oldptr));
	if (size < oldsize) oldsize = size;
	memcpy(newptr, oldptr, oldsize);

	/* Free the old block */
	free(oldptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
	size_t bytes;
	void *ptr;

	bytes = nmemb * size;
	ptr = malloc(bytes);
	memset(ptr, 0, bytes);

    return ptr;
}

/*
 * internal helper routines 
 */

/*
 * extend the heap by words by asking the OS
 * return pointer to the paged-in coalesced free block of size requested
 */
static void *extend_heap(size_t words) {
	char *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	/* Initialize free block header/footer and epilogue header */
	/* free block header */
	PUT(HDRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp)), 0)); 
	/* free block footer */
	PUT(FTRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp)), 0));
	/* new epilogue header */ 
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0, 1));

	/* Coalesce if previous block is free */
	return coalesce(bp);
}

/*
 * merge any free blocks adjacent in address
 * 1. delete adjacent blocks from their coressponding free lists
 * 2. coalesce them to a larger free block
 * 3. return this new block to the caller
 *
 */
static void *coalesce(void *bp) {
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	/* both sides allocated */
	if (prev_alloc && next_alloc) {
		;
	}
	/* prev allocated but next free */
	else if (prev_alloc && !next_alloc) {
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		/* delete next block from its list */
		deleteBlk(NEXT_BLKP(bp));
		/* coalesce with next */
		PUT(HDRP(bp), PACK(size, 1, 0));
		PUT(FTRP(bp), PACK(size, 1, 0));
	}
	/* prev free and next allocated */
	else if (!prev_alloc && next_alloc) {
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		/* delete prev block from its list */
		deleteBlk(PREV_BLKP(bp));
		/* coalesce with prev */
		PUT(FTRP(bp), PACK(size, 1, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 0));
		bp = PREV_BLKP(bp);
	}
	/* both sieds free */
	else {
		size += (GET_SIZE(HDRP(PREV_BLKP(bp))) +
				GET_SIZE(HDRP(NEXT_BLKP(bp))));
		/* detele prev and next free blocks from their lists */
		deleteBlk(NEXT_BLKP(bp));
		deleteBlk(PREV_BLKP(bp));
		/* coalesce with both sides */
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 1, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1, 0));
		bp = PREV_BLKP(bp);
	}
	insertBlk(bp);
	return bp;

}

/*
 * delete free block from lists
 * 1. bp's prev (if exists) points to its next
 * 2. bp's next (if exists) points to its prev
 * 3. change the list head to bp's next if bp is the head
 */
static void deleteBlk(void *bp) {
	unsigned int prev = GET(bp);
	unsigned int next = GET(bp+WSIZE);
	void *array_ptr = 0;

	/* have both prev/next free blocks */
	if (prev && next) {
		PUT(itop(prev)+WSIZE, next); /* bp's prev points to bp's next */
		PUT(itop(next), prev); /* bp's next points to bp's prev */
	}
	/* head of the list and have successive free block */
	else if (!prev && next) {
		array_ptr = hashBlkSize(GET_SIZE(HDRP(bp))); /* get addr of head ptr */
		PUT_PTR(array_ptr, itop(next)); /* change the head to bp's next */
		PUT(itop(next), 0); /* bp's next's prev points to NULL */
	}
	/* last in the list and has previous free block */
	else if (prev && !next) {
		PUT(itop(prev)+WSIZE, 0);
	}
	/* only free block in the list */
	else {
		array_ptr = hashBlkSize(GET_SIZE(HDRP(bp)));
		PUT_PTR(array_ptr, 0); /* head of this list become NULL */
	}
}
/*
 * insert free block into appropriate lists
 * 1. hash size to get addr in the array of ptrs to lists
 * 2. insert the free block in the front of appropriate list
 */
static void insertBlk(void *bp) {
	void *array_ptr;
	void *head_bp;

	array_ptr = hashBlkSize(GET_SIZE(HDRP(bp)));

	/* at least one free block already in the list */
	if ((head_bp = GET_PTR(array_ptr))) {
		PUT(bp, 0); /* set bp's prev */
		PUT(bp+WSIZE, ptoi(head_bp)); /* set bp's next */
		PUT(head_bp, ptoi(bp)); /* set old head's prev */
	}
	/* the list is empty */
	else {
		PUT(bp, 0); /* set bp's prev */
		PUT(bp+WSIZE, 0); /* set bp's next */
	}
	
	PUT_PTR(array_ptr, bp); /* reset the head to be bp */
}  

/*
 * find a fit in all the available free blocks
 * 1. use hash function to locate an appropriate list to start
 * 2. if fit not found, search larger size class
 * 3. repeate until a fit or exhaust all lists without a fit
 */
static void *find_fit(size_t asize) {
	void *bp;
	void *array_ptr;

	array_ptr = hashBlkSize(asize);

	for (; array_ptr < free_lists_end; array_ptr+=DSIZE) {
		bp = GET_PTR(array_ptr);
		while (bp) {	
			if (GET_SIZE(HDRP(bp)) >= asize) {
				return bp;
			}
			bp = get_next_free_bp(bp);
		}
	}
	/* fit not found */
	return NULL;
}

/*
 * alloactes a block and split if possible
 * 1. delete the free block from list
 * 2. split if remainder not less than mimimum block size, insert to list
 * 3. otherwise, just fill the whole block
 */
static void place(void *bp, size_t asize) {
	size_t csize = GET_SIZE(HDRP(bp));

	/* delete the free block from list */
	deleteBlk(bp);

	if ((csize - asize) >= MIN_BLK_SIZE) {
		/* allocate requested block */
		PUT(HDRP(bp), PACK(asize, 1, 1));
		PUT(FTRP(bp), PACK(asize, 1, 1));
		/* split the block */
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize-asize, 1, 0));
		PUT(FTRP(bp), PACK(csize-asize, 1, 0));
		/* insert splitted free block back to appropriate list */
		insertBlk(bp);
	} 
	else {
		/* fill the whole block */
		PUT(HDRP(bp), PACK(csize, 1, 1));
		PUT(FTRP(bp), PACK(csize, 1, 1));
		/* set next block's prev_alloc to 1 */
		PUT(HDRP(NEXT_BLKP(bp)), GET(HDRP(NEXT_BLKP(bp))) | 0x2);
	}
} 

/*
 * hashes the requested size to appropriate list
 * return an address storing 1st free block of the appropriate list
 */
static void *hashBlkSize(size_t asize) {
	return (free_lists_base + mm_log2(asize) * DSIZE);
 }

/*
 * return log2(n) offseted by MIN_PWR, truncate fractional part
 * e.g. log2(2^4) = 0, log2(2^5+1) = 1 
 */
static size_t mm_log2(size_t n) {
	size_t count = 0;
	n >>= 5; 
	while (n && count < 16) {
		count++;
		n >>= 1;
	}
	return count;
}

/* 
 * internal helper functions for 64-bit pointer and 32-bit int value
 * conversion, and free list traversing
 */
static unsigned int ptoi(void *bp) {
	return (unsigned int)(bp - mem_heap_lo());
}

static void *itop(unsigned int bpi) {
	return bpi? (((void *)((long)(bpi)) + (long)(mem_heap_lo()))) : NULL;
}

static void *get_prev_free_bp(void *bp) {
	return itop(GET(bp));
}

static void *get_next_free_bp(void *bp) {
	return itop(GET(bp + WSIZE));
}

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

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
	void *bp, *hdrp, *ftrp;
	unsigned int alloc;
	void *bp_prev, *array_ptr;
	unsigned int count_heap, count_lists;
	unsigned int blk_size;
	unsigned int power;

	/* check heap */
	/* check there are space for list pointers */
	if ((heap_listp - mem_heap_lo())/DSIZE != NUM_SIZES+1) {
		printf("line %d: list pointers space not enough!\n", lineno);
		printHeap(__LINE__);
		exit(1);
	}
	/* prologue and epilogue */
	bp = heap_listp;
	hdrp = HDRP(bp);
	ftrp = FTRP(bp);
	/* check prologue */
	if ((GET_SIZE(hdrp) != DSIZE) || (GET_ALLOC(hdrp) != 1)) {
		printf("line %d: Prologue header wrong!\n", lineno);
		printf("header size: %d\n", GET_SIZE(hdrp));
		printf("alloc state: %d\n", GET_ALLOC(hdrp));
		exit(1);
	}
	if ((GET_SIZE(hdrp) != GET_SIZE(ftrp)) || 
		(GET_ALLOC(hdrp) != GET_ALLOC(ftrp))) {
		printf("line %d: Prologue header/footer inconsistent!\n", lineno);
		printf("header: (size %d, alloc: %d)\n", GET_SIZE(hdrp), 
			    GET_ALLOC(hdrp));
		printf("footer: (size %d, alloc: %d)\n", GET_SIZE(ftrp),
				GET_ALLOC(ftrp));
		exit(1);
	}
	/* check epilogue */
	bp = mem_heap_hi()+1;
	hdrp = HDRP(bp);
	if ((GET_SIZE(hdrp) != 0) || GET_ALLOC(hdrp) != 1) {
		printf("line %d: Epilogue wrong!\n", lineno);
		printf("size: %d\n", GET_SIZE(hdrp));
		printf("alloc: %d\n", GET_ALLOC(hdrp));
	}
	/* check each block's alignment */
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!aligned(bp)) {
			printf("line %d: block not aligned!\n", lineno);
			printf("block addr %p\n", bp);
			exit(1);
		}
	}
	/* check heap boundaries */
	for (bp = heap_listp; bp < mem_heap_hi()+1; bp = NEXT_BLKP(bp)) {
		if (!in_heap(bp)) {
			printf("line %d: block %p not in heap range!\n", lineno, bp);
			printf("heap_hi: %p, heap_lo: %p\n", mem_heap_hi(), mem_heap_lo());
			exit(1);
		}
	}
	if (bp > (mem_heap_hi()+1)) {
		printf("line %d: block %p not in heap range!\n", lineno, bp);
		printf("heap_hi: %p, heap_lo: %p\n", mem_heap_hi(), mem_heap_lo());
		exit(1);	
	}
	/* check each free block's header and footer */
	/* check minimum block size */
	/* check current blk's prev_alloc match previous blk's alloc state */
	bp_prev = heap_listp;
	bp = NEXT_BLKP(heap_listp);
	for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		hdrp = HDRP(bp);
		if (!GET_ALLOC(hdrp)) {
			ftrp = FTRP(bp);
			if (GET_SIZE(hdrp) != GET_SIZE(ftrp) || 
				GET_ALLOC(hdrp) != GET_ALLOC(ftrp) ||
				GET_PREV_ALLOC(hdrp) != GET_PREV_ALLOC(ftrp)) {
				printf("line %d: hdr/ftr not matched!\n", lineno);
				printf("block %p\n", bp);
				printf("hdr size %d, pre_alloc %d, alloc %d\n", 
					   GET_SIZE(hdrp), GET_PREV_ALLOC(hdrp), GET_ALLOC(hdrp));
				printf("ftr size %d, pre_alloc %d, alloc %d\n", 
					   GET_SIZE(ftrp), GET_PREV_ALLOC(ftrp), GET_ALLOC(ftrp));
				exit(1);
			}
		}
		if (GET_SIZE(hdrp) < MIN_BLK_SIZE) {
			printf("line %d: less than minimum block size!\n", lineno);
			printf("block %p, block size %d\n", bp, GET_SIZE(hdrp));
			exit(1);
		}
		if (GET_PREV_ALLOC(hdrp) != GET_ALLOC(HDRP(bp_prev))) {
			printf("line %d: curr's prev_alloc not match prev's alloc!\n", 
				    lineno);
			printf("curr %p 's prev_alloc %d\n", bp, GET_PREV_ALLOC(hdrp));
			printf("prev %p 's alloc %d\n", bp_prev, GET_ALLOC(HDRP(bp_prev)));
			printHeap(lineno);
			exit(1);
		}
		bp_prev = bp;
	}
	/* check coalescing */
	alloc = 1;
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (alloc == 0 && GET_ALLOC(HDRP(bp)) == 0) {
			printf("line %d: neighboring free blocks not coalesced!\n", 
				    lineno);
			printf("curr blk %p, alloc %u\n", bp, GET_ALLOC(HDRP(bp)));
			printf("prev blk %p, alloc %u\n", PREV_BLKP(bp), 
				    GET_ALLOC(HDRP(PREV_BLKP(bp))));
			printHeap(lineno);
			exit(1);
		}
		alloc = GET_ALLOC(HDRP(bp));
	}

	/* check free list */
	/* all list pointers in heap */
	array_ptr = free_lists_base;
	for (; array_ptr < free_lists_end; array_ptr += DSIZE) {
		bp = GET_PTR(array_ptr);
		if (bp && !in_heap(bp)) {
			printf("line %d: list head not in heap!\n", lineno);
			exit(0);
		}
	}
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp))) {
			if (get_next_free_bp(bp) && !in_heap(get_next_free_bp(bp))) {
				printf("line %d: %p next not in heap!\n", lineno, bp);
				printf("next: %p\n", get_next_free_bp(bp));
				exit(1);
			}
			if (get_prev_free_bp(bp) && !in_heap(get_prev_free_bp(bp))) {
				printf("line %d: %p prev not in heap!\n",lineno, bp);
				printf("prev: %p\n", get_prev_free_bp(bp));
				exit(1);
			}
		}
	}
	/* next/prev pointers consistent */
	array_ptr = free_lists_base;
	for (; array_ptr < free_lists_end; array_ptr += DSIZE) {
		bp = GET_PTR(array_ptr);
		while (bp) {
			bp_prev = get_prev_free_bp(bp);
			if (bp_prev && (get_next_free_bp(bp_prev) != bp)) {
				printf("line %d: nxt/pre pointers inconsistent!\n", lineno);
				printf("blk %p prev %p\n", bp, bp_prev);
				printf("blk %p next %p\n", bp_prev, get_next_free_bp(bp_prev));
				exit(1);
			}
			bp = get_next_free_bp(bp);
		}
	}
	/* free block counting */
	count_heap = 0;
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)))
			count_heap++;
	}
	count_lists = 0;
	array_ptr = free_lists_base;
	for (; array_ptr < free_lists_end; array_ptr += DSIZE) {
		bp = GET_PTR(array_ptr);
		while (bp) {
			count_lists++;
			bp = get_next_free_bp(bp);
			if (count_lists > count_heap) {
				printf("line %d: cycles in list\n", lineno);
				printRaw(lineno);
				printHeap(lineno);
				exit(1);
			}
		}
	}
	if (count_heap != count_lists) {
		printf("line %d: number free blocks inconsistent\n", lineno);
		printf("heap count: %u\n", count_heap);
		printf("lists count: %u\n", count_lists);
		printRaw(__LINE__);
		printHeap(__LINE__);
		printLists(__LINE__);
		exit(1);
	}
	/* all blocks in each list bucket fall within size range */
	array_ptr = free_lists_base;
	for (; array_ptr < free_lists_end; array_ptr += DSIZE) {
		power = (array_ptr - free_lists_base)/DSIZE + 4;
		bp = GET_PTR(array_ptr);
		while (bp) {
			blk_size = GET_SIZE(HDRP(bp));
			if (blk_size < (unsigned int)(1 << power) || 
				blk_size > (unsigned int)(1 << (power+1))) {
				printf("line %d: block not within list size range!\n", lineno);
				printf("class size: %u, block size %u\n", 
					   (1<<power), blk_size);
				printLists(lineno);
				exit(1);
			}
			bp = get_next_free_bp(bp);
		}
	}	
}

/*
 * print raw data in the heap
 */

static void printRaw(int lineno) {
	void *bp;

	printf("-------------------------------------------------------------\n");
	printf("line %d, raw heap data in each word:\n", lineno);
	for (bp = mem_heap_lo(); bp < (mem_heap_hi()+1); bp+=WSIZE) {
		printf("[%u]", GET(bp));
	}
	printf("\n------------------------------------------------------------\n");
}

/*
 * print out the current heap
 */
static void printHeap(int lineno) {
	void *bp;

	printf("line %d: the block image: [addr, words, alloc]\n", lineno);
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		printf("[%p, %u, %u] -> ", bp, GET_SIZE(HDRP(bp)),
			   GET_ALLOC(HDRP(bp)));
	}
	printf("[%p, %u, %u]\n", bp, GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)));
	printf("-------------------------------------------------------------\n");
}

/*
 * print out the free lists
 */
static void printLists(int lineno) {
	void *array_ptr, *bp;
	int i;

	printf("-------------------------------------------------------------\n");
	printf("line %d:", lineno);
	printf("list heads: (list_num, bp)\n");
	array_ptr = free_lists_base;
	for (i = 0; array_ptr < free_lists_end; array_ptr += DSIZE){
		printf("(%u, %p), ", i, GET_PTR(array_ptr));
		i++;
	}
	printf("\nthe lists image: (prev)<-[addr, words, alloc]->(next)\n");
	array_ptr = free_lists_base;
	i = 0;
	for (; array_ptr < free_lists_end; array_ptr+=DSIZE) {
		bp = GET_PTR(array_ptr);
		if (bp)
			printf("list %d:\n", i);
		while (bp) {
			printf("(%p)<-[%p, %u, %u]->(%p);", get_next_free_bp(bp), bp,
				    GET_SIZE(HDRP(bp)), GET_ALLOC(HDRP(bp)), 
				    get_next_free_bp(bp));
			bp = get_next_free_bp(bp);
			if (!bp)
				printf("\n");
		}
		i++;
	}
	printf("-------------------------------------------------------------\n");

	return;
}