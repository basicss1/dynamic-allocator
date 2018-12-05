/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Here we try to implement a simple allocator;
 * we implement with implicit free lists and we add block boundaries
 * to distinguish between allocated and free blocks. The invariant form
 * of the implicit free list includes an ununsed padding word, prologue
 * block and the heap always ends with an epilogue block. For each block
 * there is a 4_byte header which contains information about size and allo
 * -cation status, the payload and optional padding.
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
    "Group 14",
    /* First member's full name */
    "Jakob Frank",
    /* First member's email address */
    "jakobfrank2019@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Yuxin Chen",
    /* Second member's email address (leave blank if none) */
    "yuxinchen2020@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* Word and header/footer size (bytes) */
#define WSIZE       4
/* Double word size (bytes) */
#define DSIZE       8
/* Extend heap by this amount (bytes) */
#define CHUNKSIZE  (1<<12)


/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


/*#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) */
/* get the larger value between x and y */
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p,val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*global variable heap_listp; always points to the start of the heap */
static char* heap_listp = 0;

/*helper functions declared */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);

/*helper functions defined */

/*extend_heap is invoked in two circumstances: 1) when heap is initialized
and 2) when mm_malloc is unable to find a suitable fit */
static void *extend_heap(size_t words){
	char* bp;
	size_t size;

	/*Allocate an even number of words to maintain allignemnt */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((long) (bp = mem_sbrk(size)) == -1)
		return NULL;

	/*initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0)); /* Free Block's Header */
	PUT(FTRP(bp), PACK(size, 0)); /* Free Block's footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); /*New epilogue header */

	/*Coalesce if the previous block was free */
	return coalesce(bp);
}

/* coalesce combines free blocks in the heap to avoid false fragmentation */
static void* coalesce(void *bp){
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	/* four different cases for coalesce function */

	/*case 1: both previous and next blocks are allocated */
	if (prev_alloc && next_alloc){
		return bp;
	}

	/*case 2: only previous block is allocated; combining bp with the next block */
	else if (prev_alloc && !next_alloc){
		//update size to be the sum of size of bp and that of next block
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));

	}

	/*case 3: only next block is allocated; combining bp with the previous block */
	else if (!prev_alloc && next_alloc){
		//update size to be the sum of size of bp and that of previous block
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	/*case 4: both previous and next block are unallocated; combining bp with the other 2 */
	else {
		//update size to be the sum of 3 blocks
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	return bp;

}

/* place the allocated block in a suitable free block. If the remainder of the block
after splitting would be greater than or equal to the minimum block size, we go ahead
and split the block */
static void place(void *bp, size_t asize){
	size_t csize = GET_SIZE(HDRP(bp));

	if ((csize - asize) >= (2 * DSIZE)){
		//place before moving on to the next block
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
	}
	else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

/*find_fit looks for suitable free blocks to get ready for place */
static void *find_fit(size_t asize){
	void *bp;
	//traversing the heap to find a fit
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
			return bp;
		}
	}
	return NULL;
}

/* main functions */
/*mm_init initilizes the heap */
int mm_init(void){
	/* create the initial empty heap */
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return -1;
	PUT(heap_listp, 0); //alignment padding
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); //prologue header
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); //prologue header
	PUT(heap_listp + (3 * WSIZE), PACK(0,1)); //epilogue header
	heap_listp += (2 * WSIZE);

	/*Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return -1;
	return 0;
}

/* mm_malloc simulates the allocator; it looks over the heap to find a suitable
free block to place the requested block; if unable to find a fit, malloc calls
extend_heap and place to place the requested block in the new free block */
void *mm_malloc(size_t size){
	size_t asize;
	size_t extendsize;
	char *bp;

	/* checking the validity of parameter size */
	if (size == 0)
		return NULL;

	/* must allow room for header and the footer */
	if(size <= DSIZE)
		asize = 2 * DSIZE;
	/*keeping the right allignment */
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

	/* if we can find a suitable fit for the requested block we call the place function */
	if ((bp = find_fit(asize)) != NULL){
		place(bp, asize);
		return bp;
	}

	/*if not we extend the heap with a new free block to place the requested block */

	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return NULL;
	place(bp, asize);
	return bp;
}

/*mm_free frees the requested block and then merges adjacent free blocks using the boundary_tag
coalescing technique as we call the coalesce function */
void mm_free(void* bp){
	size_t size = GET_SIZE(HDRP(bp));

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/* from manual: realloc changes the size of the memory block pointed to by ptr to size bytes. The contents
will be unchanged to the minimum of the old and the new sizes; newly allocated memories will be
uninitiazlied */
void *mm_realloc(void* ptr, size_t size){
	void *oldptr = ptr;
	void *newptr;

	size_t old = GET_SIZE(HDRP(ptr));

	/*if size is negative input is invalid */
	if (size < 0) return 0;

	/* if size is zero, then it is equivalent to
	free(ptr) */

	if (size == 0){
		mm_free(ptr);
		return 0 ;
	}

	/* if ptr is null, then the call is equivalent to malloc(size)
	otherwise the content's gonna be unchanged to the minimum of the old
	and new sizes */
	else {
		if (oldptr == NULL){
			mm_malloc(size);
			return 0;

		}

		else{
			//initializing newptr
			newptr = mm_malloc(size);
			if (size > old){
				//the the previous memory block will remain unchanged and we copy old data
				memcpy(newptr, ptr, old);
			}
			else{
				//if size is smaller than the size of previous memory block we keep the
				//part up to size unchanged
				memcpy(newptr, ptr, size);
			}

			mm_free(ptr); //free the old pointer
			return newptr;

		}
	}
}
