
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
    /* Team name */
    "X-Men",
    /* First member's full name */
    "Hayden Udelson",
    /* First member's email address */
    "haydenudelson2020@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Daniel Birnbaum",
    /* Second member's email address (leave blank if none) */
    "danielbirnbaum2020@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Points to first byte of heap */
static char *mem_heap;

/* Points to last byte of heap plus 1 */
static char *mem_brk;

/* Max legal heap addr plus 1 */
static char *mem_max_addr;

/* TEXTBOOK 
/* Basic constants and macros */
#define WSIZE     4       /* Word and header/footer size (bytes) */
#define DSIZE     8       /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & -0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)      ((char *)(bp) - WSIZE)
#define FTRP(bp)      ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/*
 * *extend_heap: Extends the heap with a new free block
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_SBRK(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) { 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * *find_fit: performs first-fit search of the implicit free list
 * not in textbook
 */
static void *find_fit(size_t asize)
{
  void *bp;
  if(free_count == 0)
    return NULL;
  
  int minlist = asize / 50;
  if(minlist > 83)
    minlist = 83;
  if(minlist < global_minlist)
    minlist = global_minlist;
  for(; minlist < 84; minlist++){
    int i = 0;
    for (bp = (char *)GET(head_listp + (minlist * WSIZE)); (int)bp != 0 && GET_SIZE(HDRP(bp)) > 0 && i < 250; bp = (char *)GET(bp+WSIZE)) {
      if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDROP(bp)))) {
	return bp;
      }
      i++;
    }
  }
  return NULL;
}

/*
 * place: places requested block at beginning of the free block, splitting only if
          the size of the remainder would equal or exceed the minimum block size
 * Not textbook
 */
static void place(void *bp, size_t asize)
{
  size_t ptr_size = GET_SIZE(HDRP(ptr));
  size_t remainder = ptr_size - asize;
    
  delete_node(ptr);
    
    
  if (remainder <= DSIZE * 2) {
    // Do not split block 
    PUT(HDRP(ptr), PACK(ptr_size, 1)); 
    PUT(FTRP(ptr), PACK(ptr_size, 1));
  }

  else if (asize >= 100) {
    // Split block
    PUT(HDRP(ptr), PACK(remainder, 0));
    PUT(FTRP(ptr), PACK(remainder, 0));
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1));
    PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1));
    insert_node(ptr, remainder);
    return NEXT_BLKP(ptr);
        
  }
    
  else {
    // Split block
    PUT(HDRP(ptr), PACK(asize, 1)); 
    PUT(FTRP(ptr), PACK(asize, 1)); 
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); 
    PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); 
    insert_node(NEXT_BLKP(ptr), remainder);
  }
  return ptr;
}

/* 
 * mm_init - initialize the malloc package.
 * creates a heap with an initial free block.
 */
int mm_init(void)
{
    /* Create initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    /* Extend the empty heap w a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
    return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
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
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr);
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

int mm_check(void)
{
     
}













