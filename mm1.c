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
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  "Team Northeast",
  /* First member's full name */
  "Daniel Birnbaum",
  /* First member's email address */
  "danielbirnbaum2020@u.northwestern.edu",
  /* Second member's full name (leave blank if none) */
  "Hayden Udelson",
  /* Second member's email address (leave blank if none) */
    "haydenudelson2020@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//*****Begin Textbook Code*****
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define GET_NEXT_PTR(bp)  (*(char **)(bp + WSIZE))
#define GET_PREV_PTR(bp)  (*(char **)(bp))

/* Puts pointers in the next and previous elements of free list */
#define SET_NEXT_PTR(bp, qp) (GET_NEXT_PTR(bp) = qp)
#define SET_PREV_PTR(bp, qp) (GET_PREV_PTR(bp) = qp)

static char *heap_listp = 0;

//*****End Textbook Code*****

static char *free_list_start = 0;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_in_free_list(void *bp);
static void remove_from_free_list(void *bp);
//static void mm_check(void *bp, int size);

//*****Begin Textbook Code*****
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp; //second condition and 'or' not inclu\ ded in textbook code

  //if ((char *)(bp) < 0x10)
  // prev_alloc = 1;
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
    
    //insert_in_free_list(bp), remove_from_free_list(bp) not included in textbook code
  if (prev_alloc && next_alloc) {             // Case 1
      insert_in_free_list(bp);
      return bp;
    }
    
 else if (prev_alloc && !next_alloc) {       // Case 2
      size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
      remove_from_free_list(NEXT_BLKP(bp));
      PUT(HDRP(bp), PACK(size, 0));
      PUT(FTRP(bp), PACK(size,0));
      }
 else if (!prev_alloc && next_alloc) {       // Case 3
      size += GET_SIZE(HDRP(PREV_BLKP(bp)));
      PUT(FTRP(bp), PACK(size, 0));
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      bp = PREV_BLKP(bp);
      remove_from_free_list(bp);
    }
    else {      // Case 4
      size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
      remove_from_free_list(PREV_BLKP(bp));
      remove_from_free_list(NEXT_BLKP(bp));
      PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
      PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
      bp = PREV_BLKP(bp);
    }
    insert_in_free_list(bp);
    return bp; 

}
//*****End Textbook Code*****

//*****Begin Textbook Code*****
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;
    
  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    
  if (size < 16)
    size = 16;
    
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;
    
  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
  PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    
  /* Coalesce if the previous block was free */
  return coalesce(bp);
}
//*****End Textbook Code*****

static void *find_fit(size_t asize){
  void *bp = free_list_start;
  if (asize == 0) {
      bp = extend_heap(WSIZE);
      return bp;
  }
  while (GET_ALLOC(HDRP(bp)) == 0) {
    if (asize <= GET_SIZE(HDRP(bp))) {
      return bp;
    }
    bp = GET_NEXT_PTR(bp);
  }
  return NULL;
}

static void place(void *bp, size_t asize) {
  size_t csize = GET_SIZE(HDRP(bp));
    
  if ((csize - asize) >= 4 * WSIZE) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    remove_from_free_list(bp);
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
    coalesce(bp);
  }
  else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    remove_from_free_list(bp);
  }
}

static void insert_in_free_list(void *bp){
  SET_NEXT_PTR(bp, free_list_start); //make bp's next pointer  point to the old first element in the list
  SET_PREV_PTR(free_list_start, bp); //make the old first element's previous pointer point to bp
  SET_PREV_PTR(bp, NULL); //make bp's previous pointer point to null
  free_list_start = bp; //make bp the start of the list
}

static void remove_from_free_list(void *bp){
  //Get bp's previous and next pointers
  void* prev_pointer = GET_PREV_PTR(bp);
  void* next_pointer = GET_NEXT_PTR(bp);

  //If bp is not at the start of the list, have the previous pointer point to the next pointer 
  if (prev_pointer)
    SET_NEXT_PTR(prev_pointer, next_pointer);

  //If bp is at the start of the list, have the start now be the next pointer
  else
    free_list_start = next_pointer;

  //Make next's previous pointer point to bp's old previous pointer
  SET_PREV_PTR(next_pointer, prev_pointer);
}

/*
 * mm_init - initialize the malloc package.
 */
//*****Begin Textbook Code*****
int mm_init(void)
{
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(8*WSIZE)) == (void *)-1) //changed 4*WSIZE to 8*WSIZE
    return -1;
    
  PUT(heap_listp, 0); /* Alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
  free_list_start = heap_listp + 2 * WSIZE;  //not included in textbook code
  heap_listp += 2*WSIZE;
    
  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    return -1;
  return 0;
}
//*****End Textbook Code*****

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
//*****Begin Textbook Code*****
void *mm_malloc(size_t size)
{
  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  void *bp;
    
  /* Ignore spurious requests. */
  if (size == 0)
    return (NULL);
    
  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
    
  /* Search the free list for a fit. */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return (bp);
  }
    
  /* No fit found.  Get more memory and place the block. */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return (NULL);
  place(bp, asize);

  //if (CHECK && CHECK_MALLOC)
  //mm_check('a', bp, checksize);

  return (bp);
}
//*****End Textbook Code*****

/*
 * mm_free - Freeing a block does nothing.
 */
//*****Begin Textbook Code*****
void mm_free(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));
  if (bp == NULL)
    return;
    
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);

  // if (CHECK && CHECK_FREE)
  //  mm_check('f', bp, size);
}
//*****End Textbook Code*****

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
  if((int)size < 0)
    return NULL;
  else if((int)size == 0){
    mm_free(bp);
    return NULL;
  }
  else if(size > 0){
    size_t oldsize = GET_SIZE(HDRP(bp));
    size_t newsize = size + 2 * WSIZE; // 2 words for header and footer
    /*if newsize is less than oldsize then we just return bp */
    if(newsize <= oldsize){
      return bp;
    }
    /*if newsize is greater than oldsize */
    else {
      size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
      size_t csize;
      /* next block is free and the size of the two blocks is greater than or equal the new size  */
      /* then we only need to combine both the blocks  */
      if(!next_alloc && ((csize = oldsize + GET_SIZE(  HDRP(NEXT_BLKP(bp))  ))) >= newsize){
	remove_from_free_list(NEXT_BLKP(bp));
	PUT(HDRP(bp), PACK(csize, 1));
	PUT(FTRP(bp), PACK(csize, 1));
	return bp;
      }
      else {
	void *new_ptr = mm_malloc(newsize);
	place(new_ptr, newsize);
	memcpy(new_ptr, bp, newsize);
	mm_free(bp);
	return new_ptr;
      }
    }
  }
  else
    return NULL;
}
