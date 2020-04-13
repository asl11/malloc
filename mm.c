/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP3e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Team LiLee",
	/* First member's full name */
	"Alexander Li",
	/* First member's NetID */
	"asl11",
	/* Second member's full name (leave blank if none) */
	"Christopher Lee",
	/* Second member's NetID (leave blank if none) */
	"chl4"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(DSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  
static struct block_list **free_list_segregatedp; /* Pointer to first block_list of the free_list.*/  

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* Helper functions that we created. */
static int freelistindex(int size);
static struct block_list *remove_free(void* blockp);

/* Struct for segregated free list */
struct block_list
{
	struct block_list *prev_list;
	size_t size;
	void *pointer;
	struct block_list *next_list;
};

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{
	if ((free_list_segregatedp = mem_sbrk(4 * WSIZE + 16 * sizeof(void*))) == (void*)-1)
		return (-1);

	int i;
	for (i = 0; i < 16; i ++) {
		free_list_segregatedp[i] = NULL;
	}

	heap_listp = ((char *) free_list_segregatedp) + 16 * sizeof(void*);

	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
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
	if ((bp = extend_heap(asize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	size_t size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	struct block_list *add_block;
	void *temp_bp;

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		temp_bp = bp;
		add_block = (struct block_list*) bp;
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		remove_free(NEXT_BLKP(bp));
		temp_bp = bp;
		add_block = (struct block_list*) bp;
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		add_block = remove_free(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		temp_bp = bp;
	} else {                                        /* Case 4 */
		remove_free(NEXT_BLKP(bp));
		add_block = remove_free(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		temp_bp = bp;
	}

	int index = freelistindex(size / WSIZE);
	
	add_block->prev_list = NULL;
	add_block->pointer = temp_bp;
	add_block->next_list = free_list_segregatedp[index];
	if (free_list_segregatedp[index] != NULL) {
		free_list_segregatedp[index]->prev_list = add_block;
	}
	free_list_segregatedp[index] = add_block;
	return (temp_bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	size_t size;
	void *bp;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	/* Coalesce if the previous block was free. */
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
	if (asize % WSIZE != 0)
		printf("Error: you did something wrong");

	int index = freelistindex(asize / WSIZE);

	/* No fit was found. */
	if (free_list_segregatedp[index] == NULL)
		return NULL;

	struct block_list *freep = free_list_segregatedp[index];

	while (freep != NULL) {
		if (freep->size >= asize / WSIZE) {
			if (freep->prev_list != NULL && freep->next_list != NULL) {
				freep->prev_list->next_list = freep->next_list;
				freep->next_list->prev_list = freep->prev_list;
			} else if (freep->prev_list != NULL) {
				freep->next_list->prev_list = freep->prev_list;
				free_list_segregatedp[index] = freep->next_list;
			} else if (freep->next_list != NULL) {
				freep->prev_list->next_list = freep->next_list;
			} else {
				free_list_segregatedp[index] = NULL;
			}
			return freep->pointer;
		} else {
			freep = freep->next_list;
		}
	}

	/* If we go to the next free list, the head is guaranteed to be enough size */
	freep = free_list_segregatedp[index + 1];
	if (freep != NULL) {
		if (freep->next_list != NULL) {
			freep->next_list->prev_list = freep->prev_list;
			free_list_segregatedp[index + 1] = freep->next_list;
		} else {
			free_list_segregatedp[index + 1] = NULL;
		}
		return freep->pointer;
	}

	return NULL;
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   

	if ((csize - asize) >= (2 * DSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));

		
		int index = freelistindex((csize - asize) / WSIZE);
		struct block_list *add_block = (struct block_list*) bp;;
		add_block->prev_list = NULL;
		add_block->pointer = bp;
		add_block->next_list = free_list_segregatedp[index];
		if (free_list_segregatedp[index] != NULL) {
			free_list_segregatedp[index]->prev_list = add_block;
		}
		free_list_segregatedp[index] = add_block;
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{
	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");

	int index = freelistindex(GET_SIZE(HDRP(bp)));
	struct block_list *i = free_list_segregatedp[index];
	while (i != NULL) {
		if (i->pointer == bp) {
			printf("Found %p", bp);
		}
		i = i->next_list;
	}
	printf("Error: %p not in free list", bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	size_t hsize, fsize;
	bool halloc, falloc;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/* 
 * Requires:
 * 	 "bp" is the address of the newly freed block
 * 
 * Effects:
 *   adds the bp to the free list
 */
// static void 
// add_to_free(void *bp) {

// }


/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Prints the correct index for the proper free list for a block of the size of "bp".
 */
static int
freelistindex(int block_size) {
	int index = -1;
	if (block_size < 2) {
		index = 0;
	} else if (block_size < pow(2, 2) && block_size >= 2) {
		index = 1;
	} else if (block_size < pow(2, 3) && block_size >= pow(2, 2)) {
		index = 2;
	} else if (block_size < pow(2, 4) && block_size >= pow(2, 3)) {
		index = 3;
	} else if (block_size < pow(2, 5) && block_size >= pow(2, 4)) {
		index = 4;
	} else if (block_size < pow(2, 6) && block_size >= pow(2, 5)) {
		index = 5;
	} else if (block_size < pow(2, 7) && block_size >= pow(2, 6)) {
		index = 6;
	} else if (block_size < pow(2, 8) && block_size >= pow(2, 7)) {
		index = 7;
	} else if (block_size < pow(2, 9) && block_size >= pow(2, 8)) {
		index = 8;
	} else if (block_size < pow(2, 10) && block_size >= pow(2, 9)) {
		index = 9;
	} else if (block_size < pow(2, 11) && block_size >= pow(2, 10)) {
		index = 10;
	} else if (block_size < pow(2, 12) && block_size >= pow(2, 11)) {
		index = 11;
	} else if (block_size < pow(2, 13) && block_size >= pow(2, 12)) {
		index = 12;
	} else if (block_size < pow(2, 14) && block_size >= pow(2, 13)) {
		index = 13;
	} else if (block_size < pow(2, 15) && block_size >= pow(2, 14)) {
		index = 14;
	} else {
		index = 15;
	}

	return index;
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Removes the given block's pointer from the free list.
 */
static struct block_list*
remove_free(void* blockp) {
	int size = GET_SIZE(HDRP(blockp));
	int index = freelistindex(size / WSIZE);
	struct block_list *removep = free_list_segregatedp[index];

	while (removep != NULL) {
		if (removep->pointer == blockp) {
			if (removep->next_list != NULL && removep->prev_list != NULL) {
				removep->next_list->prev_list = removep->prev_list;
				removep->prev_list->next_list = removep->next_list;
			} else if (removep->next_list != NULL) {
				removep->prev_list->next_list = removep->next_list;
			} else if (removep->prev_list != NULL) {
				removep->next_list->prev_list = removep->prev_list;
			} else {
				free_list_segregatedp[index] = NULL;
			}
			return removep;
		}
	}

	printf("Error: somehow this free block isn't in the free list");
	return removep;
}
