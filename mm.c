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
	"Malloc Madmen",
	/* Liam Ruiz-Steblein */
	"Liam Ruiz-Steblein",
	/* ldr3 */
	"ldr3",
	/* Jared Duran */
	"Jared Duran",
	/* jad21 */
	"jad21"
};

//Structure for doubly-linked list 
struct pointer_data {
	void *next;
	void *prev;
};
typedef struct pointer_data *Pointers;

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */
#define ALIGNMENT  (sizeof(char) * 8)		  /* Byte alignment size (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(ALIGNMENT - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  

static struct pointer_data *dummy_head;

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Addedfunction prototypes for helper routines: */
static void insert_freeblock(void *bp,  void *where_head);
static void remove_freeblock(void *bp);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

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
	
	void *bp;

	/*creates the memory for the dummy head, prologue & epilogue*/
	if ((heap_listp = mem_sbrk(5*WSIZE)) == (void *)-1)
		return (-1);

	dummy_head = (struct pointer_data *)heap_listp;
	printf("dummy head: %p\n", dummy_head);
	printf("lo heap: %p\n", mem_heap_lo());
	// Put the address of the next node
	PUT(heap_listp, (long)&heap_listp);
	// Put the address of the prev node
	PUT(heap_listp + (1 * WSIZE), (long)&heap_listp);
	// Put prologue hdr, ftr, and epilogue hdr
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (3 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (4 * WSIZE), PACK(0, 1));   /* Epilogue header */

	printf("next adr: %p\n", heap_listp);
	printf("prev adr: %p\n", (heap_listp + (1*WSIZE)));
	printf("pro hdr adr: %p\n", (heap_listp + (2*WSIZE)));
	printf("pro ftr adr: %p\n", ((heap_listp + (3*WSIZE))));
	printf("ep hdr adr: %p\n", (heap_listp + (4*WSIZE)));
	
	printf("next: %p\n", dummy_head->next);
	printf("prev: %p\n", dummy_head->prev);
	printf("pro hdr: %u\n", *(heap_listp + (2*WSIZE)));
	printf("pro ftr: %u\n", *((heap_listp + (3*WSIZE))));
	printf("ep hdr: %u\n", *(heap_listp + (4*WSIZE)));

	heap_listp += (3 * WSIZE);//Aligns the heap pointer between prologue hdr & ftr

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if ((bp = extend_heap(CHUNKSIZE / WSIZE)) == NULL)
		return (-1);
	
	//insert the CHUNKSIZE block into the dummy head (explicit list)
	insert_freeblock(bp, dummy_head);
	printf("freeblock adr: %p\n", bp);
	//bp = (struct pointer_data *)
	printf("freeblock next: %u\n", *((int *)bp));
	printf("freeblock prev: %u\n", *(((int *)bp) + 2));
	printf("dummyhead next: %u\n", *((int *)(heap_listp - (3 * WSIZE))));
	printf("dummyhead prev: %u\n", *((int *)(heap_listp - (2 * WSIZE))));
	//printf("End of mm_init\n");
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
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	printf("enters malloc\n");

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE) // Note, must be 4 words to holds hdrs & ftrs
		asize = 2 * DSIZE;
	else
		asize = (ALIGNMENT * ((size + (ALIGNMENT - 1)) / ALIGNMENT)) + DSIZE;

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		// Remove from free list
		remove_freeblock(bp);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	
	//Try coalescing here first? just a thought (w/ deffered coalescing) during 
	//segragated explicit 
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	// Remove from free list
	remove_freeblock(bp);
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
	void *blockP;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	//Edit so just frees the block (can do coalescing later?)
	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	
	//Add block back into freelist
	blockP = coalesce(bp);
	insert_freeblock(blockP, (heap_listp - (3 * WSIZE)));
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

	// TODO: fix for explicit list

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	newptr = mm_malloc(size);

	/* If realloc() fails, the original block is left untouched.  */
	if (newptr == NULL)
		return (NULL);

	//Don't copy if possible - really expensive operation 

	/* Copy just the old data, not the old header and footer. */
	oldsize = GET_SIZE(HDRP(ptr)) - DSIZE;
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

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 - block after free */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		//removes block after bp from freelist 
		remove_freeblock(NEXT_BLKP(bp));

	} else if (!prev_alloc && next_alloc) {         /* Case 3 - block before free */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		//removes bp's block from freelist 
		remove_freeblock(bp);
	} else {                                        /* Case 4 - both before, after free*/
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
		//remove both bp, block after bp from freelist
		remove_freeblock(NEXT_BLKP(bp));
		remove_freeblock(bp);
	}
	return (bp);
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
	void *bp;

	/*Change: search through free list */
	
	//bp2->next

	/* Search for the first fit. */
	// for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	// 	if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
	// 		return (bp);
	// }
	// Assign to dummy_head->next
	bp = ((struct pointer_data *)(heap_listp - (3 * WSIZE)))->next;
	printf("bp before: %lu\n", *((long *)bp));
	//printf("hp before: %lu\n", *((long *)(heap_listp - (3*WSIZE))));
	while (((char *)bp) != (heap_listp - (3 * WSIZE))) {
		//printf("bp: %lu\n", *(long *)bp);
		//printf("hp before: %lu\n", *((long *)(heap_listp - (3*WSIZE))));
		if (asize <= GET_SIZE(HDRP(bp)))
			return (bp);
		bp = ((struct pointer_data *)&bp)->next;
	}
	/* No fit was found. */
	return (NULL);
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

	//TODO: EDIT FREELIST (if larger and needs to split)

	if ((csize - asize) >= (2 * DSIZE)) { // Large enough to split
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		insert_freeblock(bp, (heap_listp - (3 * WSIZE)));
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}

}

/*
* Requires:
*   
*
* Effects: 
*   Inserts bp after target in the free linked list. 
*
*/
static void
insert_freeblock(void *bp,  void *target) 
{
	//Casts to struct pointer_data * to use next and prev from the struct.

	//sets the successor of target's prev to bp
	((struct pointer_data *)
	    &(((struct pointer_data *)&target)->next))->prev = bp;
	((struct pointer_data *)&bp)->next = ((struct pointer_data *)&target)->next;
	((struct pointer_data *)&bp)->prev = target;
	((struct pointer_data *)&target)->next = bp;

}
/*
* Requires:
*
* Effects: 
*   Removes bp from its free linked list. 
*/
static void 
remove_freeblock(void *bp)
{
	//Casts to struct pointer_data * to use next and prev from the struct.
	((struct pointer_data *)
	    &(((struct pointer_data *)&bp)->prev))->next = ((struct pointer_data *)&bp)->next;
	((struct pointer_data *)
	    &(((struct pointer_data *)&bp)->next))->prev = ((struct pointer_data *)&bp)->prev;
	
}

//Check that everything in freelist is actually free in checking routine 

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

	if ((uintptr_t)bp % ALIGNMENT)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
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
