#include "my_malloc.h"

#include <assert.h>
#include <errno.h>
#include <math.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "printing.h"

/* Pointer to the location of the heap prior to any sbrk calls */
void *g_base = NULL;

/* Pointer to the end of our heap */
void *g_heap_end = NULL;

/* Pointer to the head of the free list */
header *g_freelists[NUM_LISTS] = { NULL };

/* Mutex to ensure thread safety for the freelist */
static pthread_mutex_t g_mutex = { 0 };

/* Counter for sbrk calls */
int g_sbrk_num = 0;

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */

header *g_last_left_fence_post = NULL;
header *g_last_right_fence_post = NULL;

/*
 * Direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */

static void init(void) __attribute__((constructor));

/*
 * Insert a block at the beginning of the freelist.
 * The block is located after its left header, h.
 */

static void insert_free_block(header *h) {
  h->prev = NULL;
  h->next = g_freelists[ORDER(h)];
  if (g_freelists[ORDER(h)] != NULL) {
    g_freelists[ORDER(h)]->prev = h;
  }
  g_freelists[ORDER(h)] = h;
} /* insert_free_block() */

/*
 * Remove a block, h, from the free list it is in.
 */

static void remove_free_block(header *h) {
  if (h->prev != NULL) {
    h->prev->next = h->next;
  }
  if (h->next != NULL) {
    h->next->prev = h->prev;
  }
  if (g_freelists[ORDER(h)] == h) {
    g_freelists[ORDER(h)] = h->next;
  }
  h->next = NULL;
  h->prev = NULL;
} /* remove_free_block() */

/*
 * Instantiates fenceposts at the left and right side of a block.
 */

static void set_fenceposts(void *mem, size_t size) {
  header *left_fence = (header *) mem;
  header *right_fence = (header *) (((char *) mem) + size - ALLOC_HEADER_SIZE);
  SET_SIZE(left_fence, size - (2 * ALLOC_HEADER_SIZE));
  SET_SIZE(right_fence, ALLOC_HEADER_SIZE);
  SET_STATUS(left_fence, FENCEPOST);
  SET_STATUS(right_fence, FENCEPOST);
  left_fence->chunk = (header *) (((char *) left_fence) + ALLOC_HEADER_SIZE);
  //right_fence->chunk = (header *) (((char *) left_fence) + ALLOC_HEADER_SIZE);
} /* set_fenceposts() */

/*
 * Constructor that runs before main() to initialize the library.
 */

__attribute__((constructor))void init() {
  /* Initialize all the free lists */
  for (int i = 0; i < NUM_LISTS; i++) {
    g_freelists[i] = NULL;
  }

  /* Initialize mutex for thread safety */

  pthread_mutex_init(&g_mutex, NULL);

  /* Manually set printf buffer so it won't call malloc */

  setvbuf(stdout, NULL, _IONBF, 0);

  /* Record the starting address of the heap */

  g_base = sbrk(0);

} /* init() */


/*
 * This function calculates the required block size by rounding the
 * needed size up to the next power of two. The parameter size is the
 * amount of memory space requested.
 */

int round_up(int size) {
  // Real size
  size = size + ALLOC_HEADER_SIZE;

  int power = 1;
  // Increment power
  while ((power < size) || (power < MIN_SIZE)) {
    power *= 2;
  }

  return power;
} /* round_up() */

/* This function splits a block until the smallest possible size
 * (given by needed_order) is reached. It returns the block's header.
 */

header * split(header * block, int needed_order) {
  // loop while block size is greater than min size and greater than
  // 2 times needed_order
  while ((TRUE_SIZE(block) > MIN_SIZE) &&
    (TRUE_SIZE(block) >> 1 >= 1 << needed_order)) {
    // Remove whole block, divide size
    remove_free_block(block);
    SET_SIZE(block, TRUE_SIZE(block) / 2);
    // Make new header, set size/status/chunk
    header *buddy_block = (header *)((char *) block + TRUE_SIZE(block));
    SET_SIZE(buddy_block, TRUE_SIZE(block));
    SET_STATUS(buddy_block, UNALLOCATED);
    buddy_block->chunk = block->chunk;
    // Insert free buddy_block and bock which are
    // now half the size of the original blcok
    insert_free_block(buddy_block);
    insert_free_block(block);
  }
  return block;
} /* split() */

/*
 * This function finds a free block for the requested size.
 * If that size doesn't exist it returns NULL.
 */

header * find_block(int size) {
  header * search_free = g_freelists[LOG_2(size)];
  if (search_free != NULL) {
    return search_free;
  } else {
    // Iterate through g_freelists with order > size
    for (int i = LOG_2(size) + 1; i < NUM_LISTS; i++) {
      // Set header iterater to head of current free list
      search_free = g_freelists[i];
      // If it isn't null, it can be used, but may need to be split
      if ((search_free != NULL) && (TRUE_SIZE(search_free) >= size)) {
        // If greater than OR EQUAL to 2 * size, split
        search_free = split(search_free, LOG_2(size));
        return search_free;
      }
    }
  }
  return NULL;
} /* find_block() */

/*
 * This function handles a new sbrk() block (given by address)
 * by setting fenceposts, creating a header for the block,
 * and coalescing if necessary. It returns the new block header.
 */

header * merge_blocks(void * address) {

  // If there has been one sbrk
  if (g_sbrk_num == 1) {

    // Set fenceposts
    set_fenceposts(address, ARENA_SIZE + 2 * ALLOC_HEADER_SIZE);

    // Set header properties
    header * new_block = (header *) ((char *)address + ALLOC_HEADER_SIZE);
    SET_SIZE(new_block, ARENA_SIZE);
    SET_STATUS(new_block, UNALLOCATED);
    new_block->chunk = new_block;

    // Set global fencepost variables
    g_base = address;
    g_last_left_fence_post = (header *)address;
    g_last_right_fence_post = (header *)(((char *)address)
        + ARENA_SIZE + ALLOC_HEADER_SIZE);
    g_last_right_fence_post->chunk = new_block;
    insert_free_block(new_block);
  // If there has been >1 sbrk AND the block is
  // at the end of the heap
  } else if ((g_sbrk_num > 1) && (((char *)address - 1)
        == ((char *) g_heap_end))) {

    // Set fenceposts
    set_fenceposts(g_last_left_fence_post, 2 * TRUE_SIZE(g_last_left_fence_post)
        + 2 * ALLOC_HEADER_SIZE);

    // Set header properties
    header * temp = (header *)(((char *) g_last_left_fence_post)
        + ALLOC_HEADER_SIZE);
    if ((TRUE_SIZE(temp) == TRUE_SIZE(g_last_left_fence_post) / 2)
        && (STATUS(temp) == UNALLOCATED)) {
      remove_free_block(temp);
      SET_SIZE(temp, 2 * TRUE_SIZE(temp));
      insert_free_block(temp);
    } else {
      header * new_block = (header *) ((char *)(g_last_left_fence_post)
          + ALLOC_HEADER_SIZE + TRUE_SIZE(g_last_left_fence_post) / 2);
      SET_STATUS(new_block, UNALLOCATED);
      SET_SIZE(new_block, TRUE_SIZE(g_last_left_fence_post) / 2);
      new_block->chunk = (header *)(((char *) g_last_left_fence_post)
          + ALLOC_HEADER_SIZE);
      insert_free_block(new_block);
    }
    // Set gloabl fencepost variables
    g_last_right_fence_post = (header *)(((char *)g_last_left_fence_post)
        + TRUE_SIZE(g_last_left_fence_post) + ALLOC_HEADER_SIZE);
    g_last_right_fence_post->chunk = (header *)
        (((char *) g_last_left_fence_post)
        + ALLOC_HEADER_SIZE);

  } else if (g_sbrk_num > 1){

    // Set fenceposts
    set_fenceposts(address, TRUE_SIZE(g_last_left_fence_post)
        + (2 * ALLOC_HEADER_SIZE));

    // Set header properties
    header * new_block = (header *) (((char *)address) + ALLOC_HEADER_SIZE);
    SET_SIZE(new_block, TRUE_SIZE(g_last_left_fence_post));
    SET_STATUS(new_block, UNALLOCATED);
    new_block->chunk = new_block;

    // Set global fencepost variables
    g_last_left_fence_post = (header *) address;
    g_last_right_fence_post = (header *)(((char *)address)
        + TRUE_SIZE(g_last_left_fence_post) + ALLOC_HEADER_SIZE);
    g_last_right_fence_post->chunk = new_block;
    insert_free_block(new_block);
  }


} /* merge_blocks() */

/*
 * This function stores data, with a specified size, in memory.
 * It does so by using sbrk to reserve a memory chunk, and the
 * split function to find the smallest possible space to allocate.
 */

void * my_malloc(size_t size) {

  pthread_mutex_lock(&g_mutex);

  // Calculate block size needed
  if (size == 0) {
    pthread_mutex_unlock(&g_mutex);
    return NULL;
  }
  size = round_up(size);

  // Find free block
  header * free = find_block(size);

  // If there is no free / it is too small
  while (free == NULL) {
    // Request chunk of memory from OS
    int chunk_size = 0;

    char * address = (void *) -1;

    // Find chunk size based on sbrk() number, call sbrk()
    if (g_sbrk_num == 0) {
      chunk_size = ARENA_SIZE + (2 * ALLOC_HEADER_SIZE);
      address = sbrk(chunk_size);
      g_sbrk_num += 1;
    } else {
      chunk_size = TRUE_SIZE(g_last_left_fence_post) + 2 * ALLOC_HEADER_SIZE;
      address = sbrk(chunk_size);
      g_sbrk_num += 1;
    }

    // If no address, quit
    if (address == (void *) -1 ) {
      errno = ENOMEM;
      pthread_mutex_unlock(&g_mutex);
      return NULL;
    }

    // Merge blocks if necessary
    merge_blocks(address);

    // Set end of heap
    g_heap_end = (void *) ((char *) address + chunk_size - 1);

    // Find open block to allocate
    free = find_block(size);
  }

  // Remove block from free list, set as allocated
  remove_free_block(free);
  SET_STATUS(free, ALLOCATED);
  free->data = (void *) ((char *) free + ALLOC_HEADER_SIZE);

  pthread_mutex_unlock(&g_mutex);
  return free->data;
} /* my_malloc() */

/*
 * Calls malloc and sets each byte of
 * the allocated memory to a value
 */

void my_free(void * p) {

  pthread_mutex_lock(&g_mutex);

  // If p is null, stop
  if ( p == NULL ){
    pthread_mutex_unlock(&g_mutex);
    return;
  }

  // Get head_address, if unallocated
  header * head_address = (header *)(((char *) p) - ALLOC_HEADER_SIZE);
  if ((head_address == NULL) || (STATUS(head_address) == UNALLOCATED)) {
    pthread_mutex_unlock(&g_mutex);
    assert(false);
  }

  // Set status and data
  SET_STATUS(head_address, UNALLOCATED);
  head_address->data = NULL;
  head_address->next = NULL;
  head_address->prev = NULL;

  // If buddy exists, merge
  //merge_buddys(head_address);
  header * remove_buddy = NULL;

  // Offset and header to find the second buddy
  int offset = (int)(((char *) head_address) - ((char *) head_address->chunk));
  header * buddy_address = (header *)(((char *) head_address->chunk) +
    (offset ^ TRUE_SIZE(head_address)));

  // While second buddy is unallocated AND buddy size < head size
  while ((STATUS(buddy_address) == UNALLOCATED)) {

    // Find first and second budy --> tells which header to keep
    remove_buddy = head_address > buddy_address ? head_address :
      buddy_address;
    head_address = head_address == remove_buddy ? buddy_address :
      head_address;

    // Remove block from free list
    remove_free_block(buddy_address);

    // Set buddy size to double
    SET_SIZE(head_address, 2 * TRUE_SIZE(head_address));
    //SET_STATUS(head_address, UNALLOCATED);

    // Compute next offset and get next second buddy if exists
    offset = (int)(((char *) head_address) - ((char *) head_address->chunk));
    buddy_address = (header *)(((char *) head_address->chunk) +
      (offset ^ TRUE_SIZE(head_address)));
    if (head_address == buddy_address) {
      break;
    }
    header * check = head_address;
    if ((char *)head_address > (char*)buddy_address) {
      check = buddy_address;
    }

    if ((char *) check + 2 * TRUE_SIZE(check) > (char *)g_heap_end) {
      break;
    }
  }

  insert_free_block(head_address);
  pthread_mutex_unlock(&g_mutex);

} /* my_free() */

/*
 * Calls malloc and sets each byte of
 * the allocated memory to a value
 */

void *my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
} /* my_calloc() */

/*
 * Reallocates an allocated block to a new size and
 * copies the contents to the new block.
 */

void *my_realloc(void *ptr, size_t size) {
  void *mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem;
} /* my_realloc() */
