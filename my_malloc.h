#ifndef MY_MALLOC_H
#define MY_MALLOC_H

#include <stdint.h>
#include <sys/types.h>

#ifndef ARENA_SIZE
#define ARENA_SIZE (4096)
#endif

#define MIN_ALLOCATION (sizeof(header))

#if INTPTR_MAX == INT64_MAX
#define NUM_LISTS (64)
#elif INTPTR_MAX == INT32_MAX
#define NUM_LISTS (32)
#endif

#define ALLOC_HEADER_SIZE (sizeof(header) - (2 * sizeof(header *)))

#define UNALLOC_HEADER_SIZE (sizeof(header))

#define TRUE_SIZE(x) ((x -> size) & ~0b111)

#define STATUS(x) ((x -> size) & 0b111)

#define SET_STATUS(x, _state) (x->size = (((x -> size) & ~0b111) | (_state)))

#define SET_SIZE(x, _size) (x->size = ((_size) | ((x -> size) & 0b111)))

#define LOG_2(x) \
    ({ \
        int _count_ = 0; \
        size_t _temp_ = x; \
        while (_temp_ >>= 1) \
            _count_++; \
        _count_; \
    })

#define ORDER(x) ((int)LOG_2(TRUE_SIZE(x)))


#define MIN_SIZE (sizeof(header))

/* The 3 least significant bits in
 * the block size field are used
 * to store allocation state.
 */

typedef enum state {
  UNALLOCATED = 0b000,
  ALLOCATED = 0b001,
  FENCEPOST = 0b010,
} state;

typedef struct header {

  /* Size variable based upon assumption
   * that header takes ALLOC_HEADER_SIZE
   */

  size_t size;
  struct header *chunk;
  union {
    struct {
      struct header *next;
      struct header *prev;
    };
    void *data;
  };
} header;

/* Variations of the malloc function.
 * You only need to implement malloc and free.
 */

void *my_malloc(size_t size);
void *my_calloc(size_t nmemb, size_t size);
void *my_realloc(void *ptr, size_t size);
void my_free(void *p);

/*
 * Helper functions for allocating a block
 */

static void insert_free_block(header *h);
static void set_fenceposts(void *mem, size_t size);

/*
 * Library initialization
 */

static void init();

/*
 * Global variable declarations
 */

extern header *g_freelists[NUM_LISTS];
extern header *g_last_left_fence_post;
extern header *g_last_right_fence_post;
extern void *g_base;
extern void *g_heap_end;

#endif
