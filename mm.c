/*
Autor: Paweł Borek indeks 324938
Oświadczam, że jestem jedynym autorem kodu źródłowego poza fragemnatami wziętymi
z mm-implicit.c
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) */

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */
typedef int64_t dword_t;

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */

/* --=[ boundary tag handling ]=-------------------------------------------- */
// z mm-implicit.c

static inline word_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  debug("[bt_footer]: bt_size(bt)=%d bt=%ld\n", bt_size(bt), (size_t)bt);
  return (void *)(bt - 1) + bt_size(bt);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  debug("[bt_make]: size=%d flags=%d bt=%ld \n", (word_t)size, flags,
        (size_t)bt);
  *bt = size | flags;
  debug("[bt_make]: size=%d flags=%d \n", bt_size(bt), flags);
  if (bt_free(bt))
    *bt_footer(bt) = *bt;
  debug("===========\n");
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of payload. */
static inline void *bt_payload(word_t *bt) {
  return bt + 1;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  return bt == last ? NULL : (void *)bt + bt_size(bt);
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  return bt == heap_start ? NULL : (void *)bt - bt_size(bt - 1);
}

/* --=[ miscellanous procedures ]=------------------------------------------ */
// z mm-implicit.c

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return (sizeof(word_t) + size + ALIGNMENT - 1) & -ALIGNMENT;
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  heap_end = ptr + size;
  return ptr;
}

/* --=[ list of free blocks ]=---------------------------------------------- */

#define ONE_SIZE_CLASSES 8
#define RANGE_SIZE_CLASSES 3
#define SIZE_CLASSES (ONE_SIZE_CLASSES + RANGE_SIZE_CLASSES)

static word_t *lists;

static inline word_t *size_class(word_t bsize) {
  word_t res = bsize / ALIGNMENT;

  if (res > ONE_SIZE_CLASSES) {
    res = ONE_SIZE_CLASSES;
    word_t csize = ONE_SIZE_CLASSES * ALIGNMENT;
    while (csize < bsize && res < SIZE_CLASSES) {
      csize <<= 1;
      res++;
    }
  }

  return (void *)lists + (res - 1) * blksz(0);
}

static inline word_t *get_list(word_t *blk_ptr) {
  return size_class(bt_size(blk_ptr));
}

static inline word_t *next_node(word_t *blk_ptr) {
  return !*(blk_ptr + 1) ? NULL : (void *)blk_ptr + *(blk_ptr + 1);
}

static inline word_t *prev_node(word_t *blk_ptr) {
  return !*(blk_ptr + 2) ? NULL : (void *)blk_ptr + *(blk_ptr + 2);
}

static inline void make_node(word_t *blk_ptr, word_t *prev_ptr,
                             word_t *next_ptr) {
  assert(bt_free(blk_ptr));
  *(blk_ptr + 1) = !(next_ptr) ? 0 : (void *)next_ptr - (void *)blk_ptr;
  *(blk_ptr + 2) = !(prev_ptr) ? 0 : (void *)prev_ptr - (void *)blk_ptr;
}

static inline void put_front(word_t *blk_ptr) {
  if (bt_size(blk_ptr) == ALIGNMENT)
    return;
  word_t *head = get_list(blk_ptr);
  word_t *next = next_node(head);

  make_node(blk_ptr, head, next);
  make_node(head, NULL, blk_ptr);
  if (next)
    make_node(next, blk_ptr, next_node(next));
}

static inline void remove_node(word_t *blk_ptr) {
  if (bt_size(blk_ptr) == ALIGNMENT)
    return;

  word_t *prev = prev_node(blk_ptr);
  word_t *next = next_node(blk_ptr);

  if (prev)
    make_node(prev, prev_node(prev), next);
  if (next)
    make_node(next, prev, next_node(next));
}

/* --=[ mm_init ]=---------------------------------------------------------- */

int mm_init(void) {

  void *ptr = morecore((2 + SIZE_CLASSES) * blksz(0) - sizeof(word_t));
  if (!ptr)
    return -1;

  lists = ptr + 12;
  last = heap_start = (void *)lists + SIZE_CLASSES * blksz(0);

  for (word_t *curr = lists; curr != heap_start; curr = bt_next(curr)) {
    bt_make(curr, blksz(0), FREE);
    make_node(curr, NULL, NULL);
  }

  bt_make(last, blksz(0), FREE);
  put_front(last);

  return 0;
}

/* --=[ malloc ]=----------------------------------------------------------- */

/* [too_big] -> [fitted(used)][reminder(free)] */
static void shrink(word_t *blk_ptr, size_t reqsz) {
  size_t total_size = bt_size(blk_ptr);

  bt_flags flags = USED | bt_get_prevfree(blk_ptr);

  if (total_size < reqsz + blksz(0))
    /* remider is too small to store a free block */
    bt_make(blk_ptr, total_size, flags);
  else {
    bt_make(blk_ptr, reqsz, flags);
    word_t *next_ptr = (void *)blk_ptr + reqsz;
    bt_make(next_ptr, total_size - reqsz, FREE);
    put_front(next_ptr);
    if ((void *)next_ptr + bt_size(next_ptr) == heap_end)
      last = next_ptr;
    else
      bt_set_prevfree(bt_next(next_ptr));
  }
  if (bt_next(blk_ptr))
    bt_clr_prevfree(bt_next(blk_ptr));
}

static word_t *find_fit(size_t reqsz) {
  for (word_t *class = size_class(reqsz); class != heap_start;
       class = bt_next(class)) {
    word_t *current = next_node(class);

    if (current)
      do {
        if (bt_free(current) && bt_size(current) >= reqsz)
          return current;
      } while ((current = next_node(current)));
  }
  return NULL;
}

void *malloc(size_t size) {
  debug("malloc %ld\n", size);
  size = blksz(size);
  word_t *blk = find_fit(size);

  if (!blk) {
    if (bt_free(last)) {
      blk = last;
      remove_node(blk);
    } else
      blk = heap_end;

    void *old_brk = morecore(size - ((void *)heap_end - (void *)blk));

    if (!old_brk)
      return NULL;

    heap_end = (void *)blk + size;
    bt_make(blk, size, USED);
    last = blk;

    debug("malloc sbrk succ\n");
    return bt_payload(blk);
  }

  debug("malloc w/o sbrk at [%ld]\n", (size_t)blk);
  remove_node(blk);
  bt_make(blk, bt_size(blk), USED);
  shrink(blk, size);
  debug("malloc succ\n");
  return bt_payload(blk);
}

/* --=[ free ]=-------------------------------------------------------------- */

void free(void *ptr) {
  debug("free\n");

  if (!ptr)
    return;

  word_t *beg_ptr = bt_fromptr(ptr);
  word_t *next_ptr = bt_next(beg_ptr);
  word_t size = bt_size(beg_ptr);

  if (next_ptr && bt_free(next_ptr)) {
    size += bt_size(next_ptr);
    remove_node(next_ptr);
    // else
    // bt_set_prevfree(next_ptr);
  }

  if (bt_get_prevfree(beg_ptr)) {
    assert(beg_ptr != heap_start);
    beg_ptr = bt_prev(beg_ptr);
    size += bt_size(beg_ptr);
    assert(!(bt_get_prevfree(beg_ptr)));
    remove_node(beg_ptr);
  }

  bt_make(beg_ptr, size, FREE);
  put_front(beg_ptr);
  if ((void *)beg_ptr + bt_size(beg_ptr) == heap_end)
    last = beg_ptr;
  else
    bt_set_prevfree(bt_next(beg_ptr));

  debug("free succes\n");
}

/* --=[ realloc ]=---------------------------------------------------------- */

void *realloc(void *old_ptr, size_t size) {
  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }

  /* If old_ptr is NULL, then this is just malloc. */
  if (!old_ptr)
    return malloc(size);

  word_t *blk_ptr = bt_fromptr(old_ptr);
  word_t *next_ptr = bt_next(blk_ptr);
  size_t reqsz = blksz(size);
  word_t total_size = bt_size(blk_ptr);

  if (next_ptr && bt_free(next_ptr)) {
    total_size += bt_size(next_ptr);
    remove_node(next_ptr);
  }

  /* Change current block size, if possible */
  if (total_size >= reqsz) {
    bt_make(blk_ptr, total_size, USED | bt_get_prevfree(blk_ptr));
    shrink(blk_ptr, reqsz);
    if ((void *)blk_ptr + bt_size(blk_ptr) == heap_end)
      last = blk_ptr;

    return bt_payload(blk_ptr);
  } else if ((void *)blk_ptr + total_size == (void *)heap_end) {
    /* If we can complete realloc by increasing heap size */
    void *old_brk = morecore(reqsz - total_size);

    if (!old_brk)
      return NULL;

    heap_end = (void *)blk_ptr + reqsz;
    bt_make(blk_ptr, reqsz, USED | bt_get_prevfree(blk_ptr));
    last = blk_ptr;

    return bt_payload(blk_ptr);
  }

  void *new_ptr2 = malloc(reqsz);

  /* If malloc() fails, the original block is left untouched. */
  if (!new_ptr2)
    return NULL;

  /* Copy the old data. */
  size_t old_size = bt_size(blk_ptr) - sizeof(word_t); // size of old payload
  if (size < old_size)
    old_size = size;
  memcpy(new_ptr2, bt_payload(blk_ptr), old_size);

  /* Free the old block. */
  free(bt_payload(blk_ptr));

  return new_ptr2;
}

/* --=[ calloc ]=----------------------------------------------------------- */
// z mm-implicit.c

void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);
  if (new_ptr)
    memset(new_ptr, 0, bytes);
  return new_ptr;
}

/* --=[ mm_checkheap ]=----------------------------------------------------- */

void mm_checkheap(int verbose) {
  /* There are no 2 adjacent free blocks. Prevfree flag is set correctly for
   * every block. */
  if (verbose < 2)
    return;
  static int run = 4;
  int errors = 0;
  word_t *current = heap_start;

  if (bt_get_prevfree(heap_start)) {
    printf("prevfree==true for heap_start\n");
    errors++;
  }

  if ((void *)last + bt_size(last) != heap_end) {
    printf("last+size != heap_end\n");
    printf("last:%ld last_size:%d heap_end:%ld\n", (size_t)last, bt_size(last),
           (size_t)heap_end);
    errors++;
  }

  while (current != last) {
    if (bt_size(current) < ALIGNMENT) {
      printf("-Block too small\n");
      errors++;
    }
    if (!bt_free(current) != !bt_get_prevfree(bt_next(current))) {
      // printf("curr[%ld]last[%ld]\n", (size_t)current, (size_t)last);
      printf("-Incorrect flags. ");
      printf(bt_free(current) ? "[free]<-" : "[used]<-");
      printf(bt_get_prevfree(bt_next(current)) ? "[pfree]\n" : "[pused]\n");
      errors++;
    }
    if (bt_free(current) && bt_free(bt_next(current))) {
      printf("-Two free blocks next to each other.\n");
      errors++;
    }
    current = bt_next(current);
  }
  current = heap_start;
  while (current) {
    if (bt_free(current) && *current != *bt_footer(current)) {
      printf("Invalid footer\n");
      errors++;
    }
    bool found = true;
    if (true && bt_free(current) &&
        bt_size(current) > ALIGNMENT) { // check if node is on the list
      found = false;
      for (word_t *class = lists; class != heap_start; class = bt_next(class))
        for (word_t *curr = next_node(class); curr; curr = next_node(curr)) {
          // printf("looping2 [%ld]\n", (size_t)curr);
          if (curr == current) {
            found = true;
            break;
          }
        }
    }
    if (!found) {
      printf("Free block not on the list.\n");
      errors++;
    }

    current = bt_next(current);
  }

  /* check if every node on the list is free and has correct size */
  for (word_t *class = lists; class != heap_start; class = bt_next(class)) {
    for (word_t *curr = next_node(class); curr; curr = next_node(curr)) {
      // printf("looping2 [%ld]\n", (size_t)curr);
      if (!bt_free(curr)) {
        printf("Used block on the list.\n");
        errors++;
      }
      if (get_list(curr) != class) {
        printf("Block is on a wrong list.\n");
        errors++;
      }
    }
  }

  run++;
  if (errors + 1)
    printf("[%d] errors: %d\n", run, errors);
  current = heap_start;
  if (errors) {
    while (current) {
      printf("[(%ld)", (size_t)current);
      printf(bt_free(current) ? "free(" : "used(");
      printf("%d)]", bt_size(current));

      current = bt_next(current);
    }
    printf("\n");
  }
}
