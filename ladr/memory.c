/*  Copyright (C) 2006, 2007 William McCune

    This file is part of the LADR Deduction Library.

    The LADR Deduction Library is free software; you can redistribute it
    and/or modify it under the terms of the GNU General Public License,
    version 2.

    The LADR Deduction Library is distributed in the hope that it will be
    useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with the LADR Deduction Library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
*/

#include "memory.h"
#include "string.h"
#include <unistd.h>
#include <string.h>

#define MALLOC_MEGS        20  /* size of blocks malloced by palloc */
#define DEFAULT_MAX_MEGS  49152  /* 48 GB; change with set_max_megs(n) */
#define MAX_MEM_LISTS     2500 /* number of lists of available nodes */

static void ** M[MAX_MEM_LISTS];

static BOOL Max_megs_check = TRUE;
static int Max_megs = DEFAULT_MAX_MEGS;  /* change with set_max_megs(n) */
static void (*Exit_proc) (void);         /* set with set_max_megs_proc() */

static int Malloc_calls = 0;   /* number of calls to malloc by palloc */

static unsigned long long Bytes_palloced = 0;  /* 64-bit to handle >4GB */

static void *Block = NULL;        /* location returned by most recent malloc */
static void *Block_pos = NULL;    /* current position in block */

static unsigned Mem_calls = 0;
static unsigned Mem_calls_overflows = 0;

#define BUMP_MEM_CALLS {Mem_calls++; if (Mem_calls==0) Mem_calls_overflows++;}

/* Forward declarations for safe allocation functions */
void *safe_malloc(size_t n);
void *safe_calloc(size_t nmemb, size_t size);

/*************
 *
 *    void *palloc(n) -- assume n is a multiple of BYTES_POINTER.
 *
 *************/

static
void *palloc(size_t n)
{
  if (n == 0)
    return NULL;
  else {
    void *chunk;
    size_t malloc_bytes = MALLOC_MEGS*1024*1024;

    if (Block==NULL || Block + malloc_bytes - Block_pos < n) {
      /* First call or not enough in the current block, so get a new block. */
      if (n > malloc_bytes) {
	printf("palloc, n=%d\n", (int) n);
	fatal_error("palloc, request too big; reset MALLOC_MEGS");
      }
      else if (Max_megs_check && (long long)(Malloc_calls+1)*MALLOC_MEGS > Max_megs) {
	if (Exit_proc)
	  (*Exit_proc)();
	else
	  fatal_error("palloc, Max_megs parameter exceeded");
      }
      else {
	Block_pos = Block = safe_malloc(malloc_bytes);
	Malloc_calls++;
	/* safe_malloc handles retry/exit on failure, so Block_pos is valid */
      } 
    }
    chunk = Block_pos; 
    Block_pos += n; 
    Bytes_palloced += n; 
    return(chunk);
  }
}  /* palloc */

/*************
 *
 *   get_cmem()
 *
 *************/

/* DOCUMENTATION
Get a chunk of memory that will hold n pointers (NOT n BYTES).
The memory is initialized to all 0.
*/

/* PUBLIC */
void *get_cmem(unsigned n)
{
  if (n == 0)
    return NULL;
  else {
    void **p = NULL;
    BUMP_MEM_CALLS;
    if (n >= MAX_MEM_LISTS)
      return safe_calloc(n, BYTES_POINTER);
    else if (M[n] == NULL)
      p = palloc(n * BYTES_POINTER);
    else {
      /* the first pointer is used for the avail list */
      p = M[n];
      M[n] = *p;
    }
    {
      int i;
      for (i = 0; i < n; i++)
	p[i] = 0;
    }
    return p;
  }
}  /* get_cmem */

/*************
 *
 *   get_mem()
 *
 *************/

/* DOCUMENTATION
Get a chunk of memory that will hold n pointers (NOT n BYTES).
The memory is NOT initialized.
*/


/* PUBLIC */
void *get_mem(unsigned n)
{
  if (n == 0)
    return NULL;
  else {
    void **p = NULL;
    BUMP_MEM_CALLS;
    if (n >= MAX_MEM_LISTS)
      p = safe_malloc(n * BYTES_POINTER);
    else if (M[n] == NULL)
      p = palloc(n * BYTES_POINTER);
    else {
      /* the first pointer is used for the avail list */
      p = M[n];
      M[n] = *p;
    }
    return p;
  }
}  /* get_mem */

/*************
 *
 *   free_mem()
 *
 *************/

/* DOCUMENTATION
Free a chunk of memory that holds n pointers (not n bytes)
that was returned from a previous get_mem() or get_cmem() call.
*/

/* PUBLIC */
void free_mem(void *q, unsigned n)
{
  if (n == 0)
    ;  /* do nothing */
  else {
    /* put it on the appropriate avail list */
    void **p = q;
    if (n >= MAX_MEM_LISTS)
      safe_free(p);  /* large allocations used safe_malloc/safe_calloc */
    else {
      /* the first pointer is used for the avail list */
      *p = M[n];
      M[n] = p;
    }
  }
}  /* free_mem */

/*************
 *
 *   mlist_length()
 *
 *************/

static
int mlist_length(void **p)
{
  int n;
  for (n = 0; p; p = *p, n++);
  return n;
}  /* mlist_length */

/*************
 *
 *   memory_report()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void memory_report(FILE *fp)
{
  int i;
  fprintf(fp, "\nMemory report, %d @ %d = %lld megs (%s bytes used).\n",
	  Malloc_calls, MALLOC_MEGS, (long long) Malloc_calls * MALLOC_MEGS,
	  comma_num(Bytes_palloced));
  for (i = 0; i < MAX_MEM_LISTS; i++) {
    int n = mlist_length(M[i]);
    if (n != 0)
      fprintf(fp, "List %3d, length %s, %8.1f K\n", i, comma_num(n),
	      (double) i * n * BYTES_POINTER / 1024.);
  }
}  /* memory_report */

/*************
 *
 *    int megs_malloced() -- How many MB have been dynamically allocated?
 *
 *************/

/* DOCUMENTATION
This routine returns the number of megabytes that palloc()
has obtained from the operating system by malloc();
*/

/* PUBLIC */
long long megs_malloced(void)
{
  return (long long) Malloc_calls * MALLOC_MEGS;
}  /* megs_malloced */

/*************
 *
 *   set_max_megs()
 *
 *************/

/* DOCUMENTATION
This routine changes the limit on the amount of memory obtained
from malloc() by palloc().  The argument is in megabytes.
The default value is DEFAULT_MAX_MEGS.
*/

/* PUBLIC */
void set_max_megs(int megs)
{
  Max_megs = (megs == -1 ? INT_MAX : megs);
}  /* set_max_megs */

/*************
 *
 *   set_max_megs_proc()
 *
 *************/

/* DOCUMENTATION
This routine is used to specify the routine that will be called
if max_megs is exceeded.
*/

/* PUBLIC */
void set_max_megs_proc(void (*proc)(void))
{
  Exit_proc = proc;
}  /* set_max_megs_proc */

/*************
 *
 *   bytes_palloced()
 *
 *************/

/* DOCUMENTATION
How many bytes have been allocated by the palloc() routine?
This includes all of the get_mem() calls.
*/

/* PUBLIC */
unsigned long long bytes_palloced(void)
{
  return Bytes_palloced;
}  /* bytes_palloced */

/*************
 *
 *   tp_alloc()
 *
 *************/

/* DOCUMENTATION
Allocate n bytes of memory, aligned on a pointer boundary.
The memory is not initialized, and it cannot be freed.
*/

/* PUBLIC */
void *tp_alloc(size_t n)
{
  /* If n is not a multiple of BYTES_POINTER, round up so that it is. */
  if (n % BYTES_POINTER != 0) {
    n += (BYTES_POINTER - (n % BYTES_POINTER));
  }
  return palloc(n);
}  /* tp_alloc */

/*************
 *
 *   mega_mem_calls()
 *
 *************/

/* DOCUMENTATION
 */

/* PUBLIC */
unsigned mega_mem_calls(void)
{
  return
    (Mem_calls / 1000000) +
    ((UINT_MAX / 1000000) * Mem_calls_overflows);
}  /* mega_mem_calls */

/*************
 *
 *   disable_max_megs()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void disable_max_megs(void)
{
  Max_megs_check = FALSE;
}  /* disable_max_megs */

/*************
 *
 *   enable_max_megs()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void enable_max_megs(void)
{
  Max_megs_check = TRUE;
}  /* enable_max_megs */

/*************
 *
 *   alloc_retry_loop() - Retry allocation with exponential backoff
 *
 *   Wait sequence: 1, 2, 4, 8, 16, 32, 64 minutes
 *   Then prompt user to retry sequence or exit(3)
 *
 *************/

static
void *alloc_retry_loop(void *(*alloc_func)(size_t), size_t n, const char *func_name)
{
  void *p;
  int wait_minutes;
  int response;

  for (;;) {  /* outer loop for user retry */
    /* exponential backoff: 1, 2, 4, 8, 16, 32, 64 minutes */
    for (wait_minutes = 1; wait_minutes <= 64; wait_minutes *= 2) {
      fprintf(stderr, "%s: allocation of %lu bytes failed, "
              "waiting %d minute(s) before retry...\n",
              func_name, (unsigned long)n, wait_minutes);
      fflush(stderr);
      sleep(wait_minutes * 60);
      p = alloc_func(n);
      if (p != NULL)
        return p;
    }

    /* All retries exhausted, prompt user */
    fprintf(stderr, "%s: allocation of %lu bytes failed after all retries.\n",
            func_name, (unsigned long)n);
    fprintf(stderr, "Try retry sequence again? (y/n): ");
    fflush(stderr);

    response = getchar();
    /* consume rest of line */
    while (getchar() != '\n' && !feof(stdin))
      ;

    if (response != 'y' && response != 'Y') {
      fprintf(stderr, "%s: exiting due to memory allocation failure.\n",
              func_name);
      exit(3);
    }
  }
}  /* alloc_retry_loop */

#ifdef DEBUG

/*************
 *
 *   DEBUG mode: Memory tracking and logging variables
 *
 *************/

static BOOL Memory_logging_enabled = FALSE;
static unsigned long long Total_allocated = 0;
static unsigned long long Total_freed = 0;
static unsigned long Alloc_count = 0;
static unsigned long Free_count = 0;

/* Size header stored before each allocation */
#define SIZE_HEADER_SIZE sizeof(size_t)

/*************
 *
 *   enable_memory_logging()
 *
 *************/

/* PUBLIC */
void enable_memory_logging(void)
{
  Memory_logging_enabled = TRUE;
  fprintf(stderr, "MEMORY_LOG: Memory logging enabled\n");
  fflush(stderr);
}  /* enable_memory_logging */

/*************
 *
 *   disable_memory_logging()
 *
 *************/

/* PUBLIC */
void disable_memory_logging(void)
{
  Memory_logging_enabled = FALSE;
}  /* disable_memory_logging */

/*************
 *
 *   memory_logging_summary()
 *
 *************/

/* PUBLIC */
void memory_logging_summary(FILE *fp)
{
  fprintf(fp, "\n");
  fprintf(fp, "============ Memory Logging Summary ============\n");
  fprintf(fp, "Total allocations:   %s calls, %s bytes (%.2f MB)\n",
          comma_num(Alloc_count), comma_num(Total_allocated),
          Total_allocated / (1024.0 * 1024.0));
  fprintf(fp, "Total frees:         %s calls, %s bytes (%.2f MB)\n",
          comma_num(Free_count), comma_num(Total_freed),
          Total_freed / (1024.0 * 1024.0));
  fprintf(fp, "Net allocated:       %s bytes (%.2f MB)\n",
          comma_num(Total_allocated - Total_freed),
          (Total_allocated - Total_freed) / (1024.0 * 1024.0));
  fprintf(fp, "================================================\n");
  fflush(fp);
}  /* memory_logging_summary */

/*************
 *
 *   get_total_allocated()
 *
 *************/

/* PUBLIC */
unsigned long long get_total_allocated(void)
{
  return Total_allocated;
}  /* get_total_allocated */

/*************
 *
 *   get_total_freed()
 *
 *************/

/* PUBLIC */
unsigned long long get_total_freed(void)
{
  return Total_freed;
}  /* get_total_freed */

/*************
 *
 *   safe_malloc() - malloc with NULL check, retry mechanism, and tracking
 *
 *   Allocates extra space for size header to enable tracked frees.
 *
 *************/

/* PUBLIC */
void *safe_malloc(size_t n)
{
  void *p;
  size_t total_size;
  size_t *header;

  if (n == 0)
    return NULL;

  /* Catch negative-int-cast-to-size_t and other overflow bugs. */
  if (n > (unsigned long long)1 << 40) {
    fprintf(stderr,
            "safe_malloc: absurd allocation of %lu bytes "
            "(probable integer overflow)\n", (unsigned long)n);
    exit(3);
  }

  total_size = n + SIZE_HEADER_SIZE;
  p = malloc(total_size);
  if (p == NULL)
    p = alloc_retry_loop(malloc, total_size, "safe_malloc");

  /* Store size in header */
  header = (size_t *)p;
  *header = n;

  /* Update tracking */
  Total_allocated += n;
  Alloc_count++;

  if (Memory_logging_enabled) {
    fprintf(stderr, "MEMORY_LOG: safe_malloc(%lu) = %p [total_alloc=%llu, net=%lld]\n",
            (unsigned long)n, (void *)((char *)p + SIZE_HEADER_SIZE),
            Total_allocated, (long long)(Total_allocated - Total_freed));
    fflush(stderr);
  }

  /* Return pointer past the header */
  return (char *)p + SIZE_HEADER_SIZE;
}  /* safe_malloc */

/*************
 *
 *   calloc_wrapper() - wrapper for calloc to match malloc signature
 *
 *************/

static size_t Calloc_size;  /* used by calloc_wrapper */

static
void *calloc_wrapper(size_t n)
{
  return calloc(n, Calloc_size);
}  /* calloc_wrapper */

/*************
 *
 *   safe_calloc() - calloc with NULL check, retry mechanism, and tracking
 *
 *   Allocates extra space for size header to enable tracked frees.
 *
 *************/

/* PUBLIC */
void *safe_calloc(size_t nmemb, size_t size)
{
  void *p;
  size_t user_bytes;
  size_t total_bytes;
  size_t *header;

  if (nmemb == 0 || size == 0)
    return NULL;

  if (size != 0 && nmemb > (SIZE_MAX - SIZE_HEADER_SIZE) / size)
    fatal_error("safe_calloc: nmemb * size overflow");

  user_bytes = nmemb * size;
  total_bytes = user_bytes + SIZE_HEADER_SIZE;

  /* malloc + memset (calloc can't accommodate the size header) */
  p = malloc(total_bytes);
  if (p == NULL) {
    Calloc_size = 1;
    p = alloc_retry_loop(calloc_wrapper, total_bytes, "safe_calloc");
  }

  /* Store size in header */
  header = (size_t *)p;
  *header = user_bytes;

  /* Zero the user portion (not the header) */
  memset((char *)p + SIZE_HEADER_SIZE, 0, user_bytes);

  /* Update tracking */
  Total_allocated += user_bytes;
  Alloc_count++;

  if (Memory_logging_enabled) {
    fprintf(stderr, "MEMORY_LOG: safe_calloc(%lu, %lu) = %p [total_alloc=%llu, net=%lld]\n",
            (unsigned long)nmemb, (unsigned long)size,
            (void *)((char *)p + SIZE_HEADER_SIZE),
            Total_allocated, (long long)(Total_allocated - Total_freed));
    fflush(stderr);
  }

  /* Return pointer past the header */
  return (char *)p + SIZE_HEADER_SIZE;
}  /* safe_calloc */

/*************
 *
 *   safe_free() - free with tracking
 *
 *   Reads size from header and updates tracking.
 *
 *************/

/* PUBLIC */
void safe_free(void *p)
{
  size_t *header;
  size_t user_size;

  if (p == NULL)
    return;

  /* Get pointer to header (before user data) */
  header = (size_t *)((char *)p - SIZE_HEADER_SIZE);
  user_size = *header;

  /* Update tracking */
  Total_freed += user_size;
  Free_count++;

  if (Memory_logging_enabled) {
    fprintf(stderr, "MEMORY_LOG: safe_free(%p) size=%lu [total_freed=%llu, net=%lld]\n",
            p, (unsigned long)user_size,
            Total_freed, (long long)(Total_allocated - Total_freed));
    fflush(stderr);
  }

  /* Free the actual allocated block (including header) */
  free(header);
}  /* safe_free */

#else /* !DEBUG -- Release mode: no size headers, no tracking */

/*************
 *
 *   Release mode stubs for logging functions
 *
 *************/

/* PUBLIC */
void enable_memory_logging(void)
{
}  /* enable_memory_logging */

/* PUBLIC */
void disable_memory_logging(void)
{
}  /* disable_memory_logging */

/* PUBLIC */
void memory_logging_summary(FILE *fp)
{
}  /* memory_logging_summary */

/* PUBLIC */
unsigned long long get_total_allocated(void)
{
  return 0;
}  /* get_total_allocated */

/* PUBLIC */
unsigned long long get_total_freed(void)
{
  return 0;
}  /* get_total_freed */

/*************
 *
 *   safe_malloc() - malloc with NULL check and retry mechanism
 *
 *************/

/* PUBLIC */
void *safe_malloc(size_t n)
{
  void *p;

  if (n == 0)
    return NULL;

  /* Catch negative-int-cast-to-size_t and other overflow bugs. */
  if (n > (unsigned long long)1 << 40) {
    fprintf(stderr,
            "safe_malloc: absurd allocation of %lu bytes "
            "(probable integer overflow)\n", (unsigned long)n);
    exit(3);
  }

  p = malloc(n);
  if (p == NULL)
    p = alloc_retry_loop(malloc, n, "safe_malloc");

  return p;
}  /* safe_malloc */

/*************
 *
 *   safe_calloc() - calloc with NULL check and retry mechanism
 *
 *************/

static size_t Calloc_size;  /* used by calloc_wrapper */

static
void *calloc_wrapper(size_t n)
{
  return calloc(n, Calloc_size);
}  /* calloc_wrapper */

/* PUBLIC */
void *safe_calloc(size_t nmemb, size_t size)
{
  void *p;

  if (nmemb == 0 || size == 0)
    return NULL;

  if (size != 0 && nmemb > (size_t)(-1) / size)
    fatal_error("safe_calloc: nmemb * size overflow");

  p = calloc(nmemb, size);
  if (p == NULL) {
    Calloc_size = size;
    p = alloc_retry_loop(calloc_wrapper, nmemb, "safe_calloc");
  }

  return p;
}  /* safe_calloc */

/*************
 *
 *   safe_free() - free
 *
 *************/

/* PUBLIC */
void safe_free(void *p)
{
  if (p == NULL)
    return;
  free(p);
}  /* safe_free */

#endif /* DEBUG */
