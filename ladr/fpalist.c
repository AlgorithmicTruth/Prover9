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

#include "fpalist.h"

/* Private definitions and types */

/*
   April 2004.  This if the new code for inserting/deleting/traversing
   FPA lists.  It should function exactly the same as the old code,
   except that deletions should be much faster, and memory usage will
   be somewhat different (not much).

   Instead of a (singly-linked) list of pointers to terms, we have a
   (singly-linked) list of *arrays* of pointers to terms.  As before,
   the terms are kept in decreasing order.  Recall that in practice,
   terms being inserted will usually be greater than anything already
   in the list.

   The design is determined by the following properties of the
   application:  (1) items will usually be inserted in
   increasing order, (2) the lists will be traversed, and the
   items must be kept in decreasing order, and (3) deletions
   will be arbitrary and occasionally extensive.

   March 2005.  Code changed so that the size of the chunks
   starts small and increases as needed.  When the number of
   chunks in an fpa list grows to be the same as the chunksize,
   the list is reconstructed, doubling the chunksize (and halving
   the number of chunks).  (Chunk sizes are never made smaller.)
*/

#define F_INITIAL_SIZE 4  /* initial size of chunks  (they double as needed) */
#define F_MAX_SIZE 512    /* maximum size of chunks */

/*
 * memory management
 */

#define PTRS_FPA_CHUNK PTRS(sizeof(struct fpa_chunk))
static unsigned Fpa_chunk_gets, Fpa_chunk_frees;

#define PTRS_FPA_LIST PTRS(sizeof(struct fpa_list))
static unsigned Fpa_list_gets, Fpa_list_frees;

static unsigned Chunk_mem;  /* keep track of memory (pointers) for chunks */

/*************
 *
 *   Fpa_chunk get_fpa_chunk()
 *
 *************/

static
Fpa_chunk get_fpa_chunk(int n)
{
  Fpa_chunk p = get_cmem(PTRS_FPA_CHUNK);
  p->d = get_cmem(n);
  Chunk_mem += n;
  p->size = n;
  Fpa_chunk_gets++;
  return(p);
}  /* get_fpa_chunk */

/*************
 *
 *    free_fpa_chunk()
 *
 *************/

static
void free_fpa_chunk(Fpa_chunk p)
{
  Chunk_mem -= p->size;
  free_mem(p->d, p->size);
  free_mem(p, PTRS_FPA_CHUNK);
  Fpa_chunk_frees++;
}  /* free_fpa_chunk */

/*************
 *
 *   Fpa_list get_fpa_list()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Fpa_list get_fpa_list()
{
  Fpa_list p = get_cmem(PTRS_FPA_LIST);
  p->chunksize = F_INITIAL_SIZE;
  Fpa_list_gets++;
  return(p);
}  /* get_fpa_list */

/*************
 *
 *    free_fpa_list()
 *
 *************/

static
void free_fpa_list(Fpa_list p)
{
  free_mem(p, PTRS_FPA_LIST);
  Fpa_list_frees++;
}  /* free_fpa_list */

/*************
 *
 *   fprint_fpalist_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for data types
associated with the fpalist package.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_fpalist_mem(FILE *fp, BOOL heading)
{
  int n;
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");

  n = sizeof(struct fpa_chunk);
  fprintf(fp, "fpa_chunk (%4d)    %11u%11u%11u%9.1f K\n",
          n, Fpa_chunk_gets, Fpa_chunk_frees,
          Fpa_chunk_gets - Fpa_chunk_frees,
          ((Fpa_chunk_gets - Fpa_chunk_frees) * n) / 1024.);

  n = sizeof(struct fpa_list);
  fprintf(fp, "fpa_list (%4d)     %11u%11u%11u%9.1f K\n",
          n, Fpa_list_gets, Fpa_list_frees,
          Fpa_list_gets - Fpa_list_frees,
          ((Fpa_list_gets - Fpa_list_frees) * n) / 1024.);
  fprintf(fp, "      fpa_list chunks:                               %9.1f K\n",
	  Chunk_mem * BYTES_POINTER / 1024.); 

}  /* fprint_fpalist_mem */

/*************
 *
 *   p_fpalist_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) memory usage statistics for data types
associated with the fpalist package.
*/

/* PUBLIC */
void p_fpalist_mem()
{
  fprint_fpalist_mem(stdout, TRUE);
}  /* p_fpalist_mem */

/*
 *  end of memory management
 */

/* First and last items in chunk.  Items are right-justified. */

#define FLAST(f) (f)->d[(f)->size - 1]
#define FFIRST(f) (f)->d[(f)->size - (f)->n]

/*************
 *
 *   double_chunksize()
 *
 *************/

static
Fpa_chunk double_chunksize(Fpa_chunk f)
{
  if (f == NULL)
    return NULL;
  else if (f->next == NULL) {
    fatal_error("double_chunksize, parity error");
    return NULL;
  }
  else {
    int newsize = f->size * 2;
    Fpa_chunk g = f->next;
    Fpa_chunk new = get_fpa_chunk(newsize);
    /* put f and g terms into new, free f and g, return new */
    int i = newsize - (f->n + g->n);
    int j;
    for (j = f->size - f->n; j < f->size; j++)
      new->d[i++] = f->d[j];
    for (j = g->size - g->n; j < g->size; j++)
      new->d[i++] = g->d[j];
    new->n = f->n + g->n;
    new->head = f->head;
    new->next = double_chunksize(g->next);
    free_fpa_chunk(f);
    free_fpa_chunk(g);
    return new;
  }
}  /* double_chunksize */

/*************
 *
 *   flist_insert()
 *
 *   If the item is greater than any in the list, insertion should
 *   be constant time.
 *
 *************/

static
Fpa_chunk flist_insert(Fpa_chunk f, Term x, Fpa_list head)
{
  /* Iterative version.  link points to the next-field leading to cur
     (NULL when cur is the head of the list). */
  Fpa_chunk *link = NULL;
  Fpa_chunk cur = f;

  while (1) {
    if (cur == NULL) {
      cur = get_fpa_chunk(head->chunksize);
      head->num_chunks++;
      FLAST(cur) = x;
      cur->n = 1;
      if (link) *link = cur; else f = cur;
      return f;
    }

    if (cur->n == cur->size) {
      /* chunk is full */
      if (FLT(x, FLAST(cur))) {
	/* x belongs further down the list */
	link = &cur->next;
	cur = cur->next;
	continue;
      }
      if (x == FLAST(cur))
	fatal_error("flist_insert, item already here (1)");

      if (FGT(x, FFIRST(cur))) {
	/*
	  This special case isn't necessary.  It is to improve performance.
	  The application for which I'm writing this inserts items in
	  increasing order (most of the time), and this prevents a lot of
	  half-empty chunks in that case.
	*/
	Fpa_chunk f2 = get_fpa_chunk(head->chunksize);
	head->num_chunks++;
	FLAST(f2) = x;
	f2->n = 1;
	f2->next = cur;
	if (link) *link = f2; else f = f2;
	return f;
      }

      /* split this chunk in half (new chunk has same size) */
      {
	Fpa_chunk f2 = get_fpa_chunk(cur->size);
	int move = f2->size / 2;
	int i, j;
	head->num_chunks++;
	for (i = 0, j = cur->size - move; i < move; i++, j++) {
	  f2->d[j] = cur->d[i];
	  cur->d[i] = NULL;
	}
	f2->n = move;
	cur->n = cur->size - move;
	f2->next = cur;
	if (link) *link = f2; else f = f2;
	/* Restart insertion from f2 (now half-full) */
	cur = f2;
	continue;
      }
    }

    /* chunk not full */
    if (cur->next && FLE(x, FFIRST(cur->next))) {
      /* x belongs in a later chunk */
      link = &cur->next;
      cur = cur->next;
      continue;
    }

    /* insert into this chunk */
    {
      int n = cur->n;
      int i = cur->size - n;
      while (i < cur->size && FLT(x, cur->d[i]))
	i++;

      if (i < cur->size && x == cur->d[i])
	fatal_error("flist_insert, item already here (2)");

      if (i == cur->size - n) {
	cur->d[i-1] = x;
	cur->n = n+1;
      }
      else {
	/* insert at i-1, shifting the rest */
	int j;
	for (j = cur->size - n; j < i; j++)
	  cur->d[j-1] = cur->d[j];
	cur->d[i-1] = x;
	cur->n = n+1;
      }
      return f;
    }
  }
}  /* flist_insert */

/*************
 *
 *   fpalist_insert()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void fpalist_insert(Fpa_list p, Term t)
{
  p->chunks = flist_insert(p->chunks, t, p);
  p->num_terms++;

#if 0
  printf("insert %p, %d chunks of size %d, %d terms\n",
	 p, p->num_chunks, p->chunksize, p->num_terms);
#endif

  if (p->num_chunks == p->chunksize && p->chunksize < F_MAX_SIZE) {
#if 0
    printf("doubling %p chunksize from %d to %d (%d chunks, density=%.2f)\n",
	   p,
	   p->chunksize, p->chunksize * 2, p->num_chunks,
	   p->num_terms / (double) (p->num_chunks * p->chunksize));
#endif
    p->chunks = double_chunksize(p->chunks);
    p->chunksize = p->chunksize * 2;
    p->num_chunks = p->num_chunks / 2;
  }
}  /* fpalist_insert */

/*************
 *
 *   consolidate() - try to join f and f->next; not recursive
 *
 *************/

static
Fpa_chunk consolidate(Fpa_chunk f, Fpa_list head)
{
  if (f->next && f->n + f->next->n <= f->size) {
    Fpa_chunk f2 = f->next;
    int i;
    for (i = 0; i < f->n; i++)
      f2->d[f->size - (f2->n + i + 1)] = f->d[f->size - (i+1)];
    f2->n = f->n + f2->n;
    free_fpa_chunk(f);
    head->num_chunks--;
    return f2;
  }
  else
    return f;
}  /* consolidate */

/*************
 *
 *   flist_delete()
 *
 *************/

static
Fpa_chunk flist_delete(Fpa_chunk f, Term x, Fpa_list head)
{
  /* Iterative: walk chunks to find x, then delete it. */
  Fpa_chunk *link = NULL;  /* &prev->next, or NULL for head */
  Fpa_chunk cur = f;

  /* Walk to the chunk containing x */
  while (cur != NULL && FLT(x, FLAST(cur))) {
    link = &cur->next;
    cur = cur->next;
  }

  if (cur == NULL)
    fatal_error("flist_delete, item not found (1)");

  {
    int n = cur->n;
    int i = cur->size - n;
    int j;
    while (i < cur->size && FLT(x, cur->d[i]))
      i++;
    if (x != cur->d[i])
      fatal_error("flist_delete, item not found (2)");

    /* delete and close the hole */
    for (j = i; j > cur->size - n; j--)
      cur->d[j] = cur->d[j-1];
    cur->d[j] = NULL;
    cur->n = n - 1;
    if (cur->n == 0) {
      Fpa_chunk next = cur->next;
      head->num_chunks--;
      free_fpa_chunk(cur);
      cur = next;
    }
    else {
      cur = consolidate(cur, head);
    }
    if (link) *link = cur; else f = cur;
  }
  return f;
}  /* flist_delete */

/*************
 *
 *   fpalist_delete()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void fpalist_delete(Fpa_list p, Term t)
{
  p->chunks = flist_delete(p->chunks, t, p);
  p->num_terms--;
#if 0
  printf("delete %p, %d chunks of size %d, %d terms\n",
	 p, p->num_chunks, p->chunksize, p->num_terms);
#endif
}  /* fpalist_delete */

/*************
 *
 *   first_fpos()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
struct fposition first_fpos(Fpa_list f)
{
  return next_fpos((struct fposition) {f->chunks, -1});
}  /* first_fpos */

/*************
 *
 *   next_fpos()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
struct fposition next_fpos(struct fposition p)
{
  if (p.f == NULL)
    return (struct fposition) {NULL, 0};
  else if (p.i == -1)
    return (struct fposition) {p.f, p.f->size - p.f->n};
  else {
    int i = p.i+1;
    
    if (i < (p.f)->size)
      return (struct fposition) {p.f, i};
    else
      return next_fpos((struct fposition) {(p.f)->next, -1});
  }
}  /* next_fpos */

/*************
 *
 *   zap_fpa_chunks()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void zap_fpa_chunks(Fpa_chunk p)
{
  while (p != NULL) {
    Fpa_chunk next = p->next;
    free_fpa_chunk(p);
    p = next;
  }
}  /* zap_fpa_chunks */

/*************
 *
 *   zap_fpalist()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void zap_fpalist(Fpa_list p)
{
  zap_fpa_chunks(p->chunks);
  free_fpa_list(p);
}  /* zap_fpalist */

/*************
 *
 *   fpalist_empty()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL fpalist_empty(Fpa_list p)
{
  return !p || p->chunks == NULL;
}  /* fpalist_empty */

/*************
 *
 *   p_fpa_list()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void p_fpa_list(Fpa_chunk c)
{
  for (; c; c = c->next) {
    int i;
    /* terms right justified in chunk */
    for (i = c->size-c->n; i < c->size; i++) {
      Term t = c->d[i];
      printf(" : ");
      fprint_term(stdout, t);
    }
  }
}  /* p_fpa_list */

/*************
 *
 *   fpalist_build()
 *
 *   Build an Fpa_list from an array of Term pointers already sorted
 *   in decreasing FPA_ID order.  This is O(n) — no per-element
 *   insertion, no sorting, no chunk splitting.  Used for fast
 *   checkpoint restore of serialized FPA indexes.
 *
 *************/

/* PUBLIC */
Fpa_list fpalist_build(Term *terms, int n)
{
  Fpa_list p = get_fpa_list();
  int chunksize, remaining, pos;

  if (n == 0) return p;

  /* Choose chunk size: double from F_INITIAL_SIZE until it covers n,
     but cap at F_MAX_SIZE.  This mirrors what fpalist_insert would
     end up with after n insertions. */
  chunksize = F_INITIAL_SIZE;
  while (chunksize < F_MAX_SIZE && chunksize * chunksize < n)
    chunksize *= 2;
  p->chunksize = chunksize;

  /* Build chunks from the front of the array (highest FPA_IDs first,
     which is how the decreasing-order list is structured). */
  remaining = n;
  pos = 0;
  while (remaining > 0) {
    int fill = (remaining < chunksize) ? remaining : chunksize;
    Fpa_chunk c = get_fpa_chunk(chunksize);
    int i;
    /* Right-justify: items go in d[chunksize-fill .. chunksize-1] */
    for (i = 0; i < fill; i++)
      c->d[chunksize - fill + i] = terms[pos + i];
    c->n = fill;
    c->head = p;
    /* Prepend — we'll reverse after the loop so chunks are in order */
    c->next = p->chunks;
    p->chunks = c;
    p->num_chunks++;
    pos += fill;
    remaining -= fill;
  }

  /* Reverse chunk list so first chunk has highest FPA_IDs */
  {
    Fpa_chunk prev = NULL, cur = p->chunks, next;
    while (cur) {
      next = cur->next;
      cur->next = prev;
      prev = cur;
      cur = next;
    }
    p->chunks = prev;
  }

  p->num_terms = n;
  return p;
}  /* fpalist_build */

