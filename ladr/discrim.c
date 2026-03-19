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

#include "discrim.h"

/* Private definitions and types */

/*
 * memory management
 */

#define PTRS_DISCRIM PTRS(sizeof(struct discrim))
static unsigned Discrim_gets, Discrim_frees;

#define PTRS_DISCRIM_POS PTRS(sizeof(struct discrim_pos))
static unsigned Discrim_pos_gets, Discrim_pos_frees;

/*************
 *
 *   Discrim get_discrim()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Discrim get_discrim(void)
{
  Discrim p = get_cmem(PTRS_DISCRIM);
  Discrim_gets++;
  return(p);
}  /* get_discrim */

/*************
 *
 *    free_discrim()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void free_discrim(Discrim p)
{
#ifndef NO_DISCRIM_HASH
  if (p->kid_hash != NULL)
    free(p->kid_hash);
#endif
  free_mem(p, PTRS_DISCRIM);
  Discrim_frees++;
}  /* free_discrim */

/*************
 *
 *   Discrim_pos get_discrim_pos()
 *
 *************/

/* DOCUMENTATION
The structure is not initialized.
*/

/* PUBLIC */
Discrim_pos get_discrim_pos(void)
{
  Discrim_pos p = get_mem(PTRS_DISCRIM_POS);  /* not initialized */
  Discrim_pos_gets++;
  return(p);
}  /* get_discrim_pos */

/*************
 *
 *    free_discrim_pos()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void free_discrim_pos(Discrim_pos p)
{
  free_mem(p, PTRS_DISCRIM_POS);
  Discrim_pos_frees++;
}  /* free_discrim_pos */

/*************
 *
 *   fprint_discrim_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for data types
associated with the discrim package.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_discrim_mem(FILE *fp, BOOL heading)
{
  int n;
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");

  n = sizeof(struct discrim);
  fprintf(fp, "discrim (%4d)      %11u%11u%11u%9.1f K\n",
          n, Discrim_gets, Discrim_frees,
          Discrim_gets - Discrim_frees,
          ((Discrim_gets - Discrim_frees) * n) / 1024.);

  n = sizeof(struct discrim_pos);
  fprintf(fp, "discrim_pos (%4d)  %11u%11u%11u%9.1f K\n",
          n, Discrim_pos_gets, Discrim_pos_frees,
          Discrim_pos_gets - Discrim_pos_frees,
          ((Discrim_pos_gets - Discrim_pos_frees) * n) / 1024.);

}  /* fprint_discrim_mem */

/*************
 *
 *   p_discrim_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) memory usage statistics for data types
associated with the discrim package.
*/

/* PUBLIC */
void p_discrim_mem(void)
{
  fprint_discrim_mem(stdout, TRUE);
}  /* p_discrim_mem */

/*
 *  end of memory management
 */

/*************
 *
 *   discrim_init()
 *
 *************/

/* DOCUMENTATION
This routine allocates and returns an empty discrimination index.
It can be used for either wild or tame indexing.
*/

/* PUBLIC */
Discrim discrim_init(void)
{
  return get_discrim();
}  /* discrim_init */

/*************
 *
 *   discrim_dealloc(d)
 *
 *************/

/* DOCUMENTATION
This routine frees an empty discrimination index (wild or tame).
*/

/* PUBLIC */
void discrim_dealloc(Discrim d)
{
  if (d->u.kids) {
    fatal_error("discrim_dealloc, nonempty index.");
  }
  else
    free_discrim(d);
}  /* discrim_dealloc */

/*************
 *
 *   zap_discrim_tree()
 *
 *************/

static
void zap_discrim_tree(Discrim d, int n)
{
  /* Iterative DFS using heap-allocated dynamically-grown stack */
  struct zap_frame { Discrim node; int n; };
  int cap = 256;
  int top = 0;
  struct zap_frame *stack = malloc(cap * sizeof(struct zap_frame));
  if (stack == NULL)
    fatal_error("zap_discrim_tree: malloc failed");

  stack[top].node = d;
  stack[top].n = n;
  top++;

  while (top > 0) {
    Discrim cur;
    int cur_n;

    top--;
    cur = stack[top].node;
    cur_n = stack[top].n;

    if (cur_n == 0) {
      zap_plist(cur->u.data);
    }
    else {
      Discrim k = cur->u.kids;
      while (k != NULL) {
	int arity;
	Discrim next_k = k->next;
	if (k->type == AC_ARG_TYPE || k->type == AC_NV_ARG_TYPE)
	  arity = 0;
	else if (DVAR(k))
	  arity = 0;
	else
	  arity = sn_to_arity(k->symbol);
	if (top >= cap) {
	  cap *= 2;
	  stack = realloc(stack, cap * sizeof(struct zap_frame));
	  if (stack == NULL)
	    fatal_error("zap_discrim_tree: realloc failed");
	}
	stack[top].node = k;
	stack[top].n = cur_n + arity - 1;
	top++;
	k = next_k;
      }
    }
    free_discrim(cur);
  }
  free(stack);
}  /* zap_discrim_tree */

/*************
 *
 *   destroy_discrim_tree()
 *
 *************/

/* DOCUMENTATION
This routine frees all the memory associated with a discrimination
index.  It can be used with either wild or tame trees.
*/

/* PUBLIC */
void destroy_discrim_tree(Discrim d)
{
  zap_discrim_tree(d, 1);
}  /* destroy_discrim_tree */

/*************
 *
 *   discrim_empty()
 *
 *************/

/* DOCUMENTATION
This Boolean function checks if a discrimination index is empty.
It can be used with either wild or tame trees.
*/

/* PUBLIC */
BOOL discrim_empty(Discrim d)
{
  return (d == NULL ? TRUE : (d->u.kids == NULL ? TRUE : FALSE));
}  /* discrim_empty */

#ifndef NO_DISCRIM_HASH

static int Discrim_hash_threshold = 999999;  /* disabled by default */

/*
 *  Hash table helpers for rigid child lookup in discrimination trees.
 *  Open-addressing with linear probing, identical pattern to FPA kid_hash.
 *  Only rigid (DRIGID) children are hashed; DVARs are excluded.
 */

/*************
 *
 *   discrim_ht_lookup()
 *
 *************/

/* PUBLIC */
Discrim discrim_ht_lookup(struct discrim_ht *ht, int symbol)
{
  int mask = ht->cap - 1;
  int idx = (unsigned)symbol & mask;
  Discrim e;
  while ((e = ht->e[idx]) != NULL) {
    if (e->symbol == symbol)
      return e;
    idx = (idx + 1) & mask;
  }
  return NULL;
}  /* discrim_ht_lookup */

/*************
 *
 *   discrim_ht_insert()
 *
 *************/

/* PUBLIC */
void discrim_ht_insert(struct discrim_ht *ht, Discrim child)
{
  int mask = ht->cap - 1;
  int idx = (unsigned)child->symbol & mask;
  while (ht->e[idx] != NULL)
    idx = (idx + 1) & mask;
  ht->e[idx] = child;
}  /* discrim_ht_insert */

/*************
 *
 *   discrim_ht_delete()
 *
 *************/

/* PUBLIC */
void discrim_ht_delete(struct discrim_ht *ht, int symbol)
{
  int mask = ht->cap - 1;
  int idx = (unsigned)symbol & mask;
  Discrim e;
  /* Find the entry */
  while ((e = ht->e[idx]) != NULL) {
    if (e->symbol == symbol)
      break;
    idx = (idx + 1) & mask;
  }
  if (e == NULL)
    return;  /* not found */
  /* Remove by shifting back subsequent entries (robin hood deletion) */
  ht->e[idx] = NULL;
  {
    int j = (idx + 1) & mask;
    while (ht->e[j] != NULL) {
      int natural = (unsigned)ht->e[j]->symbol & mask;
      if ((j > idx && (natural <= idx || natural > j)) ||
	  (j < idx && (natural <= idx && natural > j))) {
	ht->e[idx] = ht->e[j];
	ht->e[j] = NULL;
	idx = j;
      }
      j = (j + 1) & mask;
    }
  }
}  /* discrim_ht_delete */

/*************
 *
 *   discrim_ht_build()
 *
 *   Build hash table from existing kids list (rigid children only).
 *   Called when num_kids reaches Discrim_hash_threshold.
 *
 *************/

/* PUBLIC */
void discrim_ht_build(Discrim node)
{
  int cap = Discrim_hash_threshold * 2;
  struct discrim_ht *ht;
  Discrim k;
  int rigid_count = 0;

  /* Count rigid children */
  for (k = node->u.kids; k != NULL; k = k->next) {
    if (!DVAR(k))
      rigid_count++;
  }

  /* Ensure cap is large enough: at least 2 * rigid_count */
  while (cap < rigid_count * 2)
    cap *= 2;

  ht = calloc(1, sizeof(struct discrim_ht) + cap * sizeof(Discrim));
  if (ht == NULL)
    fatal_error("discrim_ht_build: malloc failed");
  ht->cap = cap;
  ht->count = 0;
  for (k = node->u.kids; k != NULL; k = k->next) {
    if (!DVAR(k)) {
      discrim_ht_insert(ht, k);
      ht->count++;
    }
  }
  node->kid_hash = ht;
}  /* discrim_ht_build */

/*************
 *
 *   discrim_ht_resize()
 *
 *   Double hash table capacity and rehash all entries.
 *
 *************/

/* PUBLIC */
void discrim_ht_resize(Discrim node)
{
  struct discrim_ht *old = node->kid_hash;
  int old_cap = old->cap;
  int new_cap = old_cap * 2;
  struct discrim_ht *ht;
  int i;

  ht = calloc(1, sizeof(struct discrim_ht) + new_cap * sizeof(Discrim));
  if (ht == NULL)
    fatal_error("discrim_ht_resize: malloc failed");
  ht->cap = new_cap;
  ht->count = old->count;
  for (i = 0; i < old_cap; i++) {
    if (old->e[i] != NULL)
      discrim_ht_insert(ht, old->e[i]);
  }
  free(old);
  node->kid_hash = ht;
}  /* discrim_ht_resize */

/* PUBLIC */
int get_discrim_hash_threshold(void)
{
  return Discrim_hash_threshold;
}  /* get_discrim_hash_threshold */
#endif

/* PUBLIC */
void set_discrim_hash_threshold(int n)
{
#ifndef NO_DISCRIM_HASH
  Discrim_hash_threshold = (n < 0) ? 999999 : n;
#endif
}  /* set_discrim_hash_threshold */

/* PUBLIC */
#ifdef NO_DISCRIM_HASH
int get_discrim_hash_threshold(void)
{
  return 0;
}  /* get_discrim_hash_threshold */
#endif

