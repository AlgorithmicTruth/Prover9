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

#include "fpa.h"

#include <stdlib.h>

/* NO_INDEX_HASH disables both discrim and FPA hash tables */
#ifdef NO_INDEX_HASH
#ifndef NO_FPA_HASH
#define NO_FPA_HASH
#endif
#endif

/* Private definitions and types */

static unsigned Fpa_id_count = 0;

static unsigned Next_calls = 0;
static unsigned Next_calls_overflows = 0;
#define BUMP_NEXT_CALLS {Next_calls++; if (Next_calls == 0) Next_calls_overflows++;}

/* FPA index statistics */
static unsigned long long Query_special_calls = 0;
static unsigned long long Intersect_merge_ops = 0;

typedef struct fpa_trie * Fpa_trie;

#ifndef NO_FPA_HASH
/*
 * Hash table for fast child lookup.  Stored as a struct with a flexible
 * array of Fpa_trie pointers (open addressing, linear probing).
 * NULL entry = empty slot.
 */
struct kid_ht {
  int cap;        /* always a power of 2 */
  Fpa_trie e[];   /* cap entries */
};

static int Kid_hash_threshold = 4;
#endif

struct fpa_trie {
  Fpa_trie   parent, next, kids;
  int        label;
#ifndef NO_FPA_HASH
  int        num_kids;          /* number of children in kids list */
#endif
  Fpa_list   terms;
#ifndef NO_FPA_HASH
  struct kid_ht *kid_hash;      /* hash table for child lookup, or NULL */
#endif
#ifdef FPA_DEBUG
  Ilist      path;
#endif
};

struct fpa_index {
  Fpa_trie   root;
  int        depth;
  Fpa_index  next;
};

struct fpa_state {
  int              type;
  Fpa_state        left, right;
  Term             left_term, right_term;
  struct fposition fpos;
#ifdef FPA_DEBUG
  Ilist            path;
#endif
};

/* A path is a sequence of integers.  We have to do some operations
   to the end of a path, and an Ilist is singly-linked; but we can
   get away with just keeping a pointer to the end of the list.
 */

struct path {
  Ilist first;
  Ilist last;
};

enum { LEAF, UNION, INTERSECT };  /* types of fpa_state (node in FPA tree) */

/* for a mutual recursion */

static Fpa_state build_query(Term t, Context c, Querytype type,
			     struct path *p, int bound, Fpa_trie index);

/*
 * memory management
 */

#define PTRS_FPA_TRIE PTRS(sizeof(struct fpa_trie))
static unsigned Fpa_trie_gets, Fpa_trie_frees;

#define PTRS_FPA_STATE PTRS(sizeof(struct fpa_state))
static unsigned Fpa_state_gets, Fpa_state_frees;

#define PTRS_FPA_INDEX PTRS(sizeof(struct fpa_index))
static unsigned Fpa_index_gets, Fpa_index_frees;

/*************
 *
 *   Fpa_trie get_fpa_trie()
 *
 *************/

static
Fpa_trie get_fpa_trie(void)
{
  Fpa_trie p = get_cmem(PTRS_FPA_TRIE);
  p->label = -1;
  Fpa_trie_gets++;
  return(p);
}  /* get_fpa_trie */

/*************
 *
 *    free_fpa_trie()
 *
 *************/

static
void free_fpa_trie(Fpa_trie p)
{
#ifndef NO_FPA_HASH
  if (p->kid_hash != NULL)
    free(p->kid_hash);
#endif
  free_mem(p, PTRS_FPA_TRIE);
  Fpa_trie_frees++;
}  /* free_fpa_trie */

#ifndef NO_FPA_HASH
/*
 * Hash table helpers for child lookup (open addressing, linear probing).
 * Capacity is always a power of 2.  NULL entry = empty.
 */

static
Fpa_trie kid_hash_lookup(struct kid_ht *ht, int label)
{
  int mask = ht->cap - 1;
  int idx = (unsigned)label & mask;
  Fpa_trie e;
  while ((e = ht->e[idx]) != NULL) {
    if (e->label == label)
      return e;
    idx = (idx + 1) & mask;
  }
  return NULL;
}  /* kid_hash_lookup */

static
void kid_hash_insert_entry(struct kid_ht *ht, Fpa_trie child)
{
  int mask = ht->cap - 1;
  int idx = (unsigned)child->label & mask;
  while (ht->e[idx] != NULL)
    idx = (idx + 1) & mask;
  ht->e[idx] = child;
}  /* kid_hash_insert_entry */

static
void kid_hash_delete(struct kid_ht *ht, int label)
{
  int mask = ht->cap - 1;
  int idx = (unsigned)label & mask;
  Fpa_trie e;
  /* Find the entry */
  while ((e = ht->e[idx]) != NULL) {
    if (e->label == label)
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
      int natural = (unsigned)ht->e[j]->label & mask;
      /* Check if this entry's natural slot is at or before the gap.
       * In a circular sense: if the entry doesn't belong in its current
       * position without the deleted entry, move it. */
      if ((j > idx && (natural <= idx || natural > j)) ||
	  (j < idx && (natural <= idx && natural > j))) {
	ht->e[idx] = ht->e[j];
	ht->e[j] = NULL;
	idx = j;
      }
      j = (j + 1) & mask;
    }
  }
}  /* kid_hash_delete */

/*
 * Build a hash table from the existing kids linked list.
 * Called when num_kids reaches Kid_hash_threshold.
 */
static
void kid_hash_build(Fpa_trie node)
{
  int cap = Kid_hash_threshold < 2 ? 4 : Kid_hash_threshold * 2;
  struct kid_ht *ht;
  Fpa_trie k;

  /* Ensure cap is large enough: at least 2 * num_kids */
  while (cap < node->num_kids * 2)
    cap *= 2;

  ht = calloc(1, sizeof(struct kid_ht) + cap * sizeof(Fpa_trie));
  if (ht == NULL)
    fatal_error("kid_hash_build: malloc failed");
  ht->cap = cap;
  for (k = node->kids; k != NULL; k = k->next)
    kid_hash_insert_entry(ht, k);
  node->kid_hash = ht;
}  /* kid_hash_build */

/*
 * Resize the hash table (double capacity) and rehash all entries.
 * Called when load factor exceeds 3/4.
 */
static
void kid_hash_resize(Fpa_trie node)
{
  struct kid_ht *old = node->kid_hash;
  int old_cap = old->cap;
  int new_cap = old_cap * 2;
  struct kid_ht *ht;
  int i;

  ht = calloc(1, sizeof(struct kid_ht) + new_cap * sizeof(Fpa_trie));
  if (ht == NULL)
    fatal_error("kid_hash_resize: malloc failed");
  ht->cap = new_cap;
  for (i = 0; i < old_cap; i++) {
    if (old->e[i] != NULL)
      kid_hash_insert_entry(ht, old->e[i]);
  }
  free(old);
  node->kid_hash = ht;
}  /* kid_hash_resize */
#endif

/*************
 *
 *   Fpa_state get_fpa_state()
 *
 *************/

static
Fpa_state get_fpa_state(void)
{
  Fpa_state p = get_cmem(PTRS_FPA_STATE);
  Fpa_state_gets++;
  return(p);
}  /* get_fpa_state */

/*************
 *
 *    free_fpa_state()
 *
 *************/

static
void free_fpa_state(Fpa_state p)
{
  free_mem(p, PTRS_FPA_STATE);
  Fpa_state_frees++;
}  /* free_fpa_state */

/*************
 *
 *   Fpa_index get_fpa_index()
 *
 *************/

static
Fpa_index get_fpa_index(void)
{
  Fpa_index p = get_cmem(PTRS_FPA_INDEX);
  p->depth = -1;
  Fpa_index_gets++;
  return(p);
}  /* get_fpa_index */

/*************
 *
 *    free_fpa_index()
 *
 *************/

static
void free_fpa_index(Fpa_index p)
{
  free_mem(p, PTRS_FPA_INDEX);
  Fpa_index_frees++;
}  /* free_fpa_index */

/*************
 *
 *   fprint_fpa_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for data types
associated with the fpa package.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_fpa_mem(FILE *fp, BOOL heading)
{
  int n;
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");

  n = sizeof(struct fpa_trie);
  fprintf(fp, "fpa_trie (%4d)     %11u%11u%11u%9.1f K\n",
          n, Fpa_trie_gets, Fpa_trie_frees,
          Fpa_trie_gets - Fpa_trie_frees,
          ((Fpa_trie_gets - Fpa_trie_frees) * n) / 1024.);

  n = sizeof(struct fpa_state);
  fprintf(fp, "fpa_state (%4d)    %11u%11u%11u%9.1f K\n",
          n, Fpa_state_gets, Fpa_state_frees,
          Fpa_state_gets - Fpa_state_frees,
          ((Fpa_state_gets - Fpa_state_frees) * n) / 1024.);

  n = sizeof(struct fpa_index);
  fprintf(fp, "fpa_index (%4d)    %11u%11u%11u%9.1f K\n",
          n, Fpa_index_gets, Fpa_index_frees,
          Fpa_index_gets - Fpa_index_frees,
          ((Fpa_index_gets - Fpa_index_frees) * n) / 1024.);

}  /* fprint_fpa_mem */

/*************
 *
 *   p_fpa_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) memory usage statistics for data types
associated with the fpa package.
*/

/* PUBLIC */
void p_fpa_mem()
{
  fprint_fpa_mem(stdout, TRUE);
}  /* p_fpa_mem */

/*
 *  end of memory management
 */

/*************
 *
 *   fprint_path()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) an FPA Path.  A newline is NOT printed.
*/

/* PUBLIC */
void fprint_path(FILE *fp, Ilist p)
{
  int i;
  fprintf(fp, "(");
  for (i = 0; p != NULL; p = p->next, i++) {
    if (i%2 == 0) {
      if (p->i == 0)
	fprintf(fp, "*");
      else
	fprint_sym(fp, p->i);
    }
    else
      fprintf(fp, "%d", p->i);

    if (p->next != NULL)
      fprintf(fp, " ");
  }
  fprintf(fp, ")");
}  /* fprint_path */

/*************
 *
 *   p_path()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) an FPA Path.  A newline is NOT printed.
*/

/* PUBLIC */
void p_path(Ilist p)
{
  fprint_path(stdout, p);
  fflush(stdout);
}  /* p_path */

/*************
 *
 *    fprint_fpa_trie -- Print an FPA trie to stdout.
 *
 *************/

static
void fprint_fpa_trie(FILE *fp, Fpa_trie p, int depth)
{
  /* Iterative DFS using heap-allocated stack */
  struct fpt_frame { Fpa_trie node; int depth; };
  int cap = 1024;
  struct fpt_frame *stack = malloc(cap * sizeof(struct fpt_frame));
  int top = 0;
  int ccap = 1024;
  Fpa_trie *children = malloc(ccap * sizeof(Fpa_trie));

  if (stack == NULL || children == NULL)
    fatal_error("fprint_fpa_trie: malloc failed");

  stack[top].node = p;
  stack[top].depth = depth;
  top++;

  while (top > 0) {
    Fpa_trie cur, q;
    int cur_depth, i, count, j;

    top--;
    cur = stack[top].node;
    cur_depth = stack[top].depth;

    for (i = 0; i < cur_depth; i++)
      fprintf(fp, " - ");
    if (cur_depth == 0)
      fprintf(fp, "root");
    else if (cur_depth % 2 == 1) {
      if (cur->label == 0)
	fprintf(fp, "*");
      else
	fprint_sym(fp, cur->label);
    }
    else
      fprintf(fp, "%2d", cur->label);

    if (cur->terms)
      p_fpa_list(cur->terms->chunks);

#ifdef FPA_DEBUG
    if (cur->path != NULL)
      fprint_path(fp, cur->path);
#endif
    fprintf(fp, "\n");

    /* Collect children, then push in reverse order */
    count = 0;
    for (q = cur->kids; q != NULL; q = q->next) {
      if (count >= ccap) {
	ccap *= 2;
	children = realloc(children, ccap * sizeof(Fpa_trie));
	if (children == NULL)
	  fatal_error("fprint_fpa_trie: realloc failed");
      }
      children[count++] = q;
    }
    for (j = count - 1; j >= 0; j--) {
      if (top >= cap) {
	cap *= 2;
	stack = realloc(stack, cap * sizeof(struct fpt_frame));
	if (stack == NULL)
	  fatal_error("fprint_fpa_trie: realloc failed");
      }
      stack[top].node = children[j];
      stack[top].depth = cur_depth + 1;
      top++;
    }
  }
  free(children);
  free(stack);
}  /* fprint_fpa_trie */

/*************
 *
 *   fprint_fpa_index()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) an Fpa_index.
WARNING: An Fpa_index can be very big, and it is printed as a tree,
so if you use this routine, I suggest trying it on a small index first.
*/

/* PUBLIC */
void fprint_fpa_index(FILE *fp, Fpa_index idx)
{
  fprintf(fp, "FPA/Path index, depth is %d.\n", idx->depth);
  fprint_fpa_trie(fp, idx->root, 0);
}  /* fprint_fpa_index */

/*************
 *
 *   p_fpa_index()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) an Fpa_index.
WARNING: An Fpa_index can be very big, and it is printed as a tree,
so if you use this routine, I suggest trying it on a small index first.
*/

/* PUBLIC */
void p_fpa_index(Fpa_index idx)
{
  fprint_fpa_index(stdout, idx);
}  /* p_fpa_index */

/*************
 *
 *    fpa_trie_member_insert (recursive) -- This routine takes a trie
 *    and a path, and looks for a node in the trie that corresponds
 *    to the path.  If such a node does not exist, it is created, and
 *    the trie is updated.
 *
 *************/

static
Fpa_trie fpa_trie_member_insert(Fpa_trie node, Ilist path)
{
  /* Iterative version -- original is tail-recursive on path list */
  while (path != NULL) {
    int val = path->i;
    Fpa_trie found = NULL;

#ifndef NO_FPA_HASH
    if (node->kid_hash != NULL) {
      /* Fast path: hash table lookup O(1) */
      found = kid_hash_lookup(node->kid_hash, val);
      if (found == NULL) {
	/* Create new child, prepend to kids list, insert into hash table */
	Fpa_trie new = get_fpa_trie();
	new->parent = node;
	new->label = val;
	new->next = node->kids;
	node->kids = new;
	node->num_kids++;
	/* Check if resize needed (load > 3/4) */
	if (node->num_kids > node->kid_hash->cap * 3 / 4)
	  kid_hash_resize(node);
	kid_hash_insert_entry(node->kid_hash, new);
	found = new;
      }
    }
    else
#endif
    {
      /* Linear scan */
      Fpa_trie curr = node->kids;
      while (curr != NULL) {
	if (curr->label == val) {
	  found = curr;
	  break;
	}
	curr = curr->next;
      }
      if (found == NULL) {
	/* Prepend new child (no sorted order needed) */
	Fpa_trie new = get_fpa_trie();
	new->parent = node;
	new->label = val;
	new->next = node->kids;
	node->kids = new;
#ifndef NO_FPA_HASH
	node->num_kids++;
	/* Build hash table if threshold reached */
	if (node->num_kids >= Kid_hash_threshold)
	  kid_hash_build(node);
#endif
	found = new;
      }
    }
    node = found;
    path = path->next;
  }
  return node;
}  /* fpa_trie_member_insert */

/*************
 *
 *    fpa_trie_member (recursive) -- This routine looks for a trie
 *    node that corresponds to a given path.
 *
 *************/

static
Fpa_trie fpa_trie_member(Fpa_trie node, Ilist path)
{
  /* Iterative version -- original is tail-recursive on path list */
  while (path != NULL) {
    int val = path->i;
    Fpa_trie found;

#ifndef NO_FPA_HASH
    if (node->kid_hash != NULL) {
      found = kid_hash_lookup(node->kid_hash, val);
    }
    else
#endif
    {
      Fpa_trie curr;
      found = NULL;
      for (curr = node->kids; curr != NULL; curr = curr->next) {
	if (curr->label == val) {
	  found = curr;
	  break;
	}
      }
    }
    if (found != NULL) {
      node = found;
      path = path->next;
    }
    else
      return NULL;
  }
  return node;
}  /* fpa_trie_member */

/*************
 *
 *    fpa_trie_possible_delete (recursive) -- This routine checks if
 *    a trie node should be deleted.  If so, it is deleted, and a
 *    recursive call is made on the parent node.  The trie node should
 *    be deleted if (1) it is not the root, (2) there is no FPA list,
 *    and (3) it has no children.
 *
 *************/

static
void fpa_trie_possible_delete(Fpa_trie node)
{
  /* Iterative version -- original is tail-recursive up the parent chain.
   * We collect nodes to free, then free them after unlinking.
   */
  Fpa_trie to_free[1000];
  int nfree = 0;

  while (node->parent &&
	 node->terms &&
	 fpalist_empty(node->terms) &&
	 node->kids == NULL) {
    Fpa_trie parent = node->parent;
    /* Unlink from parent's kids list */
    if (parent->kids == node)
      parent->kids = node->next;
    else {
      Fpa_trie p = parent->kids;
      while (p->next != node)
	p = p->next;
      p->next = node->next;
    }
#ifndef NO_FPA_HASH
    /* Remove from parent's hash table if present */
    if (parent->kid_hash != NULL)
      kid_hash_delete(parent->kid_hash, node->label);
    parent->num_kids--;
    /* Free hash table if we drop below threshold */
    if (parent->kid_hash != NULL && parent->num_kids < Kid_hash_threshold / 2) {
      free(parent->kid_hash);
      parent->kid_hash = NULL;
    }
#endif
    if (nfree >= 1000)
      fatal_error("fpa_trie_possible_delete: stack overflow");
    to_free[nfree++] = node;
    node = parent;
  }
  /* Free collected nodes (bottom-up order, matching original) */
  {
    int i;
    for (i = 0; i < nfree; i++)
      free_fpa_trie(to_free[i]);
  }
}  /* fpa_trie_possible_delete */

/*************
 *
 *    path_insert -- Given (term,path,index), insert a pointer
 *    to the term into the path list of the index.
 *
 *************/

static
void path_insert(Term t, Ilist path, Fpa_trie index)
{
  Fpa_trie node = fpa_trie_member_insert(index, path);

#ifdef FPA_DEBUG
  if (node->path == NULL)
    node->path = copy_ilist(path);
#endif

  if (node->terms == NULL)
    node->terms = get_fpa_list();
  fpalist_insert(node->terms, t);
}  /* path_insert */

/*************
 *
 *    path_delete -- Given (term,path,index), try to delete a pointer
 *    to the term from the path list of the index.
 *
 *************/

static
void path_delete(Term t, Ilist path, Fpa_trie index)
{
  Fpa_trie node = fpa_trie_member(index, path);

  if (node == NULL) {
    fatal_error("path_delete, trie node not found.");
  }

  fpalist_delete(node->terms, t);
  
#ifdef FPA_DEBUG
  if (fpalist_empty(node->terms)) {
    zap_ilist(node->path);
    node->path = NULL;
  }
#endif
  fpa_trie_possible_delete(node);
}  /* path_delete */

/*************
 *
 *    path_push -- append an integer to a path.   "save" is used because
 *    we have a pointer to the last member, but the list is singly linked.
 *
 *************/

static
Ilist path_push(struct path *p, int i)
{
  Ilist new = get_ilist();
  Ilist save = p->last;

  new->i = i;
  new->next = NULL;
  if (p->last == NULL)
    p->first = new;
  else
    p->last->next = new;
  p->last = new;
  return save;
}  /* path_push */

/*************
 *
 *    path_restore -- pop and throw away the last member of a path.
 *    We assume that "save" points to the next-to-last member.
 *
 *************/

static
void path_restore(struct path *p, Ilist save)
{
  free_ilist(p->last);
  p->last = save;
  if (save != NULL)
    save->next = NULL;
  else
    p->first = NULL;
}  /* path_restore */

/*************
 *
 *  fpa_paths (recursive) -- This routine traverses a term, keeping a
 *  path, and either inserts or deletes pointers to the term into/from the
 *  appropriate path lists of an FPA/PATH index.
 *
 *************/

static
void fpa_paths(Term root, Term t, struct path *p, int bound,
	       Indexop op, Fpa_trie index)
{
  /*
   * Iterative version using explicit stack.
   * Work item types:
   *   0 = process term (uses t, bound fields)
   *   1 = restore path (uses save field)
   *   2 = set arg position (uses argpos field, then process term)
   */
  struct fp_work {
    int type;
    Term t;
    int bound;
    int argpos;   /* for type 2: arg position to set */
    Ilist save;   /* for type 1: path restore point */
  };
  struct fp_work stack[1000];
  int top = 0;

  stack[top].type = 0;
  stack[top].t = t;
  stack[top].bound = bound;
  stack[top].argpos = 0;
  stack[top].save = NULL;
  top++;

  while (top > 0) {
    struct fp_work w;

    top--;
    w = stack[top];

    if (w.type == 1) {
      path_restore(p, w.save);
    }
    else {
      Term ct;
      int cb;
      Ilist save1;

      if (w.type == 2) {
	/* Set the arg position in the path before processing this term */
	p->last->i = w.argpos;
      }

      ct = w.t;
      cb = w.bound;

      if (VARIABLE(ct))
	save1 = path_push(p, 0);
      else
	save1 = path_push(p, SYMNUM(ct));

      if (COMPLEX(ct) && cb > 0 && !is_assoc_comm(SYMNUM(ct))) {
	int i;
	Ilist save2 = path_push(p, 0);

	/*
	 * Schedule work items (LIFO order, so push bottom-first):
	 *   1. restore save1 (executed last)
	 *   2. restore save2
	 *   3. For each child i (last to first):
	 *      - set_arg_and_process(ARG(ct,i), i+1, cb-1)
	 */
	if (top + ARITY(ct) + 2 > 1000)
	  fatal_error("fpa_paths: stack overflow");

	stack[top].type = 1;
	stack[top].save = save1;
	top++;

	stack[top].type = 1;
	stack[top].save = save2;
	top++;

	for (i = ARITY(ct) - 1; i >= 0; i--) {
	  stack[top].type = 2;
	  stack[top].t = ARG(ct, i);
	  stack[top].bound = cb - 1;
	  stack[top].argpos = i + 1;
	  top++;
	}
      }
      else {
	if (op == INSERT)
	  path_insert(root, p->first, index);
	else
	  path_delete(root, p->first, index);
	path_restore(p, save1);
      }
    }
  }
}  /* fpa_paths */

/*************
 *
 *   fpa_init_index()
 *
 *************/

/* DOCUMENTATION
This routine allocates and returns an empty FPA/Path index.
Parameter depth tells how deep to index the terms. For example,
depth=0 means to index on the root symbol only.
*/

/* PUBLIC */
Fpa_index fpa_init_index(int depth)
{
  Fpa_index f = get_fpa_index();
  f->depth = depth;
  f->root = get_fpa_trie();
  return f;
}  /* fpa_init_index */

/*************
 *
 *    fpa_update -- Insert/delete a term into/from a FPA-PATH index.
 *
 *************/

/* DOCUMENTATION
This routine inserts (op==INSERT) a term into an Fpa_index or
deletes (op==DELETE) a term from an Fpa_index.
<P>
IMPORTANT:  FPA indexing owns the FPA_ID field of the term.
<P>
A fatal error occurs if you try to delete a term that was not previously
inserted.
*/

/* PUBLIC */
void fpa_update(Term t, Fpa_index idx, Indexop op)
{
  struct path p;

  if (FPA_ID(t) == 0) {
    if (op == INSERT)
      FPA_ID(t) = ++Fpa_id_count;
    else
      fatal_error("fpa_update: FPA_ID=0.");
  }

  p.first = p.last = NULL;
  fpa_paths(t, t, &p, idx->depth, op, idx->root);
}  /* fpa_update */

/*************
 *
 *  query_leaf_full - for testing only
 *
 *  Ordinarily, with query_leaf(), if an FPA list doesn't exist,
 *  the query will be simplified.  If you wish to get the whole
 *  query tree, with NULL leaves for nonexistant FPA lists, you
 *  can use this instead of query_leaf().  This is useful if you
 *  want to print the query tree.
 *
 *************/

#ifdef FPA_DEBUG
static
Fpa_state query_leaf_full(Ilist path, Fpa_trie index)
{
  Fpa_trie n = fpa_trie_member(index, path);
  Fpa_state q = get_fpa_state();
  q->type = LEAF;
  q->terms = (n == NULL ? NULL : n->terms);
  q->path = copy_ilist(path);
  return q;
}  /* query_leaf_full */
#endif

/*************
 *
 *    query_leaf
 *
 *************/

static
Fpa_state query_leaf(Ilist path, Fpa_trie index)
{
  Fpa_trie n;

  /* return query_leaf_full(path, index); */

  n = fpa_trie_member(index, path);
  if (n == NULL)
    return NULL;
  else {
    Fpa_state q = get_fpa_state();
    q->type = LEAF;
    q->fpos = first_fpos(n->terms);
#ifdef FPA_DEBUG
    q->path = copy_ilist(path);
#endif
    return q;
  }
}  /* query_leaf */

/*************
 *
 *    query_intersect
 *
 *************/

static
Fpa_state query_intersect(Fpa_state q1, Fpa_state q2)
{
  /* Assume neither is NULL. */
  Fpa_state q = get_fpa_state();
  q->type = INTERSECT;
  q->left = q1;
  q->right = q2;
  return q;
}  /* query_intersect */

/*************
 *
 *    query_union
 *
 *************/

static
Fpa_state query_union(Fpa_state q1, Fpa_state q2)
{
  if (q1 == NULL)
    return q2;
  else if (q2 == NULL)
    return q1;
  else {
    Fpa_state q = get_fpa_state();
    q->type = UNION;
    q->left = q1;
    q->right = q2;
    return q;
  }
}  /* query_union */

/*************
 *
 *    query_special()
 *
 *************/

static
Fpa_state query_special(Fpa_trie n)
{
  /*
   * Iterative trie traversal collecting leaves, then build a BALANCED
   * union tree.  The old code built a left-degenerate tree (depth = N
   * leaves) via repeated query_union(q1, q).  next_term() recurses to
   * the depth of the union tree, so a degenerate tree with thousands
   * of leaves overflows the C stack.  A balanced tree has depth
   * log2(N), keeping next_term() recursion safe.
   */
  int trie_cap = 1024;
  Fpa_trie *trie_stack = malloc(trie_cap * sizeof(Fpa_trie));
  int trie_top = 0;

  int leaf_cap = 1024;
  Fpa_state *leaves = malloc(leaf_cap * sizeof(Fpa_state));
  int leaf_count = 0;

  if (trie_stack == NULL || leaves == NULL)
    fatal_error("query_special: malloc failed");

  trie_stack[trie_top++] = n;

  /* Phase 1: collect all leaves from the trie */
  while (trie_top > 0) {
    Fpa_trie cur = trie_stack[--trie_top];
    Query_special_calls++;

    if (cur->kids == NULL) {
      Fpa_state q = get_fpa_state();
      q->type = LEAF;
      q->fpos = first_fpos(cur->terms);
#ifdef FPA_DEBUG
      q->path = copy_ilist(cur->path);
#endif
      if (leaf_count >= leaf_cap) {
	leaf_cap *= 2;
	leaves = realloc(leaves, leaf_cap * sizeof(Fpa_state));
	if (leaves == NULL)
	  fatal_error("query_special: realloc failed");
      }
      leaves[leaf_count++] = q;
    }
    else {
      Fpa_trie pos_child;
      for (pos_child = cur->kids; pos_child != NULL; pos_child = pos_child->next) {
	if (pos_child->label == 1) {
	  Fpa_trie sym_child;
	  for (sym_child = pos_child->kids;
	       sym_child != NULL;
	       sym_child = sym_child->next) {
	    if (trie_top >= trie_cap) {
	      trie_cap *= 2;
	      trie_stack = realloc(trie_stack, trie_cap * sizeof(Fpa_trie));
	      if (trie_stack == NULL)
		fatal_error("query_special: realloc failed");
	    }
	    trie_stack[trie_top++] = sym_child;
	  }
	}
      }
    }
  }
  free(trie_stack);

  /* Phase 2: build balanced union tree by pairwise merging */
  if (leaf_count == 0) {
    free(leaves);
    return NULL;
  }
  while (leaf_count > 1) {
    int j = 0;
    int i;
    for (i = 0; i < leaf_count; i += 2) {
      if (i + 1 < leaf_count)
	leaves[j++] = query_union(leaves[i], leaves[i+1]);
      else
	leaves[j++] = leaves[i];
    }
    leaf_count = j;
  }
  {
    Fpa_state result = leaves[0];
    free(leaves);
    return result;
  }
}  /* query_special */

/*************
 *
 *  zap_fpa_state (recursive)
 *
 *  This (recursive) routine frees an Fpa_state.
 *  It should NOT be called if you retrieve all answers to
 *  a query, because the query tree is freed as it is processsed
 *  by fpa_next_answer().  This routine should be called only if
 *  you decide not to get all of the answers.
 *
 *************/

static
void zap_fpa_state(Fpa_state q)
{
  /* Iterative DFS over binary UNION tree.  Stack depth is O(log N)
     because query_special builds balanced trees via pairwise merge. */
  Fpa_state stack[1000];
  int top = 0;

  if (q == NULL)
    return;

  stack[top++] = q;

  while (top > 0) {
    Fpa_state cur = stack[--top];
    if (cur != NULL) {
      if (cur->left != NULL) {
	if (top >= 1000)
	  fatal_error("zap_fpa_state: stack overflow");
	stack[top++] = cur->left;
      }
      if (cur->right != NULL) {
	if (top >= 1000)
	  fatal_error("zap_fpa_state: stack overflow");
	stack[top++] = cur->right;
      }
#ifdef FPA_DEBUG
      zap_ilist(cur->path);
#endif
      free_fpa_state(cur);
    }
  }
}  /* zap_fpa_state */

/*************
 *
 *   union_commuted()
 *
 *************/

static
Fpa_state union_commuted(Fpa_state q, Term t, Context c,
			 Querytype type,
			 struct path *p, int bound, Fpa_trie index)
{
  Fpa_state q1;
  int empty, i;
#if 0
  printf("enter union_commuted with\n");
  p_fpa_state(q);
#endif
  q1 = NULL;
  empty = 0;

  for (i = 0; i < 2 && !empty; i++) {
    p->last->i = (i == 0 ? 2 : 1);
    /* Skip this arg if VARIABLE && (UNIFY || INSTANCE). */
    if (!VARIABLE(ARG(t,i)) || type==GENERALIZATION ||
	type==VARIANT || type==IDENTICAL) {
      Fpa_state q2 = build_query(ARG(t,i), c, type, p, bound-1, index);
      if (q2 == NULL) {
	empty = 1;
	zap_fpa_state(q1);
	q1 = NULL;
      }
      else if (q1 == NULL)
	q1 = q2;
      else
	q1 = query_intersect(q1, q2);
    }
  }
  if (q1 != NULL)
    q1 = query_union(q, q1);
  else
    q1 = q;
#if 0
  printf("exit union_commuted with\n");
  p_fpa_state(q1);
#endif    
  return(q1);
}  /* union_commuted */

/*************
 *
 *   var_in_context()
 *
 *************/

static
BOOL var_in_context(Term t, Context c)
{
  DEREFERENCE(t, c);
  return VARIABLE(t);
}  /* var_in_context */

/*************
 *
 *   all_args_vars_in_context()
 *
 *************/

static
BOOL all_args_vars_in_context(Term t, Context c)
{
  /* Assume t is not a variable. */
  int i = 0;
  BOOL ok = TRUE;
  while (i < ARITY(t) && ok) {
    ok = var_in_context(ARG(t,i), c);
    i++;
  }
  return ok;
}  /* all_args_vars_in_context */

/*************
 *
 *   build_query()
 *
 *************/

static
Fpa_state build_query(Term t, Context c, Querytype type,
		      struct path *p, int bound, Fpa_trie index)
{
  /* Convert tail-recursive variable dereferencing to a loop.
   * The structural recursion through children is bounded by 'bound'
   * (FPA index depth, typically 3-5) and cannot overflow the stack.
   */
  while (VARIABLE(t)) {
    int i = VARNUM(t);
    if (c != NULL && c->terms[i] != NULL) {
      Term new_t = c->terms[i];
      c = c->contexts[i];
      t = new_t;
    }
    else if (type == UNIFY || type == INSTANCE) {
      fatal_error("build_query, variable.");
      return NULL;  /* to quiet compiler */
    }
    else {
      Ilist save = path_push(p, 0);
      Fpa_state q = query_leaf(p->first, index);
      path_restore(p, save);
      return q;
    }
  }
  {  /* non-variable */
    Fpa_state q1 = NULL;
    Ilist save1 = path_push(p, SYMNUM(t));

    if (CONSTANT(t) || bound <= 0 || is_assoc_comm(SYMNUM(t))) {
      q1 = query_leaf(p->first, index);
      /* _AnyConst multi-path: also query all _AnyConst_n paths */
      if (MATCH_HINTS_ANYCONST && AnyConstsEnabled && CONSTANT(t)) {
        int ac_i;
        int save_sym = p->last->i;  /* save original SYMNUM(t) */
        for (ac_i = 0; ac_i < MAX_ANYCONSTS; ac_i++) {
          Fpa_state qAny;
          p->last->i = any_const_sn(ac_i);
          qAny = query_leaf(p->first, index);
          if (qAny)
            q1 = (q1 == NULL) ? qAny : query_union(q1, qAny);
        }
        p->last->i = save_sym;  /* restore */
      }
    }
    else if ((type == INSTANCE || type == UNIFY) &&
	     all_args_vars_in_context(t, c)) {
      Fpa_trie n = fpa_trie_member(index, p->first);
      q1 = (n == NULL ? NULL : query_special(n));
    }
    else {
      Ilist save2 = path_push(p, 0);
      int empty = 0;
      int i;
      for (i = 0; i < ARITY(t) && !empty; i++) {
	p->last->i = i+1;
	/* Skip this arg if VARIABLE && (UNIFY || INSTANCE). */
	if (!var_in_context(ARG(t,i),c) || type==GENERALIZATION ||
	    type==VARIANT || type==IDENTICAL) {
	  Fpa_state q2 = build_query(ARG(t,i), c, type, p, bound-1, index);
					      
	  if (q2 == NULL) {
	    empty = 1;
	    zap_fpa_state(q1);
	    q1 = NULL;
	  }
	  else if (q1 == NULL)
	    q1 = q2;
	  else
	    q1 = query_intersect(q1, q2);
	}
      }
      if (is_commutative(SYMNUM(t)) && !term_ident(ARG(t,0), ARG(t,1)))
	q1 = union_commuted(q1, t, c, type, p, bound, index);
      path_restore(p, save2);
    }
    if (type == UNIFY || type == GENERALIZATION) {
      Fpa_state q2;
      p->last->i = 0;
      q2 = query_leaf(p->first, index);
      q1 = query_union(q1, q2);
    }
    path_restore(p, save1);
    return q1;
  }
}  /* build_query */

/*************
 *
 *    fprint_fpa_state (recursive)
 *
 *************/

/* DOCUMENTATION
This (recursive) routine prints (to FILE *fp) an Fpa_state tree.
The depth parameter should be 0 on the top call.
This is an AND/OR tree, with lists of terms (ordered by FPA_ID)
at the leaves.  If FPA_DEBUG is not defined in fpa.h, the
paths corresponding to the leaves are not printed, and the
tree is hard to understand without the paths.
*/

/* PUBLIC */
void fprint_fpa_state(FILE *fp, Fpa_state q, int depth)
{
  /* Iterative version using explicit stack */
  struct { Fpa_state node; int depth; } stack[1000];
  int top = 0;

  stack[top].node = q;
  stack[top].depth = depth;
  top++;

  while (top > 0) {
    Fpa_state cur;
    int cur_depth, i;

    top--;
    cur = stack[top].node;
    cur_depth = stack[top].depth;

    for (i = 0; i < cur_depth; i++)
      fprintf(fp, "- - ");

    switch (cur->type) {
    case UNION: fprintf(fp, "OR\n"); break;
    case INTERSECT: fprintf(fp, "AND\n"); break;
    case LEAF:
#ifdef FPA_DEBUG
      fprint_path(fp, cur->path);
      fprintf(fp, " ");
#endif
      p_fpa_list(cur->fpos.f);
      break;
    }
    fflush(fp);
    if (cur->type == UNION || cur->type == INTERSECT) {
      /* Push left first (processed second), then right (processed first)
       * to match original order: right printed before left */
      if (top + 2 > 1000)
	fatal_error("fprint_fpa_state: stack overflow");
      stack[top].node = cur->left;
      stack[top].depth = cur_depth + 1;
      top++;
      stack[top].node = cur->right;
      stack[top].depth = cur_depth + 1;
      top++;
    }
  }
}  /* fprint_fpa_state */

/*************
 *
 *    p_fpa_state
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) an Fpa_state tree.
See the description of fprint_fpa_state().
*/

/* PUBLIC */
void p_fpa_state(Fpa_state q)
{
  fprint_fpa_state(stdout, q, 0);
}  /* fprint_fpa_state */

/*************
 *
 *    p_fpa_query
 *
 *************/

/* DOCUMENTATION
This routine constructs an fpa_query tree and prints it to stdout.
*/

/* PUBLIC */
void p_fpa_query(Term t, Querytype query_type, Fpa_index idx)
{
  Fpa_state q;
  char *s;
  struct path p;
  p.first = p.last = NULL;

  switch (query_type) {
  case UNIFY:          s = "UNIFY         "; break;
  case INSTANCE:       s = "INSTANCE      "; break;
  case GENERALIZATION: s = "GENERALIZATION"; break;
  case VARIANT:        s = "VARIANT       "; break;
  case IDENTICAL:      s = "IDENTICAL     "; break;
  default:                 s = "FPA_??            "; break;
  }
  printf("\n%s with term %u: ", s, (unsigned) FPA_ID(t)); p_term(t);
  fflush(stdout);

  q = build_query(t, NULL, query_type, &p, idx->depth, idx->root);
  p_fpa_state(q);
  zap_fpa_state(q);
  
}  /* fprint_fpa_query */

/*************
 *
 *    next_term()
 *
 *    Get the first or next term that satisfies a unification condition.
 *    (Unification conditions are provided by build_query.)
 *    `max' should be FPA_ID_MAX on top calls.  A return of NULL indicates
 *    that there are none or no more terms that satisfy (and the tree has
 *    been deallocated).  If you want to stop getting terms before a NULL
 *    is returned, then please deallocate the tree with zap_fpa_state(tree).
 *
 *    Warning: a return of NULL means that the tree has been deallocated.
 *
 *************/

static
Term next_term(Fpa_state q, FPA_ID_TYPE max)
{
  BUMP_NEXT_CALLS;
  if (q == NULL)
    return NULL;
  else if (q->type == LEAF) {
    Term t = FTERM(q->fpos);
    while (t != NULL && FPA_ID(t) > max) {
      q->fpos = next_fpos(q->fpos);
      t = FTERM(q->fpos);
    }
    if (t == NULL) {
      zap_fpa_state(q);
      return NULL;
    }
    else {
      q->fpos = next_fpos(q->fpos);
      return t;
    }
  }
    
  else if (q->type == INTERSECT) {
    Term t1, t2;
    Intersect_merge_ops++;
    t1 = next_term(q->left, max);
    if (t1 != NULL)
      t2 = next_term(q->right, FPA_ID(t1));
    else
      t2 = (Term) &t2;  /* anything but NULL */

    while (t1 != t2 && t1 != NULL && t2 != NULL) {
      Intersect_merge_ops++;
      if (FGT(t1,t2))
	t1 = next_term(q->left, FPA_ID(t2));
      else
	t2 = next_term(q->right, FPA_ID(t1));
    }
    if (t1 == NULL || t2 == NULL) {
      if (t1 == NULL)
	q->left = NULL;
      if (t2 == NULL)
	q->right = NULL;
      zap_fpa_state(q);
      return NULL; 
    }
    else
      return t1;
  }
    
  else {  /* UNION node */
    Term t1, t2;
    /* first get the left term */
    t1 = q->left_term;
    if (t1 == NULL) {
      /* it must be brought up */
      if (q->left) {
	t1 = next_term(q->left, max);
	if (t1 == NULL)
	  q->left = NULL;
      }
    }
    else  /* it was saved from a previous call */
      q->left_term = NULL;
    
    /* now do the same for the right side */
    t2 = q->right_term;
    if (t2 == NULL) {
      if (q->right) {
	t2 = next_term(q->right, max);
	if (t2 == NULL)
	  q->right = NULL;
      }
    }
    else
      q->right_term = NULL;
    
    /* At this point, both left_term and right_term are NULL.
     * Now decide which of t1 and t2 to return.  If both are
     * non-NULL (and different), save the smaller for the next
     * call, and return the larger.
     */
    if (t1 == NULL) {
      if (t2 == NULL) {
	zap_fpa_state(q);
	return NULL;
      }
      else
	return t2;
    }
    else if (t2 == NULL)
      return t1;
    else if (t1 == t2)
      return t1;
    else if (FGT(t1,t2)) {
      q->right_term = t2;  /* save t2 for next time */
      return t1;
    }
    else {
      q->left_term = t1;  /* save t1 for next time */
      return t2;
    }
  }
}  /* next_term */

/*************
 *
 *    fpa_next_answer()
 *
 *************/

/* DOCUMENTATION
This routine extracts and returns the next answer term
from an Fpa_state tree.  If there
are no more answers, NULL is returned, and the tree is freed.
If you wish to stop getting answers before NULL is returned,
call zap_fpa_state(q) to free the Fpa_state tree.
*/

/* PUBLIC */
Term fpa_next_answer(Fpa_state q)
{
  return next_term(q, FPA_ID_MAX);
}  /* fpa_next_answer */

/*************
 *
 *   fpa_first_answer()
 *
 *************/

/* DOCUMENTATION
This routine extracts and returns the first answer term
from an Fpa_state tree.  If there
are no more answers, NULL is returned, and the tree is freed.
If you wish to stop getting answers before NULL is returned,
call zap_fpa_state(q) to free the Fpa_state tree.
<P>
The query types are
UNIFY, INSTANCE, GENERALIZATION, VARIANT, and IDENTICAL.
<P>
If Context c is not NULL, then the instance of the term (in the
context) is used for the query.
*/

/* PUBLIC */
Term fpa_first_answer(Term t, Context c, Querytype query_type,
		      Fpa_index idx, Fpa_state *ppos)
{
  struct path p;
  p.first = p.last = NULL;

  *ppos = build_query(t, c, query_type, &p, idx->depth, idx->root);
  
  return fpa_next_answer(*ppos);
}  /* fpa_first_answer */

/*************
 *
 *    fpa_cancel
 *
 *************/

/* DOCUMENTATION
This routine should be called if you get some, but not all answers
to an fpa query.  See fpa_first_answer() and fpa_next_answer().
*/

/* PUBLIC */
void fpa_cancel(Fpa_state q)
{
  zap_fpa_state(q);
}  /* fpa_cancel */

/*************
 *
 *   zap_fpa_trie()
 *
 *************/

static
void zap_fpa_trie(Fpa_trie n)
{
  /* Iterative DFS using heap-allocated stack */
  int cap = 1024;
  Fpa_trie *stack = malloc(cap * sizeof(Fpa_trie));
  int top = 0;

  if (stack == NULL)
    fatal_error("zap_fpa_trie: malloc failed");

  stack[top++] = n;

  while (top > 0) {
    Fpa_trie cur = stack[--top];
    Fpa_trie k = cur->kids;

    /* Push all children onto stack */
    while (k != NULL) {
      Fpa_trie next_k = k->next;
      if (top >= cap) {
	cap *= 2;
	stack = realloc(stack, cap * sizeof(Fpa_trie));
	if (stack == NULL)
	  fatal_error("zap_fpa_trie: realloc failed");
      }
      stack[top++] = k;
      k = next_k;
    }

    zap_fpalist(cur->terms);

#ifdef FPA_DEBUG
    zap_ilist(cur->path);
#endif

    free_fpa_trie(cur);
  }
  free(stack);
}  /* zap_fpa_trie */

/*************
 *
 *   zap_fpa_index()
 *
 *************/

/* DOCUMENTATION
This routine removes all the entries from an Fpa_index idx and
frees all of the associated memory.
*/

/* PUBLIC */
void zap_fpa_index(Fpa_index idx)
{
  zap_fpa_trie(idx->root);
  free_fpa_index(idx);
}  /* zap_fpa_index */

/*************
 *
 *   fpa_empty()
 *
 *************/

/* DOCUMENTATION
This Boolean routine checks if an FPA/Path index is empty.
*/

/* PUBLIC */
BOOL fpa_empty(Fpa_index idx)
{
  return (idx == NULL ? TRUE : idx->root->kids == NULL);
}  /* fpa_empty */

/*************
 *
 *   fpa_density()
 *
 *************/

static
void fpa_density(Fpa_trie p)
{
  /* Iterative DFS using heap-allocated stack */
  int cap = 1024;
  Fpa_trie *stack = malloc(cap * sizeof(Fpa_trie));
  int top = 0;

  if (stack == NULL)
    fatal_error("fpa_density: malloc failed");

  stack[top++] = p;

  while (top > 0) {
    Fpa_trie cur = stack[--top];
    Fpa_trie q;

    /* Push children (order doesn't matter for density reporting) */
    for (q = cur->kids; q; q = q->next) {
      if (top >= cap) {
	cap *= 2;
	stack = realloc(stack, cap * sizeof(Fpa_trie));
	if (stack == NULL)
	  fatal_error("fpa_density: realloc failed");
      }
      stack[top++] = q;
    }

    if (cur->terms != NULL) {
      printf("Fpa_list: chunks=%d, size=%d, terms=%d\n",
	     cur->terms->num_chunks,
	     cur->terms->chunksize,
	     cur->terms->num_terms);
    }
  }
  free(stack);
}  /* fpa_density */

/*************
 *
 *   p_fpa_density()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void p_fpa_density(Fpa_index idx)
{
  fpa_density(idx->root);
}  /* p_fpa_density */

/*************
 *
 *   mega_next_calls()
 *
 *************/

/* DOCUMENTATION
 */

/* PUBLIC */
unsigned mega_next_calls(void)
{
  return
    (Next_calls / 1000000) +
    ((UINT_MAX / 1000000) * Next_calls_overflows);
}  /* mega_next_calls */

/*************
 *
 *   fpa_query_special_calls()
 *
 *************/

/* DOCUMENTATION
Return the number of query_special() calls made to FPA indices.
*/

/* PUBLIC */
unsigned long long fpa_query_special_calls(void)
{
  return Query_special_calls;
}  /* fpa_query_special_calls */

/*************
 *
 *   fpa_intersect_merge_ops()
 *
 *************/

/* DOCUMENTATION
Return the number of intersect/merge operations in FPA queries.
*/

/* PUBLIC */
unsigned long long fpa_intersect_merge_ops(void)
{
  return Intersect_merge_ops;
}  /* fpa_intersect_merge_ops */

/*************
 *
 *   get_fpa_id_count()
 *
 *   Return the current FPA ID counter value (for checkpoint save).
 *
 *************/

/* PUBLIC */
unsigned get_fpa_id_count(void)
{
  return Fpa_id_count;
}  /* get_fpa_id_count */

/*************
 *
 *   set_fpa_id_count()
 *
 *   Set the FPA ID counter to a specific value (for checkpoint restore).
 *
 *************/

/* PUBLIC */
void set_fpa_id_count(unsigned n)
{
  Fpa_id_count = n;
}  /* set_fpa_id_count */

/*************
 *
 *   set_fpa_hash_threshold()
 *
 *************/

/* PUBLIC */
void set_fpa_hash_threshold(int n)
{
#ifndef NO_FPA_HASH
  Kid_hash_threshold = n;
#endif
}  /* set_fpa_hash_threshold */

/*************
 *
 *   get_fpa_hash_threshold()
 *
 *************/

/* PUBLIC */
int get_fpa_hash_threshold(void)
{
#ifndef NO_FPA_HASH
  return Kid_hash_threshold;
#else
  return 0;
#endif
}  /* get_fpa_hash_threshold */
