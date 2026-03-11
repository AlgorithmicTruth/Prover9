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

#include "di_tree.h"

/* Private definitions and types */

static unsigned long long Nonunit_fsub_tests;
static unsigned long long Nonunit_bsub_tests;

static unsigned Sub_calls = 0;
static unsigned Sub_calls_overflows = 0;
#define BUMP_SUB_CALLS {Sub_calls++; if (Sub_calls == 0) Sub_calls_overflows++;}

/*************
 *
 *   nonunit_fsub_tests(void)
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
unsigned long long nonunit_fsub_tests(void)
{
  return Nonunit_fsub_tests;
}  /* nonunit_fsub_tests */

/*************
 *
 *   nonunit_bsub_tests(void)
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
unsigned long long nonunit_bsub_tests(void)
{
  return Nonunit_bsub_tests;
}  /* nonunit_bsub_tests */

/*
 * memory management
 */

#define PTRS_DI_TREE PTRS(sizeof(struct di_tree))
static unsigned Di_tree_gets, Di_tree_frees;

/*************
 *
 *   Di_tree get_di_tree()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Di_tree get_di_tree(void)
{
  Di_tree p = get_cmem(PTRS_DI_TREE);
  Di_tree_gets++;
  return(p);
}  /* get_di_tree */

/*************
 *
 *    free_di_tree()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void free_di_tree(Di_tree p)
{
  free_mem(p, PTRS_DI_TREE);
  Di_tree_frees++;
}  /* free_di_tree */

/*************
 *
 *   fprint_di_tree_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for data types
associated with the di_tree package.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_di_tree_mem(FILE *fp, BOOL heading)
{
  int n;
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");

  n = sizeof(struct di_tree);
  fprintf(fp, "di_tree (%4d)      %11u%11u%11u%9.1f K\n",
          n, Di_tree_gets, Di_tree_frees,
          Di_tree_gets - Di_tree_frees,
          ((Di_tree_gets - Di_tree_frees) * n) / 1024.);

}  /* fprint_di_tree_mem */

/*************
 *
 *   p_di_tree_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) memory usage statistics for data types
associated with the di_tree package.
*/

/* PUBLIC */
void p_di_tree_mem(void)
{
  fprint_di_tree_mem(stdout, TRUE);
}  /* p_di_tree_mem */

/*
 *  end of memory management
 */

/*************
 *
 *   init_di_tree()
 *
 *************/

/* DOCUMENTATION
This routine allocates and returns an empty integer-vector
discrimination index.
*/

/* PUBLIC */
Di_tree init_di_tree(void)
{
  return get_di_tree();
}  /* init_di_tree */

/*************
 *
 *   di_tree_insert()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void di_tree_insert(int *vec, int len, Di_tree node, void *datum)
{
  int i;
  for (i = 0; i < len; i++) {
    Di_tree prev = NULL;
    Di_tree curr = node->u.kids;
    /* kids are in increasing order */
    while (curr && vec[i] > curr->label) {
      prev = curr;
      curr = curr->next;
    }
    if (curr == NULL || vec[i] != curr->label) {
      Di_tree new = get_di_tree();
      new->label = vec[i];
      new->next = curr;
      if (prev)
	prev->next = new;
      else
	node->u.kids = new;
      curr = new;
    }
    node = curr;
  }
  /* past end of vec: insert datum at leaf */
  {
    Plist p = get_plist();
    p->v = datum;
    p->next = node->u.data;
    node->u.data = p;
  }
}  /* di_tree_insert */

/*************
 *
 *   di_tree_delete()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL di_tree_delete(int *vec, int len, Di_tree node, void *datum)
{
  int lev;

  if (len == 0) {
    node->u.data = plist_remove(node->u.data, datum);
    return node->u.data != NULL;
  }

  /* Heap-allocated arrays for the walk-down path */
  {
    Di_tree *parents = (Di_tree *) malloc(len * sizeof(Di_tree));
    Di_tree *prevs   = (Di_tree *) malloc(len * sizeof(Di_tree));
    Di_tree *currs   = (Di_tree *) malloc(len * sizeof(Di_tree));
    BOOL keep;
    if (!parents || !prevs || !currs)
      fatal_error("di_tree_delete, malloc failed");

    /* Walk down, saving parent/prev/curr at each level */
    for (lev = 0; lev < len; lev++) {
      Di_tree prev = NULL;
      Di_tree curr = node->u.kids;
      while (curr && vec[lev] > curr->label) {
        prev = curr;
        curr = curr->next;
      }
      if (curr == NULL || vec[lev] != curr->label)
        fatal_error("di_tree_delete, node not found");
      parents[lev] = node;
      prevs[lev]   = prev;
      currs[lev]   = curr;
      node = curr;
    }

    /* At the leaf: remove datum */
    node->u.data = plist_remove(node->u.data, datum);
    keep = (node->u.data != NULL);

    /* Walk back up, removing empty nodes */
    for (lev = len - 1; lev >= 0 && !keep; lev--) {
      Di_tree curr = currs[lev];
      if (prevs[lev])
        prevs[lev]->next = curr->next;
      else
        parents[lev]->u.kids = curr->next;
      free_di_tree(curr);
      keep = (parents[lev]->u.kids != NULL);
    }

    free(parents);
    free(prevs);
    free(currs);
    return keep;
  }
}  /* di_tree_delete */

/*************
 *
 *   zap_di_tree()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void zap_di_tree(Di_tree node, int depth)
{
  int cap = 256;
  int top = 0;
  Di_tree *nd_stk = (Di_tree *) malloc(cap * sizeof(Di_tree));
  int     *dp_stk = (int *)     malloc(cap * sizeof(int));
  if (!nd_stk || !dp_stk)
    fatal_error("zap_di_tree, malloc failed");

  nd_stk[top] = node;
  dp_stk[top] = depth;
  top++;

  while (top > 0) {
    top--;
    node  = nd_stk[top];
    depth = dp_stk[top];

    if (depth == 0) {
      zap_plist(node->u.data);
    }
    else {
      Di_tree kid = node->u.kids;
      while (kid) {
        Di_tree tmp = kid;
        kid = kid->next;
        /* Push child onto stack */
        if (top >= cap) {
          cap *= 2;
          nd_stk = (Di_tree *) realloc(nd_stk, cap * sizeof(Di_tree));
          dp_stk = (int *)     realloc(dp_stk, cap * sizeof(int));
          if (!nd_stk || !dp_stk)
            fatal_error("zap_di_tree, realloc failed");
        }
        nd_stk[top] = tmp;
        dp_stk[top] = depth - 1;
        top++;
      }
    }
    free_di_tree(node);
  }

  free(nd_stk);
  free(dp_stk);
}  /* zap_di_tree */

/*************
 *
 *   p_di_tree()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void p_di_tree(int *vec, int len, Di_tree node, int depth)
{
  /* Iterative tree traversal using a heap-allocated stack.
     Each frame stores (vec_idx, node, depth) for a deferred child visit. */
  struct pdt_frame {
    int vec_idx;
    Di_tree node;
    int depth;
  };
  int cap = 256;
  int sp = 0;
  struct pdt_frame *stack = malloc(cap * sizeof(struct pdt_frame));
  if (!stack)
    fatal_error("p_di_tree: malloc failed");

  /* Push initial call. */
  stack[sp].vec_idx = 0;
  stack[sp].node = node;
  stack[sp].depth = depth;
  sp++;

  while (sp > 0) {
    int i;
    int vi;
    Di_tree n;
    int d;

    sp--;
    vi = stack[sp].vec_idx;
    n = stack[sp].node;
    d = stack[sp].depth;

    for (i = 0; i < d; i++)
      printf(" ");

    if (vi >= len) {
      Plist p = n->u.data;
      printf("IDs:");
      while (p) {
        Topform c = p->v;
        printf(" %llu", c->id);
        p = p->next;
      }
      printf("\n");
    }
    else {
      Di_tree kid;
      /* Count children so we can push in reverse order (to print
         in the original left-to-right order when popping LIFO). */
      int nkids = 0;
      for (kid = n->u.kids; kid; kid = kid->next)
        nkids++;

      printf("%d\n", n->label);

      /* Ensure capacity. */
      while (sp + nkids > cap) {
        cap *= 2;
        stack = realloc(stack, cap * sizeof(struct pdt_frame));
        if (!stack)
          fatal_error("p_di_tree: realloc failed");
      }

      /* Push children forward, then reverse the slice so that
         LIFO popping preserves the original left-to-right order. */
      {
        int base = sp;
        for (kid = n->u.kids; kid; kid = kid->next) {
          stack[sp].vec_idx = vi + 1;
          stack[sp].node = kid;
          stack[sp].depth = d + 1;
          sp++;
        }
        /* Reverse stack[base..sp-1] to get LIFO = original order. */
        {
          int lo = base, hi = sp - 1;
          while (lo < hi) {
            struct pdt_frame tmp = stack[lo];
            stack[lo] = stack[hi];
            stack[hi] = tmp;
            lo++;
            hi--;
          }
        }
      }
    }
  }
  free(stack);
}  /* p_di_tree */

/*************
 *
 *   subsume_di_literals()
 *
 *************/

static
BOOL subsume_di_literals(Literals clit, Context subst, Literals d, Trail *trp)
{
  /* Iterative backtracking search over the literal list clit.
     MAX_LITS bounds clause length; real clauses rarely exceed 100. */
  enum { MAX_LITS = 1000 };
  Literals cstack[MAX_LITS];  /* clit at each depth */
  Literals dstack[MAX_LITS];  /* current dlit position at each depth */
  Trail    marks[MAX_LITS];   /* trail mark at each depth */
  int depth = 0;

  BUMP_SUB_CALLS;
  if (clit == NULL)
    return TRUE;

  /* Push first frame. */
  cstack[0] = clit;
  dstack[0] = d;

  while (depth >= 0) {
    Literals cl = cstack[depth];
    Literals dl = dstack[depth];
    BOOL found = FALSE;

    BUMP_SUB_CALLS;

    /* Search for a matching dlit from the current position. */
    for (; dl != NULL; dl = dl->next) {
      if (cl->sign == dl->sign) {
        Trail mark = *trp;
        if (match(cl->atom, subst, dl->atom, trp)) {
          if (cl->next == NULL) {
            return TRUE;  /* all clits matched */
          }
          marks[depth] = mark;
          dstack[depth] = dl->next;  /* resume point on backtrack */
          depth++;
          if (depth >= MAX_LITS)
            fatal_error("subsume_di_literals: clause too long for iterative stack");
          cstack[depth] = cl->next;
          dstack[depth] = d;
          found = TRUE;
          break;
        }
      }
    }

    if (!found) {
      /* Backtrack. */
      depth--;
      if (depth >= 0) {
        undo_subst_2(*trp, marks[depth]);
        *trp = marks[depth];
      }
    }
  }
  return FALSE;
}  /* subsume_di_literals */

/*************
 *
 *   subsumes_di()
 *
 *************/

static
BOOL subsumes_di(Literals c, Literals d, Context subst)
{
  Trail tr = NULL;
  BOOL subsumed = subsume_di_literals(c, subst, d, &tr);
  if (subsumed)
    undo_subst(tr);
  return subsumed;
}  /* subsumes_di */

/*************
 *
 *   di_tree_forward()
 *
 *************/

static
Topform di_tree_forward(int *vec, int len, Di_tree node, Literals dlits,
			Context subst)
{
  Topform result = NULL;

  if (len == 0) {
    /* Root is a leaf */
    Plist p = node->u.data;
    BUMP_SUB_CALLS;
    while (p) {
      Topform c = p->v;
      Nonunit_fsub_tests++;
      if (subsumes_di(c->literals, dlits, subst))
        return p->v;
      p = p->next;
    }
    return NULL;
  }

  {
    Di_tree *stk = (Di_tree *) malloc(len * sizeof(Di_tree));
    int lev = 0;
    Di_tree kid;
    if (!stk)
      fatal_error("di_tree_forward, malloc failed");

    kid = node->u.kids;

    while (lev >= 0) {
      BUMP_SUB_CALLS;
      if (kid == NULL || kid->label > vec[lev]) {
        /* Backtrack */
        lev--;
        if (lev >= 0)
          kid = stk[lev];  /* resume with next sibling */
      }
      else if (lev == len - 1) {
        /* kid is at leaf level — check its data */
        Plist p = kid->u.data;
        while (p) {
          Topform c = p->v;
          Nonunit_fsub_tests++;
          if (subsumes_di(c->literals, dlits, subst)) {
            result = p->v;
            goto done;
          }
          p = p->next;
        }
        kid = kid->next;  /* next sibling at this level */
      }
      else {
        /* Descend: save next sibling for later, go to kid's children */
        stk[lev] = kid->next;
        lev++;
        kid = kid->u.kids;
      }
    }

  done:
    free(stk);
    return result;
  }
}  /* di_tree_forward */

/*************
 *
 *   forward_feature_subsume()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Topform forward_feature_subsume(Topform d, Di_tree root)
{
  int *f = features(d->literals);
  int len = feature_length();
  Context subst = get_context();
  Topform c = di_tree_forward(f, len, root, d->literals, subst);
  free_context(subst);
  return c;
}  /* forward_feature_subsume */

/*************
 *
 *   di_tree_back()
 *
 *************/

static
void di_tree_back(int *vec, int len, Di_tree node, Literals clits,
		  Context subst, Plist *subsumees)
{
  if (len == 0) {
    /* Root is a leaf */
    Plist p = node->u.data;
    BUMP_SUB_CALLS;
    while (p) {
      Topform d = p->v;
      Nonunit_bsub_tests++;
      if (clits != d->literals && subsumes_di(clits, d->literals, subst))
        *subsumees = plist_prepend(*subsumees, d);
      p = p->next;
    }
    return;
  }

  {
    Di_tree *stk = (Di_tree *) malloc(len * sizeof(Di_tree));
    int lev = 0;
    Di_tree kid;
    if (!stk)
      fatal_error("di_tree_back, malloc failed");

    /* Start: skip kids with label < vec[0] */
    kid = node->u.kids;
    while (kid && kid->label < vec[0])
      kid = kid->next;

    while (lev >= 0) {
      BUMP_SUB_CALLS;
      if (kid == NULL) {
        /* Backtrack */
        lev--;
        if (lev >= 0)
          kid = stk[lev];  /* resume with next sibling */
      }
      else if (lev == len - 1) {
        /* kid is at leaf level — check its data */
        Plist p = kid->u.data;
        while (p) {
          Topform d = p->v;
          Nonunit_bsub_tests++;
          if (clits != d->literals && subsumes_di(clits, d->literals, subst))
            *subsumees = plist_prepend(*subsumees, d);
          p = p->next;
        }
        kid = kid->next;  /* next sibling at this level */
      }
      else {
        /* Descend: save next sibling, go to kid's children */
        stk[lev] = kid->next;
        lev++;
        /* Skip kids with label < vec[lev] at the new level */
        kid = kid->u.kids;
        while (kid && kid->label < vec[lev])
          kid = kid->next;
      }
    }

    free(stk);
  }
}  /* di_tree_back */

/*************
 *
 *   back_feature_subsume()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist back_feature_subsume(Topform c, Di_tree root)
{
  int *f = features(c->literals);
  int len = feature_length();
  Context subst = get_context();
  Plist subsumees = NULL;
  di_tree_back(f, len, root, c->literals, subst, &subsumees);
  free_context(subst);
  return subsumees;
}  /* back_feature_subsume */

/*************
 *
 *   mega_sub_calls()
 *
 *************/

/* DOCUMENTATION
 */

/* PUBLIC */
unsigned mega_sub_calls(void)
{
  return
    (Sub_calls / 1000000) +
    ((UINT_MAX / 1000000) * Sub_calls_overflows);
}  /* mega_sub_calls */
