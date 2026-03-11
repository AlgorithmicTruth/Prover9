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

#include "flatterm.h"

/* Private definitions and types */

/*
 * memory management
 */

#define PTRS_FLATTERM PTRS(sizeof(struct flatterm))
static unsigned Flatterm_gets, Flatterm_frees;

/*************
 *
 *   Flatterm get_flatterm()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Flatterm get_flatterm(void)
{
  Flatterm p = get_mem(PTRS_FLATTERM);  /* get uninitialized memory */
  Flatterm_gets++;

  p->prev = NULL;
  p->next = NULL;
  p->varnum_bound_to = -1;
  p->alternative = NULL;
  p->reduced_flag = FALSE;
  p->size = 0;

  /* end, arity, private_symbol not initilized */
  return(p);
}  /* get_flatterm */

/*************
 *
 *    free_flatterm()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void free_flatterm(Flatterm p)
{
  free_mem(p, PTRS_FLATTERM);
  Flatterm_frees++;
}  /* free_flatterm */

/*************
 *
 *   fprint_flatterm_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for data types
associated with the flatterm package.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_flatterm_mem(FILE *fp, BOOL heading)
{
  int n;
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");

  n = sizeof(struct flatterm);
  fprintf(fp, "flatterm (%4d)     %11u%11u%11u%9.1f K\n",
          n, Flatterm_gets, Flatterm_frees,
          Flatterm_gets - Flatterm_frees,
          ((Flatterm_gets - Flatterm_frees) * n) / 1024.);

}  /* fprint_flatterm_mem */

/*************
 *
 *   p_flatterm_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) memory usage statistics for data types
associated with the flatterm package.
*/

/* PUBLIC */
void p_flatterm_mem()
{
  fprint_flatterm_mem(stdout, TRUE);
}  /* p_flatterm_mem */

/*
 *  end of memory management
 */

/*************
 *
 *   flatterm_ident()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL flatterm_ident(Flatterm a, Flatterm b)
{
  Flatterm ai, bi;
  for (ai = a, bi = b; ai != a->end->next; ai = ai->next, bi = bi->next)
    if (ai->private_symbol != bi->private_symbol)
      return FALSE;
  return TRUE;
}  /* flatterm_ident */

/*************
 *
 *   zap_flatterm()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void zap_flatterm(Flatterm f)
{
  Flatterm fi = f;
  while (fi != f->end->next) {
    Flatterm tmp = fi;
    fi = fi->next;
    free_flatterm(tmp);
  }
}  /* zap_flatterm */

/*************
 *
 *   term_to_flatterm()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Flatterm term_to_flatterm(Term t)
{
  /* Iterative conversion from Term tree to Flatterm. */
  struct { Term src; Flatterm ft; int child; } stack[1000];
  int top = 0;
  Flatterm root, end_ptr;

  root = get_flatterm();
  root->private_symbol = t->private_symbol;
  ARITY(root) = ARITY(t);

  if (VARIABLE(t)) {
    root->end = root;
    root->size = 1;
    return root;
  }

  stack[0].src = t;
  stack[0].ft = root;
  stack[0].child = 0;
  end_ptr = root;

  while (top >= 0) {
    if (stack[top].child >= ARITY(stack[top].src)) {
      /* All children of this node processed. */
      stack[top].ft->end = end_ptr;
      /* Compute size: 1 + sum of children sizes. */
      {
        int n = 1;
        int i;
        Flatterm g = stack[top].ft->next;
        for (i = 0; i < ARITY(stack[top].src); i++) {
          n += g->size;
          g = g->end->next;
        }
        stack[top].ft->size = n;
      }
      top--;
    }
    else {
      int ci = stack[top].child;
      Term ch = ARG(stack[top].src, ci);
      Flatterm ft_ch = get_flatterm();
      stack[top].child++;

      ft_ch->private_symbol = ch->private_symbol;
      ARITY(ft_ch) = ARITY(ch);
      end_ptr->next = ft_ch;
      ft_ch->prev = end_ptr;
      end_ptr = ft_ch;

      if (VARIABLE(ch) || ARITY(ch) == 0) {
        ft_ch->end = ft_ch;
        ft_ch->size = 1;
        /* end_ptr already == ft_ch */
      }
      else {
        /* Push this child for further processing. */
        top++;
        stack[top].src = ch;
        stack[top].ft = ft_ch;
        stack[top].child = 0;
      }
    }
  }
  return root;
}  /* term_to_flatterm */

/*************
 *
 *   flatterm_to_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Term flatterm_to_term(Flatterm f)
{
  /* Iterative conversion from Flatterm to Term tree. */
  struct { Term t; Flatterm ft; int child; Flatterm g; } stack[1000];
  int top = -1;
  Term result;

  if (VARIABLE(f))
    return get_variable_term(VARNUM(f));

  result = get_rigid_term_dangerously(SYMNUM(f), ARITY(f));
  if (ARITY(f) == 0)
    return result;

  top = 0;
  stack[0].t = result;
  stack[0].ft = f;
  stack[0].child = 0;
  stack[0].g = f->next;

  while (top >= 0) {
    if (stack[top].child >= ARITY(stack[top].ft)) {
      top--;
      continue;
    }
    {
      int ci = stack[top].child;
      Flatterm g = stack[top].g;
      Term ch;

      if (VARIABLE(g)) {
        ch = get_variable_term(VARNUM(g));
        ARG(stack[top].t, ci) = ch;
        stack[top].g = g->end->next;
        stack[top].child++;
      }
      else {
        ch = get_rigid_term_dangerously(SYMNUM(g), ARITY(g));
        ARG(stack[top].t, ci) = ch;
        if (ARITY(g) == 0) {
          stack[top].g = g->end->next;
          stack[top].child++;
        }
        else {
          stack[top].child++;
          /* Save position for parent's next child. */
          Flatterm next_g_for_parent = g->end->next;
          /* We'll update parent's g when we pop back. But we need to
             set it now since this child will consume the flatterm range. */
          stack[top].g = next_g_for_parent;
          top++;
          stack[top].t = ch;
          stack[top].ft = g;
          stack[top].child = 0;
          stack[top].g = g->next;
        }
      }
    }
  }
  return result;
}  /* flatterm_to_term */

/*************
 *
 *   copy_flatterm()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Flatterm copy_flatterm(Flatterm f)
{
  /* Iterative flatterm copy. */
  struct { Flatterm src; Flatterm dst; Flatterm src_arg; int child; } stack[1000];
  int top;
  Flatterm root, end_ptr;

  root = get_flatterm();
  root->private_symbol = f->private_symbol;
  ARITY(root) = ARITY(f);

  if (ARITY(f) == 0) {
    root->end = root;
    root->size = 1;
    return root;
  }

  end_ptr = root;
  top = 0;
  stack[0].src = f;
  stack[0].dst = root;
  stack[0].src_arg = f->next;
  stack[0].child = 0;

  while (top >= 0) {
    if (stack[top].child >= ARITY(stack[top].src)) {
      /* Compute size and end for this node. */
      stack[top].dst->end = end_ptr;
      {
        int sz = 1;
        int i;
        Flatterm g = stack[top].dst->next;
        for (i = 0; i < ARITY(stack[top].src); i++) {
          sz += g->size;
          g = g->end->next;
        }
        stack[top].dst->size = sz;
      }
      top--;
    }
    else {
      Flatterm src_arg = stack[top].src_arg;
      Flatterm cp = get_flatterm();
      cp->private_symbol = src_arg->private_symbol;
      ARITY(cp) = ARITY(src_arg);
      end_ptr->next = cp;
      cp->prev = end_ptr;
      end_ptr = cp;

      stack[top].src_arg = src_arg->end->next;
      stack[top].child++;

      if (ARITY(src_arg) == 0) {
        cp->end = cp;
        cp->size = 1;
      }
      else {
        top++;
        stack[top].src = src_arg;
        stack[top].dst = cp;
        stack[top].src_arg = src_arg->next;
        stack[top].child = 0;
      }
    }
  }
  return root;
}  /* copy_flatterm */

/*************
 *
 *   print_flatterm()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void print_flatterm(Flatterm f)
{
  /* Iterative flatterm printing using explicit stack. */
  struct { Flatterm ft; Flatterm g; int child; } stack[1000];
  int top = -1;

  if (VARIABLE(f)) {
    if (VARNUM(f) < 3) printf("%c", 'x' + VARNUM(f));
    else if (VARNUM(f) < 6) printf("%c", 'r' + VARNUM(f));
    else printf("v%d", VARNUM(f));
    return;
  }
  if (CONSTANT(f)) {
    printf("%s", sn_to_str(SYMNUM(f)));
    return;
  }

  printf("%s(", sn_to_str(SYMNUM(f)));
  top = 0;
  stack[0].ft = f;
  stack[0].g = f->next;
  stack[0].child = 0;

  while (top >= 0) {
    if (stack[top].child >= ARITY(stack[top].ft)) {
      printf(")");
      top--;
      continue;
    }
    {
      Flatterm g = stack[top].g;
      if (stack[top].child > 0)
        printf(",");
      stack[top].child++;
      stack[top].g = g->end->next;

      if (VARIABLE(g)) {
        if (VARNUM(g) < 3) printf("%c", 'x' + VARNUM(g));
        else if (VARNUM(g) < 6) printf("%c", 'r' + VARNUM(g));
        else printf("v%d", VARNUM(g));
      }
      else if (CONSTANT(g)) {
        printf("%s", sn_to_str(SYMNUM(g)));
      }
      else {
        printf("%s(", sn_to_str(SYMNUM(g)));
        top++;
        stack[top].ft = g;
        stack[top].g = g->next;
        stack[top].child = 0;
      }
    }
  }
}  /* print_flatterm */

/*************
 *
 *   flatterm_symbol_count()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int flatterm_symbol_count(Flatterm f)
{
  /* Simply count all nodes in the flatterm sequence. */
  int n = 0;
  Flatterm fi;
  for (fi = f; fi != f->end->next; fi = fi->next)
    n++;
  return n;
}  /* flatterm_symbol_count */

/*************
 *
 *   p_flatterm()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void p_flatterm(Flatterm f)
{
  print_flatterm(f);
  printf("\n");
  fflush(stdout);
}  /* p_flatterm */

/*************
 *
 *   flat_occurs_in()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL flat_occurs_in(Flatterm t1, Flatterm t2)
{
  Flatterm t2i;
  for (t2i = t2; t2i != t2->end->next; t2i = t2i->next)
    if (flatterm_ident(t1, t2i))
      return TRUE;
  return FALSE;
}  /* flat_occurs_in */

/*************
 *
 *   flat_multiset_vars()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
I2list flat_multiset_vars(Flatterm f)
{
  I2list vars = NULL;
  Flatterm fi;
  for (fi = f; fi != f->end->next; fi = fi->next)
    if (VARIABLE(fi))
      vars = multiset_add(vars, VARNUM(fi));
  return vars;
}  /* flat_multiset_vars */

/*************
 *
 *   flat_variables_multisubset()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL flat_variables_multisubset(Flatterm a, Flatterm b)
{
  I2list a_vars = flat_multiset_vars(a);
  I2list b_vars = flat_multiset_vars(b);
  BOOL ok = i2list_multisubset(a_vars, b_vars);
  zap_i2list(a_vars);
  zap_i2list(b_vars);
  return ok;
}  /* flat_variables_multisubset */

/*************
 *
 *   flatterm_count_without_vars()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int flatterm_count_without_vars(Flatterm f)
{
  /* Count non-variable nodes in the flatterm sequence. */
  int n = 0;
  Flatterm fi;
  for (fi = f; fi != f->end->next; fi = fi->next)
    if (!VARIABLE(fi))
      n++;
  return n;
}  /* flatterm_count_without_vars */

