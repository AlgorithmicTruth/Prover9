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

#include "basic.h"

/*
  In "Basic Paramodlation", we do not paramodulate into terms that
  arise by instantiation.  Another way to look at it (and the way
  it is rigorously defined), is that substitutions (instantiations) 
  are kept separate from clauses.  The skeleton of the clause
  stays the same (except that paramoulation substitutes the 
  skeleton from the "from" parent), and all instantiations occur
  in the associationed substitution.

  In this implementation, we do not keep separate substitutions.
  Instead, we mark the subterms that arose by substitution; that
  is the "nonbasic" subterms which are inadmissible "into" terms.

  Basic paramodulation is complete; but more important, it can
  be powerful (e.g., the Robbins proof).  The paper [McCune, "33
  Basic Test Problems"] reports on experiments showing that it
  can be useful.

  Things to be aware of:

  1. The terms that are marked are the "nonbasic" terms, that is,
  the inadmissible "into" terms.  Variables are always inadmissible,
  and are never marked.

  2. Things get messy for subsumption and demodulation, and I'm not
  clear on what's exactly what's required for completeness.

  3. Forward subsumption.  If the subsumer is less basic than the
  new clause, the subsumer should acquire some of the nonbasic
  marks of the new clause.  Not implemented.  Similar for back
  subsumption

  4. Should demodulation be applied to nonbasic terms?  I think yes,
  from a practical point of view (I don't know about completeness).
  If it is, then a nonbasic term can have a basic subterm.  Should
  we paramodulate into those?  I think not.

  5. Basic paramodulation can require a greater max_weight.

*/
  
/* Private definitions and types */

static BOOL Basic_paramodulation = FALSE; /* Is basic paramod enabled? */
static int Nonbasic_flag         = -1;    /* termflag to mark nonbasic terms */

/*************
 *
 *   init_basic_paramod(void)
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_basic_paramod(void)
{
  if (Nonbasic_flag != -1)
    fatal_error("init_basic_paramod, called more than once");
  Nonbasic_flag = claim_term_flag();  /* allocate a termflag */
}  /* init_basic_paramod */

/*************
 *
 *   set_basic_paramod()
 *
 *************/

/* DOCUMENTATION
Set or clear basic paramodulation.
*/

/* PUBLIC */
void set_basic_paramod(BOOL flag)
{
  Basic_paramodulation = flag;
}  /* set_basic_paramod */

/*************
 *
 *   basic_paramod()
 *
 *************/

/* DOCUMENTATION
Is basic paramodulation enabled?
*/

/* PUBLIC */
BOOL basic_paramod(void)
{
  return Basic_paramodulation;
}  /* basic_paramod */

/*************
 *
 *   mark_term_nonbasic()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void mark_term_nonbasic(Term t)
{
  if (Nonbasic_flag == -1)
    fatal_error("mark_term_nonbasic: init_basic() was not called");
  term_flag_set(t, Nonbasic_flag);
}  /* mark_term_nonbasic */

/*************
 *
 *   mark_all_nonbasic()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void mark_all_nonbasic(Term t)
{
  /* Iterative pre-order traversal. */
  Term stack[1000];
  int top = 0;
  stack[0] = t;

  while (top >= 0) {
    Term cur = stack[top];
    top--;
    if (!VARIABLE(cur)) {
      int i;
      mark_term_nonbasic(cur);
      for (i = ARITY(cur) - 1; i >= 0; i--) {
        top++;
        stack[top] = ARG(cur, i);
      }
    }
  }
}  /* mark_all_nonbasic */

/*************
 *
 *   nonbasic_term()
 *
 *************/

/* DOCUMENTATION
Check if a term is nonbasic.  This simply checks the "nonbasic" mark.
*/

/* PUBLIC */
BOOL nonbasic_term(Term t)
{
  return term_flag(t, Nonbasic_flag);
}  /* nonbasic_term */

/*************
 *
 *   basic_term()
 *
 *************/

/* DOCUMENTATION
Check if a term is basic.  This simply checks the "nonbasic" mark.
*/

/* PUBLIC */
BOOL basic_term(Term t)
{
  return !term_flag(t, Nonbasic_flag);
}  /* basic_term */

/*************
 *
 *   nonbasic_flag()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int nonbasic_flag(void)
{
  return Nonbasic_flag;
}  /* nonbasic_flag */

/*************
 *
 *    Term apply_basic(term, context) -- Apply a substitution to a term.
 *
 *************/

/* DOCUMENTATION
This is similar to apply(), but it makes "nonbasic" marks for
"basic paramodulation".
*/

/* PUBLIC */
Term apply_basic(Term t, Context c)
{
  /* Iterative substitution application with basic-paramod marking.
     Stack frames: (src_raw, src_deref, dst_parent, child_index). */
  struct { Term raw; Term deref; Term dst; int child; } stack[1000];
  int top = -1;
  Term result;
  Term raw_t = t;

  DEREFERENCE(t, c)

  if (VARIABLE(t)) {
    if (!c)
      return get_variable_term(VARNUM(t));
    else
      return get_variable_term(c->multiplier * MAX_VARS + VARNUM(t));
  }

  /* Build root. */
  result = get_rigid_term_like(t);
  if (VARIABLE(raw_t))
    mark_all_nonbasic(result);
  else if (nonbasic_term(t))
    mark_term_nonbasic(result);

  if (ARITY(t) > 0) {
    top = 0;
    stack[0].raw = raw_t;
    stack[0].deref = t;
    stack[0].dst = result;
    stack[0].child = 0;
  }

  while (top >= 0) {
    if (stack[top].child >= ARITY(stack[top].deref)) {
      top--;
      continue;
    }
    {
      int ci = stack[top].child;
      Term ch_raw = ARG(stack[top].deref, ci);  /* for child of deref, use raw child */
      Term ch_deref;
      Term ch_dst;

      /* We need the raw (pre-deref) child to check if it was a variable. */
      /* For the top-level call, raw is the non-dereferenced original. */
      /* For children, the "raw" source is the child of the dereferenced parent. */
      ch_raw = ARG(stack[top].deref, ci);
      ch_deref = ch_raw;
      DEREFERENCE(ch_deref, c)

      stack[top].child++;

      if (VARIABLE(ch_deref)) {
        if (!c)
          ch_dst = get_variable_term(VARNUM(ch_deref));
        else
          ch_dst = get_variable_term(c->multiplier * MAX_VARS + VARNUM(ch_deref));
        ARG(stack[top].dst, ci) = ch_dst;
      }
      else {
        ch_dst = get_rigid_term_like(ch_deref);
        if (VARIABLE(ch_raw))
          mark_all_nonbasic(ch_dst);
        else if (nonbasic_term(ch_deref))
          mark_term_nonbasic(ch_dst);
        ARG(stack[top].dst, ci) = ch_dst;
        if (ARITY(ch_deref) > 0) {
          top++;
          stack[top].raw = ch_raw;
          stack[top].deref = ch_deref;
          stack[top].dst = ch_dst;
          stack[top].child = 0;
        }
      }
    }
  }
  return result;
}  /* apply_basic */

/*************
 *
 *    apply_basic_substitute()
 *
 *************/

/* DOCUMENTATION
This is similar to apply_substitute(), but it makes "nonbasic" marks for
"basic paramodulation".
*/

/* PUBLIC */
Term apply_basic_substitute(Term t, Term beta, Context c_from,
			    Term into_term, Context c_into)
{
  /* Iterative term copy with substitution at into_term. */
  struct { Term src; Term dst; int child; } stack[1000];
  int top = -1;
  Term result;

  if (t == into_term)
    return apply_basic(beta, c_from);
  if (VARIABLE(t))
    return apply_basic(t, c_into);

  result = get_rigid_term_like(t);
  if (nonbasic_term(t))
    mark_term_nonbasic(result);

  if (ARITY(t) > 0) {
    top = 0;
    stack[0].src = t;
    stack[0].dst = result;
    stack[0].child = 0;
  }

  while (top >= 0) {
    if (stack[top].child >= ARITY(stack[top].src)) {
      top--;
      continue;
    }
    {
      int ci = stack[top].child;
      Term ch = ARG(stack[top].src, ci);
      stack[top].child++;

      if (ch == into_term) {
        ARG(stack[top].dst, ci) = apply_basic(beta, c_from);
      }
      else if (VARIABLE(ch)) {
        ARG(stack[top].dst, ci) = apply_basic(ch, c_into);
      }
      else {
        Term ch_dst = get_rigid_term_like(ch);
        if (nonbasic_term(ch))
          mark_term_nonbasic(ch_dst);
        ARG(stack[top].dst, ci) = ch_dst;
        if (ARITY(ch) > 0) {
          top++;
          stack[top].src = ch;
          stack[top].dst = ch_dst;
          stack[top].child = 0;
        }
      }
    }
  }
  return result;
}  /* apply_basic_substitute */

/*************
 *
 *   clear_all_nonbasic_marks()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void clear_all_nonbasic_marks(Term t)
{
  /* Iterative pre-order traversal. */
  Term stack[1000];
  int top = 0;
  stack[0] = t;

  while (top >= 0) {
    Term cur = stack[top];
    top--;
    if (!VARIABLE(cur)) {
      int i;
      term_flag_clear(cur, Nonbasic_flag);
      for (i = ARITY(cur) - 1; i >= 0; i--) {
        top++;
        stack[top] = ARG(cur, i);
      }
    }
  }
}  /* clear_all_nonbasic_marks */

/*************
 *
 *   p_term_basic()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void p_term_basic(Term t)
{
  /* Iterative term printing using explicit stack. */
  struct { Term node; int child; } stack[1000];
  int top = 0;
  stack[0].node = t;
  stack[0].child = 0;

  while (top >= 0) {
    Term cur = stack[top].node;
    int ci = stack[top].child;

    if (ci == 0) {
      /* First visit: print prefix. */
      if (VARIABLE(cur)) {
        printf("v%d", VARNUM(cur));
        top--;
        continue;
      }
      if (basic_term(cur))
        printf("#");
      fprint_sym(stdout, SYMNUM(cur));
      if (COMPLEX(cur))
        printf("(");
    }

    if (!VARIABLE(cur) && COMPLEX(cur) && ci < ARITY(cur)) {
      if (ci > 0)
        printf(",");
      stack[top].child++;
      top++;
      stack[top].node = ARG(cur, ci);
      stack[top].child = 0;
    }
    else {
      if (!VARIABLE(cur) && COMPLEX(cur))
        printf(")");
      top--;
    }
  }
  fflush(stdout);
}  /* p_term_basic */
