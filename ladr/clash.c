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

#include "clash.h"

#include <time.h>

/* Private definitions and types */

/*
 * memory management
 */

#define PTRS_CLASH PTRS(sizeof(struct clash))
static unsigned Clash_gets, Clash_frees;

/*
 * Adaptive timeout for clash_recurse() -- prevents indefinite hangs
 * in hyper/UR/binary resolution when the combinatorial clash search
 * explores too many possibilities.  Uses the same latching pattern
 * as pred_elim.c: counter-based throttle + time(NULL) + permanent flag.
 */

static time_t Clash_deadline = 0;     /* 0 = no timeout */
static BOOL   Clash_expired = FALSE;
static int    Clash_check_counter = 0;
#define CLASH_CHECK_INTERVAL 10000

/*************
 *
 *   Clash get_clash()
 *
 *************/

static
Clash get_clash(void)
{
  Clash p = get_cmem(PTRS_CLASH);
  Clash_gets++;
  return(p);
}  /* get_clash */

/*************
 *
 *    free_clash()
 *
 *************/

static
void free_clash(Clash p)
{
  free_mem(p, PTRS_CLASH);
  Clash_frees++;
}  /* free_clash */

/*************
 *
 *   fprint_clash_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for data types
associated with the clash package.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_clash_mem(FILE *fp, BOOL heading)
{
  int n;
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");

  n = sizeof(struct clash);
  fprintf(fp, "clash (%4d)        %11u%11u%11u%9.1f K\n",
          n, Clash_gets, Clash_frees,
          Clash_gets - Clash_frees,
          ((Clash_gets - Clash_frees) * n) / 1024.);

}  /* fprint_clash_mem */

/*************
 *
 *   p_clash_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) memory usage statistics for data types
associated with the clash package.
*/

/* PUBLIC */
void p_clash_mem()
{
  fprint_clash_mem(stdout, TRUE);
}  /* p_clash_mem */

/*
 *  end of memory management
 */

/*************
 *
 *   clash_timed_out() -- adaptive throttle check for clash_recurse()
 *
 *************/

static
BOOL clash_timed_out(void)
{
  if (Clash_expired)
    return TRUE;
  if (Clash_deadline == 0)
    return FALSE;
  Clash_check_counter++;
  if (Clash_check_counter < CLASH_CHECK_INTERVAL)
    return FALSE;
  Clash_check_counter = 0;
  if (time(NULL) >= Clash_deadline) {
    Clash_expired = TRUE;
    return TRUE;
  }
  return FALSE;
}  /* clash_timed_out */

/*************
 *
 *   set_clash_deadline()
 *
 *************/

/* DOCUMENTATION
Set the wall-clock deadline for clash_recurse() timeout.
Pass 0 to disable.  Resets the expired flag and counter.
*/

/* PUBLIC */
void set_clash_deadline(time_t deadline)
{
  Clash_deadline = deadline;
  Clash_expired = FALSE;
  Clash_check_counter = 0;
}  /* set_clash_deadline */

/*************
 *
 *   clash_deadline_expired()
 *
 *************/

/* DOCUMENTATION
Returns TRUE if the clash deadline has fired.
*/

/* PUBLIC */
BOOL clash_deadline_expired(void)
{
  return Clash_expired;
}  /* clash_deadline_expired */

/*************
 *
 *   append_clash()
 *
 *************/

/* DOCUMENTATION
This routine simply allocates a new clash node, links it in after the
given node, and returns the new node.
*/

/* PUBLIC */
Clash append_clash(Clash p)
{
  Clash q = get_clash();
  if (p != NULL)
    p->next = q;
  return q;
}  /* append_clash */

/*************
 *
 *   zap_clash()
 *
 *************/

/* DOCUMENTATION
Free a clash list.  Contexts in clashable nodes (which are assumed to exist
and be empty) are freed as well.
*/

/* PUBLIC */
void  zap_clash(Clash p)
{
  while (p != NULL) {
    Clash q = p;
    p = p->next;
    if (q->clashable && !q->clashed)
      free_context(q->sat_subst);
    free_clash(q);
  }
}  /* zap_clash */

/*************
 *
 *   atom_to_literal()
 *
 *************/

/* DOCUMENTATION
This routine takes an atom and returns its parent literal.
*/

/* PUBLIC */
Literals atom_to_literal(Term atom)
{
  Topform c = atom->container;
  Literals lit = (c == NULL ? NULL : c->literals);
  while (lit != NULL && lit->atom != atom)
    lit = lit->next;
  return lit;
}  /* atom_to_literal */

/*************
 *
 *   apply_lit()
 *
 *************/

/* DOCUMENTATION
This routine applies a substitution to a literal and returns the
instance.  The given literal is not changed.
*/

/* PUBLIC */
Literals apply_lit(Literals lit, Context c)
{
  return new_literal(lit->sign, apply(lit->atom, c));
}  /* apply_lit */

/*************
 *
 *   lit_position()
 *
 *************/

static
int lit_position(Topform c, Literals lit)
{
  int i = 1;
  Literals l = c->literals;
  while (l != NULL && l != lit) {
    i++;
    l = l->next;
  }
  if (l == lit)
    return i;
  else
    return -1;
}  /* lit_position */

/*************
 *
 *   resolve() - construct a clash-resolvent (for hyper or UR)
 *
 *************/

static
Topform resolve(Clash first, Just_type rule)
{
  Topform r = get_topform();
  Topform nuc =  first->nuc_lit->atom->container;
  Ilist j = ilist_append(NULL, nuc->id);
  Clash p;
  int n;

  /* First, include literals in the nucleus. */
  for (p = first; p != NULL; p = p->next) {
    if (!p->clashed)
      r->literals = append_literal(r->literals,
				   apply_lit(p->nuc_lit, p->nuc_subst));
  }

  r->attributes = cat_att(r->attributes,
			  inheritable_att_instances(nuc->attributes,
						    first->nuc_subst));

  /* Next, include literals in the satellites. */

  n = 1;  /* n-th nucleus literal, starting with 1 */
  for (p = first; p != NULL; p = p->next, n++) {
    if (p->clashed) {
      if (p->sat_lit == NULL) {
	/* special code for resolution with x=x */
	j = ilist_append(j, n);
	j = ilist_append(j, 0);
	j = ilist_append(j, 0);
      }
      else {
	Literals lit;
	Topform sat = p->sat_lit->atom->container;
	int sat_pos = lit_position(sat, p->sat_lit);
	j = ilist_append(j, n);
	j = ilist_append(j, sat->id);
	j = ilist_append(j, p->flipped ? -sat_pos : sat_pos);
	for (lit = sat->literals; lit != NULL; lit = lit->next) {
	  if (lit != p->sat_lit)
	    r->literals = append_literal(r->literals, 
					 apply_lit(lit,  p->sat_subst));
	}
	r->attributes = cat_att(r->attributes,
				inheritable_att_instances(sat->attributes,
							  p->sat_subst));
      }
    }
  }
  r->justification = resolve_just(j, rule);
  upward_clause_links(r);
  return r;
}  /* resolve */

/*************
 *
 *   clash_recurse()
 *
 *************/

static
void clash_recurse(Clash first,
		   Clash p,
		   BOOL (*sat_test) (Literals),
		   Just_type rule,
		   void (*proc_proc) (Topform))
{
  /* Iterative backtracking search over the clash list.
     Each stack frame represents one clashable literal being resolved.
     Phase encoding:
       0 = initial: start normal mate retrieval
       1 = iterating normal mates
       2 = start flipped mate retrieval (if eq)
       3 = iterating flipped mates
       4 = try built-in x=x resolution
       5 = done with this literal
  */
  struct {
    Clash cp;
    int phase;
    Term flip;       /* allocated flip term for phase 2/3 */
    Trail tr;        /* for x=x unification */
  } stack[500];
  int top = -1;
  Clash cur;

  /* Advance p past non-clashable / already-clashed entries. */
  cur = p;
  while (cur != NULL && (!cur->clashable || cur->clashed))
    cur = cur->next;

  if (cur == NULL) {
    /* All clashable literals mated. */
    Topform resolvent = resolve(first, rule);
    (*proc_proc)(resolvent);
    return;
  }

  /* Push initial frame. */
  top = 0;
  stack[0].cp = cur;
  stack[0].phase = 0;
  stack[0].flip = NULL;
  stack[0].tr = NULL;

  while (top >= 0) {
    Clash cp;
    int phase;

    if (clash_timed_out())
      break;  /* bail out; caller checks clash_deadline_expired() */

    cp = stack[top].cp;
    phase = stack[top].phase;

    if (phase == 0) {
      /* Start normal mate retrieval. */
      Term fnd_atom = mindex_retrieve_first(cp->nuc_lit->atom, cp->mate_index,
                                             UNIFY, cp->nuc_subst, cp->sat_subst,
                                             FALSE, &(cp->mate_pos));
      stack[top].phase = 1;
      if (fnd_atom != NULL) {
        Literals slit = atom_to_literal(fnd_atom);
        if ((*sat_test)(slit)) {
          cp->clashed = TRUE;
          cp->flipped = FALSE;
          cp->sat_lit = slit;
          /* Advance to next clashable literal. */
          Clash nxt = cp->next;
          while (nxt != NULL && (!nxt->clashable || nxt->clashed))
            nxt = nxt->next;
          if (nxt == NULL) {
            Topform resolvent = resolve(first, rule);
            (*proc_proc)(resolvent);
            cp->clashed = FALSE;
          }
          else {
            top++;
            stack[top].cp = nxt;
            stack[top].phase = 0;
            stack[top].flip = NULL;
            stack[top].tr = NULL;
            continue;
          }
        }
        /* Try next normal mate -- stay in phase 1. */
      }
      else {
        stack[top].phase = 2;  /* no normal mates; try flipped */
      }
      continue;
    }

    if (phase == 1) {
      /* Continue iterating normal mates. */
      cp->clashed = FALSE;
      Term fnd_atom = mindex_retrieve_next(cp->mate_pos);
      if (fnd_atom != NULL) {
        Literals slit = atom_to_literal(fnd_atom);
        if ((*sat_test)(slit)) {
          cp->clashed = TRUE;
          cp->flipped = FALSE;
          cp->sat_lit = slit;
          Clash nxt = cp->next;
          while (nxt != NULL && (!nxt->clashable || nxt->clashed))
            nxt = nxt->next;
          if (nxt == NULL) {
            Topform resolvent = resolve(first, rule);
            (*proc_proc)(resolvent);
            cp->clashed = FALSE;
          }
          else {
            top++;
            stack[top].cp = nxt;
            stack[top].phase = 0;
            stack[top].flip = NULL;
            stack[top].tr = NULL;
            continue;
          }
        }
        /* Stay in phase 1 for next iteration. */
      }
      else {
        stack[top].phase = 2;  /* exhausted normal; try flipped */
      }
      continue;
    }

    if (phase == 2) {
      /* Start flipped mate retrieval. */
      cp->clashed = FALSE;
      if (eq_term(cp->nuc_lit->atom)) {
        Term flip = top_flip(cp->nuc_lit->atom);
        stack[top].flip = flip;
        Term fnd_atom = mindex_retrieve_first(flip, cp->mate_index, UNIFY,
                                               cp->nuc_subst, cp->sat_subst,
                                               FALSE, &(cp->mate_pos));
        stack[top].phase = 3;
        if (fnd_atom != NULL) {
          Literals slit = atom_to_literal(fnd_atom);
          if ((*sat_test)(slit)) {
            cp->clashed = TRUE;
            cp->flipped = TRUE;
            cp->sat_lit = slit;
            Clash nxt = cp->next;
            while (nxt != NULL && (!nxt->clashable || nxt->clashed))
              nxt = nxt->next;
            if (nxt == NULL) {
              Topform resolvent = resolve(first, rule);
              (*proc_proc)(resolvent);
              cp->clashed = FALSE;
            }
            else {
              top++;
              stack[top].cp = nxt;
              stack[top].phase = 0;
              stack[top].flip = NULL;
              stack[top].tr = NULL;
              continue;
            }
          }
        }
        else {
          zap_top_flip(flip);
          stack[top].flip = NULL;
          stack[top].phase = 4;
        }
      }
      else {
        stack[top].phase = 4;  /* not eq; skip to x=x check */
      }
      continue;
    }

    if (phase == 3) {
      /* Continue iterating flipped mates. */
      cp->clashed = FALSE;
      Term fnd_atom = mindex_retrieve_next(cp->mate_pos);
      if (fnd_atom != NULL) {
        Literals slit = atom_to_literal(fnd_atom);
        if ((*sat_test)(slit)) {
          cp->clashed = TRUE;
          cp->flipped = TRUE;
          cp->sat_lit = slit;
          Clash nxt = cp->next;
          while (nxt != NULL && (!nxt->clashable || nxt->clashed))
            nxt = nxt->next;
          if (nxt == NULL) {
            Topform resolvent = resolve(first, rule);
            (*proc_proc)(resolvent);
            cp->clashed = FALSE;
          }
          else {
            top++;
            stack[top].cp = nxt;
            stack[top].phase = 0;
            stack[top].flip = NULL;
            stack[top].tr = NULL;
            continue;
          }
        }
      }
      else {
        zap_top_flip(stack[top].flip);
        stack[top].flip = NULL;
        stack[top].phase = 4;
      }
      continue;
    }

    if (phase == 4) {
      /* Try built-in resolution with x=x. */
      cp->clashed = FALSE;
      if (neg_eq(cp->nuc_lit)) {
        Term alpha = ARG(cp->nuc_lit->atom, 0);
        Term beta  = ARG(cp->nuc_lit->atom, 1);
        Trail tr = NULL;
        if (unify(alpha, cp->nuc_subst, beta, cp->nuc_subst, &tr)) {
          cp->clashed = TRUE;
          cp->sat_lit = NULL;
          stack[top].tr = tr;
          stack[top].phase = 5;
          Clash nxt = cp->next;
          while (nxt != NULL && (!nxt->clashable || nxt->clashed))
            nxt = nxt->next;
          if (nxt == NULL) {
            Topform resolvent = resolve(first, rule);
            (*proc_proc)(resolvent);
            cp->clashed = FALSE;
            undo_subst(tr);
            stack[top].tr = NULL;  /* prevent double-free in phase 5 */
            stack[top].phase = 5;
          }
          else {
            top++;
            stack[top].cp = nxt;
            stack[top].phase = 0;
            stack[top].flip = NULL;
            stack[top].tr = NULL;
            continue;
          }
        }
        else {
          stack[top].phase = 5;
        }
      }
      else {
        stack[top].phase = 5;
      }
      continue;
    }

    if (phase == 5) {
      /* Done with this literal. Undo x=x if applicable and pop. */
      if (stack[top].tr != NULL) {
        undo_subst(stack[top].tr);
        stack[top].tr = NULL;
      }
      cp->clashed = FALSE;
      top--;
      continue;
    }
  }
}  /* clash_recurse */

/*************
 *
 *   clash()
 *
 *************/

/* DOCUMENTATION
This routine takes a complete clash list and computes the
resolvents.
<UL>
<LI>clash -- a complete clash list corresponding to the nucleus.
<LI>sat_test -- a Boolean function on clauses which identifies
potential satellites (e.g., positive clauses for hyperresolution).
<LI>rule -- the name of the inference rule for the justification list
(see just.h).
<LI>proc_proc -- procedure for processing resolvents.
</UL>
*/

/* PUBLIC */
void clash(Clash c,
	   BOOL (*sat_test) (Literals),
	   Just_type rule,
	   void (*proc_proc) (Topform))
{
  clash_recurse(c, c, sat_test, rule, proc_proc);
}  /* clash */

