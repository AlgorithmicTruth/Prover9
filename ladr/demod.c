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

#include "demod.h"
#include "std_options.h"
#include "dollar.h"

/* Private definitions and types */

/* These are just statistics. */

static unsigned long long Demod_attempts = 0;
static unsigned long long Demod_rewrites = 0;

/*************
 *
 *   demodulator_type()
 *
 *************/

/* DOCUMENTATION
Return NOT_DEMODULATOR, ORIENTED, LEX_DEP_LR, LEX_DEP_RL, or LEX_DEP_BOTH.
*/

/* PUBLIC */
int demodulator_type(Topform c, int lex_dep_demod_lim, BOOL sane)
{
  if (!pos_eq_unit(c->literals))
    return NOT_DEMODULATOR;
  else {
    Term atom = c->literals->atom;
    Term alpha = ARG(atom, 0);
    Term beta  = ARG(atom, 1);
    int n_alpha = symbol_count(alpha);
    int n_beta = symbol_count(beta);

    /* AC mode (assoc_comm symbols declared): only equations oriented
       by the AC-compatible weight ordering (ac_term_order, applied in
       orient_equalities) are adopted, and only as ORIENTED: every
       rewrite then strictly decreases an AC-invariant measure, so
       demodulation terminates.  The lex-dependent paths below are not
       AC-compatible (the stock ordering cycles through AC-canonical
       forms; measured 437,900 demod-limit hits on a 4-clause problem)
       and are skipped.  With no AC symbols declared this test never
       fires. */
    if (assoc_comm_symbols()) {
      /* set(ac_demod), default clear: without clause-size bounding
         (item F), AC-oriented demodulators + btm AC matching drown the
         search in giant-but-weight-decreasing rewrite chains (EQP ran
         this combination WITH max_weight 70).  Default: AC equations
         paramodulate only. */
      if (!flag(ac_demod_id()))
        return NOT_DEMODULATOR;
      if (!oriented_eq(atom))
        return NOT_DEMODULATOR;
      /* ac_demod_weight: adopt as a demodulator only if the equation is
         light enough.  -1 = unbounded (every oriented AC equation is a
         demodulator, the prior behavior).  A finite bound makes AC
         demodulation gentler -- fewer/smaller demodulators, less
         back-demodulation churn -- so the collapsed regime doesn't
         disable its own useful intermediates.  A non-adopted equation
         still paramodulates; it just isn't used to rewrite. */
      {
        int adw = parm(ac_demod_weight_id());
        if (adw >= 0 && symbol_count(atom) > adw)
          return NOT_DEMODULATOR;
      }
      return ORIENTED;
    }

    if (oriented_eq(atom))
      return ORIENTED;
    else if (sane && n_alpha != n_beta)
      return NOT_DEMODULATOR;
    else if (lex_dep_demod_lim != -1 && 
	     n_alpha + n_beta + 1 > lex_dep_demod_lim)
      return NOT_DEMODULATOR;
    else {
      Plist alpha_vars = set_of_variables(alpha);
      Plist beta_vars = set_of_variables(beta);
      BOOL lr = plist_subset(beta_vars, alpha_vars) && !VARIABLE(alpha);
      BOOL rl = !renamable_flip_eq(atom) &&
		plist_subset(alpha_vars, beta_vars) && !VARIABLE(beta);
	
      zap_plist(alpha_vars);
      zap_plist(beta_vars);

      if (lr && rl)
	return LEX_DEP_BOTH;
      else if (lr)
	return LEX_DEP_LR;
      else if (rl)
	return LEX_DEP_RL;
      else
	return NOT_DEMODULATOR;
    }
  }
}  /* demodulator_type */

/*************
 *
 *   idx_demodulator()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void idx_demodulator(Topform c, int type, Indexop operation, Mindex idx)
{
  Term atom = c->literals->atom;
  Term alpha = ARG(atom, 0);
  Term beta  = ARG(atom, 1);

  if (type == ORIENTED ||
      type == LEX_DEP_LR ||
      type == LEX_DEP_BOTH)
    mindex_update(idx, alpha, operation);  /* index for left->right */

  if (type == LEX_DEP_RL ||
      type == LEX_DEP_BOTH)
    mindex_update(idx, beta, operation);   /* index for right->left */
}  /* idx_demodulator */

/*************
 *
 *   demod_attempts()
 *
 *************/

/* DOCUMENTATION
Return the number of rewrite attempts so far (for the whole process).
*/

/* PUBLIC */
unsigned long long demod_attempts()
{
  return Demod_attempts;
}  /* demod_attempts */

/*************
 *
 *   demod_rewrites()
 *
 *************/

/* DOCUMENTATION
Return the number of successful rewrites so far (for the whole process).
*/

/* PUBLIC */
unsigned long long demod_rewrites()
{
  return Demod_rewrites;
}  /* demod_rewrites */

/*************
 *
 *   demod()
 *
 *   For non-AC terms.
 *
 *************/

static
Term demod(Term t, Mindex demods, int flag, Ilist *just_head,
	   BOOL lex_order_vars)
{
  /* Iterative demodulation: traverse subterms bottom-up, rewrite at each
     node with re-traversal on rewrite.  Use explicit stack for the
     subterm traversal.  When a rewrite occurs, replace the current term
     and restart from its children.
     Small-buffer optimization: a small on-stack buffer handles the
     common shallow case at zero allocation cost; only pathologically
     deep terms spill to a growable heap array (safe_malloc/free
     doubling). */
  typedef struct { Term node; int child; } Sframe;
  Sframe sbo_buf[64];
  Sframe *stack = sbo_buf;
  int cap = 64;
  int top;

  if (term_flag(t, flag) || VARIABLE(t))
    return t;

  top = 0;
  stack[0].node = t;
  stack[0].child = 0;

  while (top >= 0) {
    Term cur = stack[top].node;

    if (term_flag(cur, flag) || VARIABLE(cur)) {
      top--;
      continue;
    }

    /* Phase 1: push unprocessed children. */
    if (stack[top].child < ARITY(cur)) {
      int ci = stack[top].child;
      Term ch = ARG(cur, ci);
      stack[top].child++;
      if (!term_flag(ch, flag) && !VARIABLE(ch)) {
        if (top + 1 >= cap) {
          int new_cap = cap * 2;
          Sframe *new_stack = safe_malloc(new_cap * sizeof(Sframe));
          memcpy(new_stack, stack, cap * sizeof(Sframe));
          if (stack != sbo_buf)
            safe_free(stack);
          stack = new_stack;
          cap = new_cap;
        }
        top++;
        stack[top].node = ch;
        stack[top].child = 0;
      }
      continue;
    }

    /* Phase 2: all children demodulated; try to rewrite cur. */
    {
      Context c = get_context();
      Discrim_pos dpos;
      Term found;
      BOOL rewritten = FALSE;

      Demod_attempts++;
      found = discrim_bind_retrieve_first(cur, demods->discrim_tree, c, &dpos);

      while (found != NULL) {
        Topform demodulator = found->container;
        Term atom = demodulator->literals->atom;
        Term alpha = ARG(atom, 0);
        Term beta = ARG(atom, 1);
        BOOL match_left = (found == alpha);
        Term other = (match_left ? beta : alpha);
        Term contractum = apply_demod(other, c, flag);
        BOOL ok;

        if (oriented_eq(atom))
          ok = TRUE;
        else
          ok = term_greater(cur, contractum, lex_order_vars);

        if (ok) {
          discrim_bind_cancel(dpos);
          Demod_rewrites++;
          zap_term(cur);
          *just_head = ilist_prepend(*just_head, demodulator->id);
          *just_head = ilist_prepend(*just_head, match_left ? 1 : 2);
          /* Replace cur with contractum and restart. */
          if (top == 0) {
            t = contractum;
          }
          else {
            /* Find which child of parent points to cur and update it. */
            /* The parent is at top-1; the child index is stack[top-1].child - 1
               because we already incremented past it. */
            int parent_ci = stack[top-1].child - 1;
            ARG(stack[top-1].node, parent_ci) = contractum;
          }
          stack[top].node = contractum;
          stack[top].child = 0;
          rewritten = TRUE;
          found = NULL;
        }
        else {
          zap_term(contractum);
          found = discrim_bind_retrieve_next(dpos);
        }
      }
      free_context(c);

      if (!rewritten) {
        term_flag_set(cur, flag);
        top--;
      }
    }
  }
  if (stack != sbo_buf)
    safe_free(stack);
  return t;
}  /* demod */

/*************
 *
 *    contract_bt
 *
 *************/

static
Term contract_bt(Term t, Mindex demods, int flag, Topform *demodulator_ptr)
{
  Mindex_pos pos;
  Term contractum, alpha;
  Topform demodulator = NULL;
  Context c = get_context();

  alpha = mindex_retrieve_first(t,demods,GENERALIZATION,NULL,c,TRUE,&pos);
				  
  if (alpha == NULL)
    contractum = NULL;
  else {
    Term atom;
    demodulator = alpha->container;
    atom = demodulator->literals->atom;
    contractum = apply_demod(ARG(atom,1), c, flag);
    if (c->partial_term) {
      /* Get copy, including marks that indicate normal terms. */
      Term partial = apply_demod(c->partial_term, NULL, flag);
      contractum = build_binary_term(SYMNUM(t), contractum, partial);
    }
    /* SOUNDNESS GUARD: every AC-demod match must be genuine.
       Instantiated demodulator lhs (+ partial remainder) equals subject t
       modulo AC.  match_ac must never return a match that fails this; if
       it does, an unsound rewrite is about to happen, so abort loudly.
       Runs on every rewrite, in every build.

       demod_bt already ac_canonical'd t, so only the constructed lhs
       needs canonicalization (no copy of t). */
    {
      Term chk = apply(ARG(atom,0), c);   /* instantiated demodulator LHS */
      int good;
      if (c->partial_term)
        chk = build_binary_term(SYMNUM(t), chk, copy_term(c->partial_term));
      ac_canonical(chk, -1);
      good = term_ident(chk, t);
      zap_term(chk);
      if (!good) {
        fprintf(stderr, "\n%% UNSOUND AC DEMOD MATCH: demodulator id %llu, "
                "subject: ", (unsigned long long) demodulator->id);
        fprint_term(stderr, t);
        fprintf(stderr, "\n");
        fatal_error("AC demod match verification failed "
                    "(instantiated lhs != subject mod AC)");
      }
    }
    mindex_retrieve_cancel(pos);
  }
  free_context(c);
  *demodulator_ptr = demodulator;
  return(contractum);
}  /* contract_bt */

/*************
 *
 *    demod_bt
 *
 *************/

static
Term demod_bt(Term t, Mindex demods, int psn, int flag,
	      I3list *steps, int *sequence)
{
  /* Iterative backtrack demodulation with AC canonicalization.
     Rewrite steps are recorded as <demodulator-id, sequence, direction>
     triples (the demod_just format).  Under AC canonicalization the
     sequence numbers are advisory (the term is reshaped between steps,
     so exact replay is not possible); direction is always 1 because
     AC-mode demodulators are ORIENTED only.
     Small-buffer optimization: a small on-stack buffer handles the
     common shallow case at zero allocation cost; only pathologically
     deep terms spill to a growable heap array (safe_malloc/free
     doubling).  (Stack-capacity/storage-strategy handling only; the
     step-recording logic below is untouched.) */
  typedef struct { Term node; int child; int parent_sn; } Sframe;
  Sframe sbo_buf[64];
  Sframe *stack = sbo_buf;
  int cap = 64;
  int top;

  if (term_flag(t, flag) || VARIABLE(t)) {
    term_flag_set(t, flag);
    return t;
  }

  top = 0;
  stack[0].node = t;
  stack[0].child = 0;
  stack[0].parent_sn = psn;

  while (top >= 0) {
    Term cur = stack[top].node;

    if (term_flag(cur, flag) || VARIABLE(cur)) {
      term_flag_set(cur, flag);
      top--;
      continue;
    }

    /* Phase 1: push unprocessed children. */
    if (stack[top].child < ARITY(cur)) {
      int ci = stack[top].child;
      Term ch = ARG(cur, ci);
      stack[top].child++;
      if (!term_flag(ch, flag) && !VARIABLE(ch)) {
        if (top + 1 >= cap) {
          int new_cap = cap * 2;
          Sframe *new_stack = safe_malloc(new_cap * sizeof(Sframe));
          memcpy(new_stack, stack, cap * sizeof(Sframe));
          if (stack != sbo_buf)
            safe_free(stack);
          stack = new_stack;
          cap = new_cap;
        }
        top++;
        stack[top].node = ch;
        stack[top].child = 0;
        stack[top].parent_sn = SYMNUM(cur);
      }
      continue;
    }

    /* Phase 2: all children demodulated. */
    {
      int cur_sn = SYMNUM(cur);
      int cur_psn = stack[top].parent_sn;

      if (cur_sn == cur_psn && is_assoc_comm(cur_sn)) {
        /* Part of an AC term -- leave it alone. */
        term_flag_set(cur, flag);
        top--;
      }
      else {
        Term contractum;
        Topform demodulator;
        /* Children are already demodulated (and marked).  For non-AC
           tops that means cur is already AC-canonical by induction --
           skip ac_canonical.  AC tops still need it (sort/RA), but
           ac_canonical early-outs when already sorted+RA. */
        if (is_assoc_comm(cur_sn))
          ac_canonical(cur, flag);
        else {
          int i, need = 0;
          for (i = 0; i < ARITY(cur); i++) {
            Term ch = ARG(cur, i);
            if (!VARIABLE(ch) && !term_flag(ch, flag)) {
              need = 1;
              break;
            }
          }
          if (need)
            ac_canonical(cur, flag);
        }
        Demod_attempts++;
        (*sequence)++;
        contractum = contract_bt(cur, demods, flag, &demodulator);
        if (contractum) {
          Demod_rewrites++;
          zap_term(cur);
          /* Fresh contractum from apply -- must canonicalize. */
          ac_canonical(contractum, flag);
          *steps = i3list_prepend(*steps, demodulator->id, *sequence, 1);
          /* Replace cur with contractum and restart. */
          if (top == 0) {
            t = contractum;
          }
          else {
            int parent_ci = stack[top-1].child - 1;
            ARG(stack[top-1].node, parent_ci) = contractum;
          }
          stack[top].node = contractum;
          stack[top].child = 0;
          /* parent_sn stays the same */
        }
        else {
          term_flag_set(cur, flag);
          top--;
        }
      }
    }
  }
  if (stack != sbo_buf)
    safe_free(stack);
  return t;
}  /* demod_bt */

/*************
 *
 *   demodulate()
 *
 *************/

/* DOCUMENTATION
This routine demodulates a term.  ID numbers of demodulators
are put on the front of just_head, so you'll probably want
to reverse the list before putting it into the clause justification.
*/

/* PUBLIC */
Term demodulate(Term t, Mindex demods, Ilist *just_head, BOOL lex_order_vars)
{
  int flag = claim_term_flag();
  Term result;

  if (demods->unif_type == ORDINARY_UNIF)
    result = demod(t, demods, flag, just_head, lex_order_vars);
  else {
    /* Legacy callers (rewriter, idfilter) take a plain id list. */
    I3list steps = NULL;
    I3list p;
    int sequence = 0;
    result = demod_bt(t, demods, -1, flag, &steps, &sequence);
    for (p = steps; p != NULL; p = p->next)
      *just_head = ilist_prepend(*just_head, p->i);
    zap_i3list(steps);
  }
  term_flag_clear_recursively(result, flag);
  release_term_flag(flag);
  return result;
}  /* demodulate */

/*************
 *
 *   demodulate_ac()
 *
 *************/

/* DOCUMENTATION
Demodulate a term modulo AC (backtrack matching, sub-multiset
rewriting at AC roots).  The index must be BACKTRACK_UNIF.  Rewrite
steps are prepended to *steps as <demodulator-id, sequence, direction>
triples for demod_just; *sequence carries the running subterm-visit
counter across the literals of one clause.  The result is
ac_canonical.
*/

/* PUBLIC */
Term demodulate_ac(Term t, Mindex demods, I3list *steps, int *sequence)
{
  int flag = claim_term_flag();
  Term result = demod_bt(t, demods, -1, flag, steps, sequence);
  term_flag_clear_recursively(result, flag);
  release_term_flag(flag);
  return result;
}  /* demodulate_ac */

/*************
 *
 *   demod1_recurse()
 *
 *   For non-AC terms.  Similar to demod(), but do at most one rewrite
 *   and return a position.
 *
 *************/

static
Term demod1_recurse(Term top_term, Term t, Topform demodulator, int direction,
		    Ilist *ipos, BOOL lex_order_vars)
{
  /* Iterative innermost-leftmost single rewrite.
     Small-buffer optimization: a small on-stack buffer handles the
     common shallow case at zero allocation cost; only pathologically
     deep terms spill to a growable heap array (safe_malloc/free
     doubling). */
  typedef struct { Term node; int child; } Sframe;
  Sframe sbo_buf[64];
  Sframe *stack = sbo_buf;
  int cap = 64;
  int stop;

  if (VARIABLE(t))
    return t;

  stop = 0;
  stack[0].node = t;
  stack[0].child = 0;

  while (stop >= 0 && *ipos == NULL) {
    Term cur = stack[stop].node;

    if (VARIABLE(cur)) {
      stop--;
      continue;
    }

    /* Push unprocessed children. */
    if (stack[stop].child < ARITY(cur) && *ipos == NULL) {
      int ci = stack[stop].child;
      Term ch = ARG(cur, ci);
      stack[stop].child++;
      if (!VARIABLE(ch)) {
        if (stop + 1 >= cap) {
          int new_cap = cap * 2;
          Sframe *new_stack = safe_malloc(new_cap * sizeof(Sframe));
          memcpy(new_stack, stack, cap * sizeof(Sframe));
          if (stack != sbo_buf)
            safe_free(stack);
          stack = new_stack;
          cap = new_cap;
        }
        stop++;
        stack[stop].node = ch;
        stack[stop].child = 0;
      }
      continue;
    }

    if (*ipos != NULL)
      break;

    /* All children processed; try rewrite at this node. */
    {
      Context c1 = get_context();
      Trail tr = NULL;
      Term atom = demodulator->literals->atom;
      BOOL match_left = (direction == 1);
      Term t1 = ARG(atom, match_left ? 0 : 1);
      Term t2 = ARG(atom, match_left ? 1 : 0);

      if (match(t1, c1, cur, &tr)) {
        Term contractum = apply_demod(t2, c1, -1);
        BOOL ok;

        if (oriented_eq(atom))
          ok = TRUE;
        else
          ok = term_greater(cur, contractum, lex_order_vars);

        if (ok) {
          undo_subst(tr);
          *ipos = position_of_subterm(top_term, cur);
          /* Replace cur in parent. */
          if (stop > 0) {
            int parent_ci = stack[stop-1].child - 1;
            ARG(stack[stop-1].node, parent_ci) = contractum;
          }
          else {
            t = contractum;
          }
          zap_term(cur);
        }
        else
          zap_term(contractum);
      }
      free_context(c1);
    }
    stop--;
  }
  if (stack != sbo_buf)
    safe_free(stack);
  return t;
}  /* demod1_recurse */

/*************
 *
 *   demod1()
 *
 *************/

/* DOCUMENTATION
Special purpose demodulation routine.
<P>
Given a clause and a demodulator that rewrites the clause,
rewrite the innermost leftmost subterm to which
the demodulator applies.  Return the rewritten term
and the position vectors of the from and into terms.
*/

/* PUBLIC */
void demod1(Topform c, Topform demodulator, int direction,
	    Ilist *fpos, Ilist *ipos,
	    BOOL lex_order_vars)
{
  Term result;
  Literals lit;
  int n = 0;

  for (lit = c->literals, *ipos = NULL; lit && *ipos == NULL; lit=lit->next) {
    n++;
    result = demod1_recurse(lit->atom, lit->atom, demodulator,direction,ipos,
			    lex_order_vars);
  }
  (void) result;  /* side effects already applied to clause */

  if (*ipos == NULL)
    fatal_error("demod1, clause not rewritable");
  else {
    *fpos = ilist_prepend(NULL, direction);  /* side of demodulator */
    *fpos = ilist_prepend(*fpos, 1);  /* literal number */
    *ipos = ilist_prepend(*ipos, n);  /* literal number */
  }

}  /* demod1 */

/*************
 *
 *   part_recurse()
 *
 *************/

static
Term part_recurse(Term top_term, Term t, Topform demod, int target, int direction,
		  int *sequence, Ilist *ipos)
{
  /* Iterative innermost-leftmost search for the target-th matchable subterm.
     Small-buffer optimization: a small on-stack buffer handles the
     common shallow case at zero allocation cost; only pathologically
     deep terms spill to a growable heap array (safe_malloc/free
     doubling). */
  typedef struct { Term node; int child; } Sframe;
  Sframe sbo_buf[64];
  Sframe *stack = sbo_buf;
  int cap = 64;
  int stop;

  if (VARIABLE(t))
    return t;

  stop = 0;
  stack[0].node = t;
  stack[0].child = 0;

  while (stop >= 0 && *ipos == NULL) {
    Term cur = stack[stop].node;

    if (VARIABLE(cur)) {
      stop--;
      continue;
    }

    /* Push unprocessed children. */
    if (stack[stop].child < ARITY(cur) && *ipos == NULL) {
      int ci = stack[stop].child;
      Term ch = ARG(cur, ci);
      stack[stop].child++;
      if (!VARIABLE(ch)) {
        if (stop + 1 >= cap) {
          int new_cap = cap * 2;
          Sframe *new_stack = safe_malloc(new_cap * sizeof(Sframe));
          memcpy(new_stack, stack, cap * sizeof(Sframe));
          if (stack != sbo_buf)
            safe_free(stack);
          stack = new_stack;
          cap = new_cap;
        }
        stop++;
        stack[stop].node = ch;
        stack[stop].child = 0;
      }
      continue;
    }

    if (*ipos != NULL || *sequence >= target) {
      stop--;
      continue;
    }

    /* All children done; try this node. */
    (*sequence)++;
    if (*sequence == target) {
      Term alpha, beta;
      Context subst = get_context();
      Trail tr = NULL;
      if (direction == 1) {
        alpha = ARG(demod->literals->atom, 0);
        beta  = ARG(demod->literals->atom, 1);
      }
      else {
        alpha = ARG(demod->literals->atom, 1);
        beta  = ARG(demod->literals->atom, 0);
      }
      if (match(alpha, subst, cur, &tr)) {
        Term result = apply(beta, subst);
        undo_subst(tr);
        *ipos = position_of_subterm(top_term, cur);
        if (stop > 0) {
          int parent_ci = stack[stop-1].child - 1;
          ARG(stack[stop-1].node, parent_ci) = result;
        }
        else {
          t = result;
        }
        zap_term(cur);
      }
      /* else: the target-th node doesn't actually match ordinarily --
         most commonly because AC canonicalization elsewhere in the term
         has invalidated the recorded position (demod_bt's own comment:
         sequence numbers are advisory under AC).  Leave *ipos NULL and
         fall through without crashing; the loop below unwinds (sequence
         is now >= target, so every remaining node is skipped) and
         particular_demod's existing "*ipos == NULL" check reports this
         as an ordinary "not rewritable" failure -- which xproofs.c's
         DEMOD_JUST loop already treats as an expand_failed signal (now
         handled per-clause via expand_proof's fallback, not fatal to
         the whole proof or the process). */
      free_context(subst);
    }
    stop--;
  }
  if (stack != sbo_buf)
    safe_free(stack);
  return t;
}  /* part_recurse */

/*************
 *
 *   particular_demod()
 *
 *************/

/* DOCUMENTATION
Special purpose demodulation routine.
<P>
Given a clause and <demodulator,positition,direction> which applies to the
clause, return the rewritten clause and the position vectors of the from
and into terms.
*/

/* PUBLIC */
BOOL particular_demod(Topform c, Topform demodulator, int target, int direction,
		      Ilist *fpos, Ilist *ipos)
{
  Literals lit;
  int n = 0;
  int sequence = 0;

  for (lit = c->literals, *ipos = NULL; lit && *ipos == NULL; lit=lit->next) {
    n++;
    part_recurse(lit->atom, lit->atom, demodulator, target, direction, &sequence, ipos);
  }

  if (*ipos == NULL) {
    /* Silent failure: under AC compound-chain expansion the recorded
       sequence is often stale, and callers (particular_demod_scan /
       expand_proof) retry other positions.  Spamming stderr here made
       those scans unusable. */
    return FALSE;
  }
  else {
    *fpos = ilist_prepend(NULL, direction);  /* side of demodulator */
    *fpos = ilist_prepend(*fpos, 1);  /* literal number */
    *ipos = ilist_prepend(*ipos, n);  /* literal number */
    upward_clause_links(c);
    return TRUE;
  }
}  /* particular_demod */

