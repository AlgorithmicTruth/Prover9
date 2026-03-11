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

#include "termorder.h"
#include "multiset.h"

/* Private definitions and types */

Order_method Ordering_method = LRPO_METHOD; /* see assign_order_method() */

#define TERM_PAIR_STACK_SIZE 1000
#define TERM_STACK_SIZE 1000

/*************
 *
 *   assign_order_method()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void assign_order_method(Order_method method)
{
  Ordering_method = method;
}  /* assign_order_method */

/*************
 *
 *   term_compare_basic(t1, t2) -- iterative
 *
 *************/

/* DOCUMENTATION
This routine compares two terms.
variable < nonvariable; within type, the order is by VARNUM
and lexigocgaphic by ASCII ordering.  The range of return values is
{SAME_AS, GREATER_THAN, LESS_THAN}.
*/

/* PUBLIC */
Ordertype term_compare_basic(Term t1, Term t2)
{
  struct { Term a; Term b; int child; } stack[TERM_PAIR_STACK_SIZE];
  int top = 0;
  Ordertype rc = SAME_AS;

  stack[0].a = t1;
  stack[0].b = t2;
  stack[0].child = 0;

  while (top >= 0) {
    Term a = stack[top].a;
    Term b = stack[top].b;

    if (!VARIABLE(a) && !VARIABLE(b)) {
      char *s1 = sn_to_str(SYMNUM(a));
      char *s2 = sn_to_str(SYMNUM(b));
      int a1 = ARITY(a);
      int a2 = ARITY(b);
      if (str_ident(s1, s2)) {
        int i = stack[top].child;
        int minarity = (a1 < a2 ? a1 : a2);
        if (i < minarity) {
          /* Push next child pair */
          if (top + 1 >= TERM_PAIR_STACK_SIZE)
            fatal_error("term_compare_basic: stack overflow");
          stack[top].child = i + 1;
          top++;
          stack[top].a = ARG(a, i);
          stack[top].b = ARG(b, i);
          stack[top].child = 0;
          continue;
        }
        /* All compared children were SAME_AS; compare arities */
        rc = (a1 < a2 ? LESS_THAN : (a1 > a2 ? GREATER_THAN : SAME_AS));
        top--;
        if (top >= 0 && rc != SAME_AS)
          goto done;
        /* rc == SAME_AS: continue with parent's next child */
      }
      else {
        int r = strcmp(s1, s2);
        rc = (r < 0 ? LESS_THAN : (r > 0 ? GREATER_THAN : SAME_AS));
        top--;
        if (top >= 0 && rc != SAME_AS)
          goto done;
      }
    }
    else if (VARIABLE(a) && VARIABLE(b)) {
      if (VARNUM(a) == VARNUM(b))
        rc = SAME_AS;
      else
        rc = (VARNUM(a) > VARNUM(b) ? GREATER_THAN : LESS_THAN);
      top--;
      if (top >= 0 && rc != SAME_AS)
        goto done;
    }
    else {
      rc = VARIABLE(a) ? LESS_THAN : GREATER_THAN;
      top--;
      if (top >= 0)
        goto done;
    }
  }

  return rc;

done:
  /* rc is not SAME_AS, so it propagates all the way up (the for loop
     in the original breaks on rc != SAME_AS). */
  return rc;
}  /* term_compare_basic */

/*************
 *
 *    int term_compare_ncv(t1, t2) -- iterative
 *
 *************/

/* DOCUMENTATION
This routine compares two terms.  The ordering is total:
CONSTANT < COMPLEX < VARIABLE; within type, the order is by VARNUM
and lexigocgaphic by SYMNUM.  The range of return values is<BR>
{SAME_AS, GREATER_THAN, LESS_THAN}.
*/

/* PUBLIC */
Ordertype term_compare_ncv(Term t1, Term t2)
{
  struct { Term a; Term b; int child; } stack[TERM_PAIR_STACK_SIZE];
  int top = 0;
  Ordertype rc = SAME_AS;

  stack[0].a = t1;
  stack[0].b = t2;
  stack[0].child = 0;

  while (top >= 0) {
    Term a = stack[top].a;
    Term b = stack[top].b;

    if ((COMPLEX(a) && COMPLEX(b)) || (CONSTANT(a) && CONSTANT(b))) {
      if (SYMNUM(a) == SYMNUM(b)) {
        int i = stack[top].child;
        if (i < ARITY(a)) {
          if (top + 1 >= TERM_PAIR_STACK_SIZE)
            fatal_error("term_compare_ncv: stack overflow");
          stack[top].child = i + 1;
          top++;
          stack[top].a = ARG(a, i);
          stack[top].b = ARG(b, i);
          stack[top].child = 0;
          continue;
        }
        rc = SAME_AS;
        top--;
        /* SAME_AS: continue with parent */
      }
      else {
        rc = (SYMNUM(a) > SYMNUM(b) ? GREATER_THAN : LESS_THAN);
        top--;
        goto done;
      }
    }
    else if (VARIABLE(a) && VARIABLE(b)) {
      if (VARNUM(a) == VARNUM(b))
        rc = SAME_AS;
      else
        rc = (VARNUM(a) > VARNUM(b) ? GREATER_THAN : LESS_THAN);
      top--;
      if (top >= 0 && rc != SAME_AS)
        goto done;
    }
    else {
      /* Different types */
      if (VARIABLE(a))
        rc = GREATER_THAN;
      else if (VARIABLE(b))
        rc = LESS_THAN;
      else if (COMPLEX(a))
        rc = GREATER_THAN;
      else
        rc = LESS_THAN;  /* CONSTANT(a) && COMPLEX(b) */
      top--;
      goto done;
    }
  }

  return rc;

done:
  return rc;
}  /* term_compare_ncv */

/*************
 *
 *    int term_compare_vcp(t1, t2) -- iterative
 *
 *************/

/* DOCUMENTATION
This routine compares two terms.  The ordering is total:
VARIABLE < CONSTANT < COMPLEX; within type, the order is by VARNUM
and lexigocgaphic by SYMNUM.  The range of return values is<BR>
{SAME_AS, GREATER_THAN, LESS_THAN}.
*/

/* PUBLIC */
Ordertype term_compare_vcp(Term t1, Term t2)
{
  struct { Term a; Term b; int child; } stack[TERM_PAIR_STACK_SIZE];
  int top = 0;
  Ordertype rc = SAME_AS;

  stack[0].a = t1;
  stack[0].b = t2;
  stack[0].child = 0;

  while (top >= 0) {
    Term a = stack[top].a;
    Term b = stack[top].b;

    if ((COMPLEX(a) && COMPLEX(b)) || (CONSTANT(a) && CONSTANT(b))) {
      if (SYMNUM(a) == SYMNUM(b)) {
        int i = stack[top].child;
        if (i < ARITY(a)) {
          if (top + 1 >= TERM_PAIR_STACK_SIZE)
            fatal_error("term_compare_vcp: stack overflow");
          stack[top].child = i + 1;
          top++;
          stack[top].a = ARG(a, i);
          stack[top].b = ARG(b, i);
          stack[top].child = 0;
          continue;
        }
        rc = SAME_AS;
        top--;
      }
      else {
        rc = (SYMNUM(a) > SYMNUM(b) ? GREATER_THAN : LESS_THAN);
        top--;
        goto done;
      }
    }
    else if (VARIABLE(a) && VARIABLE(b)) {
      if (VARNUM(a) == VARNUM(b))
        rc = SAME_AS;
      else
        rc = (VARNUM(a) > VARNUM(b) ? GREATER_THAN : LESS_THAN);
      top--;
      if (top >= 0 && rc != SAME_AS)
        goto done;
    }
    else {
      /* Different types */
      if (VARIABLE(a))
        rc = LESS_THAN;
      else if (VARIABLE(b))
        rc = GREATER_THAN;
      else if (COMPLEX(a))
        rc = GREATER_THAN;
      else
        rc = LESS_THAN;  /* CONSTANT(a) && COMPLEX(b) */
      top--;
      goto done;
    }
  }

  return rc;

done:
  return rc;
}  /* term_compare_vcp */

/*************
 *
 *   term_compare_vr(t1, t2) -- iterative
 *
 *************/

/* DOCUMENTATION
This routine compares two terms.
variable < nonvariable; within type, the order is by VARNUM
and lexigocgaphic by symbol precedence.  The range of return values is<BR>
{SAME_AS, GREATER_THAN, LESS_THAN}.
*/

/* PUBLIC */
Ordertype term_compare_vr(Term t1, Term t2)
{
  struct { Term a; Term b; int child; } stack[TERM_PAIR_STACK_SIZE];
  int top = 0;
  Ordertype rc = SAME_AS;

  stack[0].a = t1;
  stack[0].b = t2;
  stack[0].child = 0;

  while (top >= 0) {
    Term a = stack[top].a;
    Term b = stack[top].b;

    if (!VARIABLE(a) && !VARIABLE(b)) {
      if (SYMNUM(a) == SYMNUM(b)) {
        int i = stack[top].child;
        if (i < ARITY(a)) {
          if (top + 1 >= TERM_PAIR_STACK_SIZE)
            fatal_error("term_compare_vr: stack overflow");
          stack[top].child = i + 1;
          top++;
          stack[top].a = ARG(a, i);
          stack[top].b = ARG(b, i);
          stack[top].child = 0;
          continue;
        }
        rc = SAME_AS;
        top--;
      }
      else {
        rc = sym_precedence(SYMNUM(a), SYMNUM(b));
        top--;
        goto done;
      }
    }
    else if (VARIABLE(a) && VARIABLE(b)) {
      if (VARNUM(a) == VARNUM(b))
        rc = SAME_AS;
      else
        rc = (VARNUM(a) > VARNUM(b) ? GREATER_THAN : LESS_THAN);
      top--;
      if (top >= 0 && rc != SAME_AS)
        goto done;
    }
    else {
      rc = VARIABLE(a) ? LESS_THAN : GREATER_THAN;
      top--;
      goto done;
    }
  }

  return rc;

done:
  return rc;
}  /* term_compare_vr */

/*************
 *
 *   flatterm_compare_vr(t1, t2) -- iterative
 *
 *************/

/* DOCUMENTATION
This routine compares two flatterms.
variable < nonvariable; within type, the order is by VARNUM
and lexigocgaphic by symbol precedence.  The range of return values is<BR>
{SAME_AS, GREATER_THAN, LESS_THAN}.
*/

/* PUBLIC */
Ordertype flatterm_compare_vr(Flatterm a, Flatterm b)
{
  struct { Flatterm a; Flatterm b; Flatterm ai; Flatterm bi; int child; int arity; } stack[TERM_PAIR_STACK_SIZE];
  int top = 0;
  Ordertype rc = SAME_AS;

  stack[0].a = a;
  stack[0].b = b;
  stack[0].ai = NULL;  /* will be set below */
  stack[0].bi = NULL;
  stack[0].child = 0;
  stack[0].arity = 0;  /* will be set below */

  while (top >= 0) {
    Flatterm fa = stack[top].a;
    Flatterm fb = stack[top].b;

    if (!VARIABLE(fa) && !VARIABLE(fb)) {
      if (SYMNUM(fa) == SYMNUM(fb)) {
        int i = stack[top].child;
        Flatterm ai_cur, bi_cur;

        if (i == 0) {
          /* First visit: initialize child iterators */
          stack[top].ai = fa->next;
          stack[top].bi = fb->next;
          stack[top].arity = ARITY(fa);
        }

        if (i < stack[top].arity) {
          ai_cur = stack[top].ai;
          bi_cur = stack[top].bi;
          /* Advance iterators for next visit */
          stack[top].ai = ai_cur->end->next;
          stack[top].bi = bi_cur->end->next;
          stack[top].child = i + 1;
          /* Push child pair */
          if (top + 1 >= TERM_PAIR_STACK_SIZE)
            fatal_error("flatterm_compare_vr: stack overflow");
          top++;
          stack[top].a = ai_cur;
          stack[top].b = bi_cur;
          stack[top].child = 0;
          stack[top].arity = 0;
          continue;
        }
        rc = SAME_AS;
        top--;
      }
      else {
        rc = sym_precedence(SYMNUM(fa), SYMNUM(fb));
        top--;
        goto done;
      }
    }
    else if (VARIABLE(fa) && VARIABLE(fb)) {
      if (VARNUM(fa) == VARNUM(fb))
        rc = SAME_AS;
      else
        rc = (VARNUM(fa) > VARNUM(fb) ? GREATER_THAN : LESS_THAN);
      top--;
      if (top >= 0 && rc != SAME_AS)
        goto done;
    }
    else {
      rc = VARIABLE(fa) ? LESS_THAN : GREATER_THAN;
      top--;
      goto done;
    }
  }

  return rc;

done:
  return rc;
}  /* flatterm_compare_vr */

/*************
 *
 *   int lrpo_multiset(t1, t2) -- Is t1 > t2 in the lrpo multiset ordering?
 *
 *************/

/* DOCUMENTATION
This routine
*/

/* PUBLIC */
BOOL lrpo_multiset(Term t1, Term t2, BOOL lex_order_vars)
{
  return greater_multiset(ARGS(t1), ARITY(t1), ARGS(t2), ARITY(t2),
			  lrpo, lex_order_vars);
}  /* lrpo_multiset */

/*************
 *
 *    lrpo_lex(s, t) -- Is s > t ?
 *
 *    s and t have same symbol and the symbol has lr status.
 *
 *    Iterative version: the for-loops over children that call lrpo
 *    are the iteration targets. The mutual recursion between lrpo
 *    and lrpo_lex remains because lrpo_lex is always a tail call
 *    from lrpo (same-symbol LR case), and the depth of that mutual
 *    recursion is bounded by term depth.
 *
 *************/

static
BOOL lrpo_lex(Term s, Term t, BOOL lex_order_vars)
{
  int i;
  int arity = ARITY(s);

  /* First skip over any identical arguments. */

  for (i = 0; i < arity && term_ident(ARG(s,i),ARG(t,i)); i++);

  if (i == arity)
    return FALSE;  /* s and t identical */
  else if (lrpo(ARG(s,i), ARG(t,i), lex_order_vars)) {
    /* return (s > each remaining arg of t) */
    BOOL ok;
    for (ok = TRUE, i++; ok && i < arity; i++)
      ok = lrpo(s, ARG(t,i), lex_order_vars);
    return ok;
  }
  else {
    /* return (there is a remaining arg of s s.t. arg >= t) */
    BOOL ok;
    for (ok = FALSE, i++; !ok && i < arity; i++)
      ok = (term_ident(ARG(s,i), t) || lrpo(ARG(s,i), t, lex_order_vars));
    return ok;
  }
}  /* lrpo_lex */

/*************
 *
 *    lrpo()
 *
 *************/

/* DOCUMENTATION
This routine checks if Term s > Term t in the
Lexicographic Recursive Path Ordering (LRPO),
also known as Recursive Path Ordering with Status (RPOS).

<P>
Function symbols can have either multiset or left-to-right status
(see symbols.c).
If all symbols are multiset, this reduces to the Recursive
Path Ordering (RPO).
If all symbols are left-to-right, this reduces to Lexicographic
Path Ordering (LPO).
*/

/* PUBLIC */
BOOL lrpo(Term s, Term t, BOOL lex_order_vars)
{
  if (VARIABLE(s)) {
    if (lex_order_vars)
      return VARIABLE(t) && VARNUM(s) > VARNUM(t);
    else
      return FALSE;
  }

  else if (VARIABLE(t)) {
    if (lex_order_vars)
      return TRUE;
    else
      return occurs_in(t, s);  /* s > var iff s properly contains that var */
  }

  else if (SYMNUM(s) == SYMNUM(t) &&
	   sn_to_lrpo_status(SYMNUM(s)) == LRPO_LR_STATUS)
    /* both have the same "left-to-right" symbol. */
    return lrpo_lex(s, t, lex_order_vars);

  else {
    Ordertype p = sym_precedence(SYMNUM(s), SYMNUM(t));

    if (p == SAME_AS)
      return lrpo_multiset(s, t, lex_order_vars);

    else if (p == GREATER_THAN) {
      /* return (s > each arg of t) */
      int i;
      BOOL ok;
      for (ok = TRUE, i = 0; ok && i < ARITY(t); i++)
	ok = lrpo(s, ARG(t,i), lex_order_vars);
      return ok;
    }

    else {  /* LESS_THAN or NOT_COMPARABLE */
      /* return (there is an arg of s s.t. arg >= t) */
      int i;
      BOOL ok;
      for (ok = FALSE, i = 0; !ok && i < ARITY(s); i++)
	ok = term_ident(ARG(s,i), t) || lrpo(ARG(s,i), t, lex_order_vars);
      return ok;
    }
  }
}  /* lrpo */

/*************
 *
 *   init_kbo_weights()
 *
 *************/

/* DOCUMENTATION
Plist should be a list of terms, e.g., a=3, g=0.
Symbols are written as constants; arity is deduced from the symbol table.
*/

/* PUBLIC */
void init_kbo_weights(Plist weights)
{
  Plist p;
  for (p = weights; p; p = p->next) {
    Term t = p->v;
    if (!is_eq_symbol(SYMNUM(t)))
      fatal_error("init_kbo_weights, not equality");
    else {
      Term a = ARG(t,0);
      Term b = ARG(t,1);
      if (!CONSTANT(a))
	fatal_error("init_kbo_weights, symbol not constant");
      else {
	int wt = natural_constant_term(b);
	if (wt == -1)
	  fatal_error("init_kbo_weights, weight not natural");
	else {
	  char *str = sn_to_str(SYMNUM(a));
	  int symnum = function_or_relation_sn(str);
	  if (symnum == -1) {
	    char mess[200];
	    sprintf(mess, "init_kbo_weights, symbol %s not found", str);
	    fatal_error(mess);
	  }
	  set_kb_weight(symnum, wt);
	}
      }
    }
  }
}  /* init_kbo_weights */

/*************
 *
 *   kbo_weight() -- iterative
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int kbo_weight(Term t)
{
  Term stack[TERM_STACK_SIZE];
  int top = 0;
  int wt = 0;

  stack[0] = t;

  while (top >= 0) {
    Term cur = stack[top--];
    if (VARIABLE(cur)) {
      wt += 1;
    }
    else {
      int i;
      wt += sn_to_kb_wt(SYMNUM(cur));
      /* Push children in reverse order so leftmost is processed first
         (order doesn't matter for sum, but matches original traversal). */
      for (i = ARITY(cur) - 1; i >= 0; i--) {
        if (top + 1 >= TERM_STACK_SIZE)
          fatal_error("kbo_weight: stack overflow");
        stack[++top] = ARG(cur, i);
      }
    }
  }

  return wt;
}  /* kbo_weight */

/*************
 *
 *   kbo() -- iterative (tail-call loop)
 *
 *************/

/* DOCUMENTATION
Is alpha kbo-greater-than beta?
*/

/* PUBLIC */
BOOL kbo(Term alpha, Term beta, BOOL lex_order_vars)
{
  /* The two recursive calls in kbo are both tail calls:
     1. Unary same-symbol skip: kbo(ARG(alpha,0), ARG(beta,0), lov)
     2. First differing arg: kbo(ARG(alpha,i), ARG(beta,i), lov)
     Convert to a loop. */

  while (1) {
    if (VARIABLE(alpha)) {
      if (lex_order_vars)
        return VARIABLE(beta) && VARNUM(alpha) > VARNUM(beta);
      else
        return FALSE;
    }
    else if (VARIABLE(beta)) {
      if (lex_order_vars)
        return TRUE;
      else
        return occurs_in(beta, alpha);
    }
    else if (ARITY(alpha) == 1 && ARITY(beta) == 1 &&
             SYMNUM(alpha) == SYMNUM(beta)) {
      /* Tail call: kbo(ARG(alpha,0), ARG(beta,0), lex_order_vars) */
      alpha = ARG(alpha, 0);
      beta = ARG(beta, 0);
      continue;
    }
    else if (!variables_multisubset(beta, alpha))
      return FALSE;
    else {
      int wa = kbo_weight(alpha);
      int wb = kbo_weight(beta);
      if (wa > wb)
        return TRUE;
      else if (wa < wb)
        return FALSE;
      else if (!variables_multisubset(alpha, beta))
        return FALSE;  /* if weights same, multisets of variables must be same */
      else if (sym_precedence(SYMNUM(alpha), SYMNUM(beta)) == GREATER_THAN)
        return TRUE;
      else if (SYMNUM(alpha) != SYMNUM(beta))
        return FALSE;
      else {
        /* Call KBO on first arguments that differ. */
        int i = 0;
        while (i < ARITY(alpha) && term_ident(ARG(alpha,i),ARG(beta,i)))
          i++;
        if (i == ARITY(alpha))
          return FALSE;
        else {
          /* Tail call: kbo(ARG(alpha,i), ARG(beta,i), lex_order_vars) */
          Term a = ARG(alpha, i);
          Term b = ARG(beta, i);
          alpha = a;
          beta = b;
          continue;
        }
      }
    }
  }
}  /* kbo */

/*************
 *
 *   term_greater()
 *
 *************/

/* DOCUMENTATION
Is alpha > beta in the current term ordering?  (LPR, RPO, KBO)
*/

/* PUBLIC */
BOOL term_greater(Term alpha, Term beta, BOOL lex_order_vars)
{
  if (Ordering_method == KBO_METHOD)
    return kbo(alpha, beta, lex_order_vars);
  else
    return lrpo(alpha, beta, lex_order_vars);  /* LPO, RPO, LRPO */
}  /* term_greater */

/*************
 *
 *   term_order()
 *
 *************/

/* DOCUMENTATION
Compare two terms with the current term ordering (LPR, RPO, KBO)
Return GREATER_THAN, LESS_THAN, SAME_AS, or NOT_COMPARABLE.
*/

/* PUBLIC */
Ordertype term_order(Term alpha, Term beta)
{
  if (term_greater(alpha, beta, FALSE))
    return GREATER_THAN;
  else if (term_greater(beta, alpha, FALSE))
    return LESS_THAN;
  else if (term_ident(beta, alpha))
    return SAME_AS;
  else
    return NOT_COMPARABLE;
}  /* term_order */

/*************
 *
 *   flat_kbo_weight() -- iterative
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int flat_kbo_weight(Flatterm f)
{
  /* Walk the flatterm linearly using next pointers. Every node
     contributes: variable -> 1, non-variable -> sn_to_kb_wt. */
  int wt = 0;
  Flatterm fi;

  for (fi = f; fi != f->end->next; fi = fi->next) {
    if (VARIABLE(fi))
      wt += 1;
    else
      wt += sn_to_kb_wt(SYMNUM(fi));
  }

  return wt;
}  /* flat_kbo_weight */

/*************
 *
 *   flat_kbo() -- iterative (tail-call loop)
 *
 *************/

static
BOOL flat_kbo(Flatterm alpha, Flatterm beta, BOOL lex_order_vars)
{
  while (1) {
    if (VARIABLE(alpha)) {
      if (lex_order_vars)
        return VARIABLE(beta) && VARNUM(alpha) > VARNUM(beta);
      else
        return FALSE;
    }
    else if (VARIABLE(beta)) {
      if (lex_order_vars)
        return TRUE;
      else
        return flat_occurs_in(beta, alpha);
    }
    else if (ARITY(alpha) == 1 && ARITY(beta) == 1 &&
             SYMNUM(alpha) == SYMNUM(beta)) {
      /* Tail call: flat_kbo(alpha->next, beta->next, lex_order_vars) */
      alpha = alpha->next;
      beta = beta->next;
      continue;
    }
    else if (!flat_variables_multisubset(beta, alpha))
      return FALSE;
    else {
      int wa = flat_kbo_weight(alpha);
      int wb = flat_kbo_weight(beta);
      if (wa > wb)
        return TRUE;
      else if (wa < wb)
        return FALSE;
      else if (!flat_variables_multisubset(alpha, beta))
        return FALSE;  /* multisets of variables must be the same */
      else if (sym_precedence(SYMNUM(alpha), SYMNUM(beta)) == GREATER_THAN)
        return TRUE;
      else if (SYMNUM(alpha) != SYMNUM(beta))
        return FALSE;
      else {
        Flatterm ai = alpha->next;
        Flatterm bi = beta->next;
        int i = 0;
        while (i < ARITY(alpha) && flatterm_ident(ai,bi)) {
          ai = ai->end->next;
          bi = bi->end->next;
          i++;
        }
        if (i == ARITY(alpha))
          return FALSE;
        else {
          /* Tail call: flat_kbo(ai, bi, lex_order_vars) */
          alpha = ai;
          beta = bi;
          continue;
        }
      }
    }
  }
}  /* flat_kbo */

/*************
 *
 *   flat_lrpo_multiset()
 *
 *************/

static
BOOL flat_lrpo_multiset(Flatterm s, Flatterm t)
{
  printf("ready to abort\n");
  p_syms();
  p_flatterm(s);
  p_flatterm(t);
  printf("lex vals: %d %d\n", sn_to_lex_val(SYMNUM(s)), sn_to_lex_val(SYMNUM(s)));
  fatal_error("flat_lrpo_multiset not implemented");
  return FALSE;
}  /* flat_lrpo_multiset */

/*************
 *
 *   flat_lrpo_lex()
 *
 *************/

static
BOOL flat_lrpo_lex(Flatterm s, Flatterm t, BOOL lex_order_vars)
{
  int arity = ARITY(s);

  /* First skip over any identical arguments. */

  Flatterm si = s->next;
  Flatterm ti = t->next;
  int i = 0;

  while (i < arity && flatterm_ident(si, ti)) {
    si = si->end->next;
    ti = ti->end->next;
    i++;
  }

  if (i == arity)
    return FALSE;  /* s and t identical */
  else if (flat_lrpo(si, ti, lex_order_vars)) {
    /* return (s > each remaining arg of t) */
    BOOL ok = TRUE;
    i++;
    ti = ti->end->next;
    while (ok && i < arity) {
      ok = flat_lrpo(s, ti, lex_order_vars);
      ti = ti->end->next;
      i++;
    }
    return ok;
  }
  else {
    /* return (there is a remaining arg of s s.t. arg >= t) */
    BOOL ok = FALSE;
    si = si->end->next;
    i++;
    while (!ok && i < arity) {
      ok = (flatterm_ident(si, t) || flat_lrpo(si, t, lex_order_vars));
      si = si->end->next;
      i++;
    }
    return ok;
  }
}  /* flat_lrpo_lex */

/*************
 *
 *   flat_lrpo()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL flat_lrpo(Flatterm s, Flatterm t, BOOL lex_order_vars)
{
  if (VARIABLE(s)) {
    if (lex_order_vars)
      return VARIABLE(t) && VARNUM(s) > VARNUM(t);
    else
      return FALSE;
  }

  else if (VARIABLE(t)) {
    if (lex_order_vars)
      return TRUE;
    else
      return flat_occurs_in(t, s);
  }

  else if (SYMNUM(s) == SYMNUM(t) &&
	   sn_to_lrpo_status(SYMNUM(s)) == LRPO_LR_STATUS)
    /* both have the same "left-to-right" symbol. */
    return flat_lrpo_lex(s, t, lex_order_vars);

  else {
    Ordertype p = sym_precedence(SYMNUM(s), SYMNUM(t));

    if (p == SAME_AS)
      return flat_lrpo_multiset(s, t);

    else if (p == GREATER_THAN) {
      /* return (s > each arg of t) */
      int i = 0;
      BOOL ok = TRUE;
      Flatterm ti = t->next;
      while (ok && i < ARITY(t)) {
	ok = flat_lrpo(s, ti, lex_order_vars);
	ti = ti->end->next;
	i++;
      }
      return ok;
    }

    else {  /* LESS_THEN or NOT_COMPARABLE */
      /* return (there is an arg of s s.t. arg >= t) */
      int i = 0;
      BOOL ok = FALSE;
      Flatterm si = s->next;
      while (!ok && i < ARITY(s)) {
	ok = flatterm_ident(si, t) || flat_lrpo(si, t, lex_order_vars);
	si = si->end->next;
	i++;
      }
      return ok;
    }
  }
}  /* flat_lrpo */

/*************
 *
 *   flat_greater()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL flat_greater(Flatterm alpha, Flatterm beta, BOOL lex_order_vars)
{
  if (Ordering_method == RPO_METHOD ||
      Ordering_method == LRPO_METHOD) {
    /* haven't done the flat versions of the multiset operations */
    Term t1 = flatterm_to_term(alpha);
    Term t2 = flatterm_to_term(beta);
    BOOL result = term_greater(t1, t2, lex_order_vars);  /* LPO, RPO, KBO */
    zap_term(t1);
    zap_term(t2);
    return result;
  }
  else if (Ordering_method == LPO_METHOD)
    return flat_lrpo(alpha, beta, lex_order_vars);
  else if (Ordering_method == KBO_METHOD)
    return flat_kbo(alpha, beta, lex_order_vars);
  else {
    fatal_error("flat_greater: unknown Ordering_method");
    return FALSE;
  }
}  /* flat_greater */

/*************
 *
 *   greater_multiset_current_ordering()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL greater_multiset_current_ordering(Term t1, Term t2)
{
  return greater_multiset(ARGS(t1), ARITY(t1), ARGS(t2), ARITY(t2),
			  Ordering_method == KBO_METHOD ? kbo : lrpo,
			  FALSE);
}  /* greater_multiset_current_ordering */
