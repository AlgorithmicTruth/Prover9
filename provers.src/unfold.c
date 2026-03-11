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

#include "unfold.h"
#include "../ladr/memory.h"

/* Private definitions and types */

struct symdata {
  Term alpha, beta;
  Ilist dependents;
  int status;
};

/*************
 *
 *   trace_dependents()
 *
 *************/

enum {NOT_CHECKED = 0, CHECKING, CHECKED, CYCLE};

static
void trace_dependents(int start, struct symdata *table)
{
  /* Iterative DFS using an explicit stack of (symbol, dep-cursor) frames. */
  struct { int sym; Ilist dep; } stack[1000];
  int top = -1;

  if (table[start].status == CHECKED || table[start].status == CYCLE)
    return;
  if (table[start].status == CHECKING) {
    table[start].status = CYCLE;
    return;
  }

  /* Push start node. */
  table[start].status = CHECKING;
  top = 0;
  stack[0].sym = start;
  stack[0].dep = table[start].dependents;

  while (top >= 0) {
    if (stack[top].dep == NULL) {
      /* All dependents processed; finalize this node. */
      int s = stack[top].sym;
      BOOL ok = TRUE;
      Ilist p;
      for (p = table[s].dependents; p; p = p->next) {
        if (table[p->i].status == CYCLE)
          ok = FALSE;
      }
      if (table[s].status != CYCLE)
        table[s].status = (ok ? CHECKED : CYCLE);
      top--;
    }
    else {
      int child = stack[top].dep->i;
      stack[top].dep = stack[top].dep->next;

      if (table[child].status == CHECKED || table[child].status == CYCLE) {
        /* Already resolved -- nothing to push. */
      }
      else if (table[child].status == CHECKING) {
        /* Back edge -- cycle detected. */
        table[child].status = CYCLE;
      }
      else {
        /* NOT_CHECKED -- push child. */
        table[child].status = CHECKING;
        top++;
        stack[top].sym = child;
        stack[top].dep = table[child].dependents;
      }
    }
  }
}  /* trace_dependents */

/*************
 *
 *   eliminate_cycles()
 *
 *************/

static
Ilist eliminate_cycles(Ilist symbols, struct symdata *table)
{
  /* Use pointer-to-pointer to remove CYCLE nodes in-place. */
  Ilist *pp = &symbols;
  while (*pp != NULL) {
    int i = (*pp)->i;
    if (table[i].status == CYCLE) {
      Ilist doomed = *pp;
      *pp = doomed->next;
      free_ilist(doomed);
      zap_ilist(table[i].dependents);
      table[i].dependents = NULL;
    }
    else {
      pp = &(*pp)->next;
    }
  }
  return symbols;
}  /* eliminate_cycles */

/*************
 *
 *   sym_less_or_equal()
 *
 *************/

static
BOOL sym_less_or_equal(int s1, int s2, struct symdata *table)
{
  /* Iterative DFS reachability check: is s1 reachable from s2 via dependents? */
  struct { int sym; Ilist dep; } stack[1000];
  int top;

  if (s1 == s2)
    return TRUE;

  top = 0;
  stack[0].sym = s2;
  stack[0].dep = table[s2].dependents;

  while (top >= 0) {
    if (stack[top].dep == NULL) {
      top--;
    }
    else {
      int child = stack[top].dep->i;
      stack[top].dep = stack[top].dep->next;
      if (child == s1)
        return TRUE;
      top++;
      stack[top].sym = child;
      stack[top].dep = table[child].dependents;
    }
  }
  return FALSE;
}  /* sym_less_or_equal */

/*************
 *
 *   compare_symbols()
 *
 *************/

static
Ordertype compare_symbols(int s1, int s2, struct symdata *table)
{
  if (s1 == s2)
    return SAME_AS;
  else if (sym_less_or_equal(s1, s2, table))
    return LESS_THAN;
  else if (sym_less_or_equal(s2, s1, table))
    return GREATER_THAN;
  else if (sn_to_arity(s1) < sn_to_arity(s2))
    return LESS_THAN;
  else if (sn_to_arity(s2) < sn_to_arity(s1))
    return GREATER_THAN;
  else {
    int i = strcmp(sn_to_str(s1), sn_to_str(s2));
    if (i < 0)
      return LESS_THAN;
    else if (i > 0)
      return GREATER_THAN;
    else
      return SAME_AS;
  }
}  /* compare_symbols */

/*************
 *
 *   insert_symbol()
 *
 *************/

static
Ilist insert_symbol(Ilist syms, int sym, struct symdata *table)
{
  /* Insert sym before the first node where sym is not GREATER_THAN. */
  if (syms == NULL)
    return ilist_append(NULL, sym);
  if (compare_symbols(sym, syms->i, table) != GREATER_THAN)
    return ilist_prepend(syms, sym);
  {
    Ilist prev = syms;
    Ilist curr = syms->next;
    while (curr != NULL && compare_symbols(sym, curr->i, table) == GREATER_THAN) {
      prev = curr;
      curr = curr->next;
    }
    prev->next = ilist_prepend(curr, sym);
    return syms;
  }
}  /* insert_symbol */

/*************
 *
 *   order_symbols()
 *
 *************/

static
Ilist order_symbols(Ilist syms, struct symdata *table)
{
  Ilist new = NULL;
  Ilist p;
  for (p = syms; p; p = p->next)
    new = insert_symbol(new, p->i, table);
  zap_ilist(syms);
  return new;
}  /* order_symbols */

/*************
 *
 *   eq_defs()
 *
 *************/

static
Ilist eq_defs(Clist clauses, int arity_limit)
{
  Ilist symbols = NULL;
  Ilist p;
  int size = greatest_symnum() + 1;
  int i;
  struct symdata *table = safe_calloc(size, sizeof(struct symdata));
  Clist_pos cp;
  for (cp = clauses->first; cp; cp = cp->next) {
    Topform c = cp->c;
    int rc = equational_def(c);  /* 0=no; 1=LR, 2=RL */
    if (rc != 0) {
      Term alpha = ARG(c->literals->atom, (rc == 1 ? 0 : 1));
      Term beta  = ARG(c->literals->atom, (rc == 1 ? 1 : 0));
      if (ARITY(alpha) <= arity_limit && ARITY(beta) > 0) {
	int symbol = SYMNUM(alpha);
	table[symbol].dependents = ilist_cat(table[symbol].dependents,
					     fsym_set_in_term(beta));
	table[symbol].alpha = alpha;
	table[symbol].beta = beta;
	if (!ilist_member(symbols, symbol))
	  symbols = ilist_append(symbols, symbol);
      }
    }
  }

  // trace dependencies (in table)

  for (p = symbols; p; p = p->next)
    trace_dependents(p->i, table);

  // eliminate symbols involved in cycles

  symbols = eliminate_cycles(symbols, table);

  // partial-order -> total-order (by partial-order, arity, strcmp)

  symbols = order_symbols(symbols, table);

  for (i = 0; i < size; i++)
    zap_ilist(table[i].dependents);
  safe_free(table);

  return symbols;
}  /* eq_defs */

/*************
 *
 *   num_constant_symbols()
 *
 *************/

static
int num_constant_symbols(Ilist p)
{
  int count = 0;
  while (p != NULL) {
    if (sn_to_arity(p->i) == 0)
      count++;
    p = p->next;
  }
  return count;
}  /* num_constant_symbols */

/*************
 *
 *   constant_check()
 *
 *************/

static
BOOL constant_check(int symnum, Ilist symbols, Clist clauses, int constant_limit)
{
  if (sn_to_arity(symnum) > 0)
    return TRUE;
  else if (num_constant_symbols(symbols) > constant_limit)
    return FALSE;
  else {
    /* ok if the constant occurs in a negative clause */
    Clist_pos cp;
    for (cp = clauses->first; cp; cp = cp->next) {
      Topform c = cp->c;
      if (negative_clause(c->literals)) {
	Literals lit;
	for (lit = cp->c->literals; lit; lit = lit->next) {
	  if (symbol_in_term(symnum, lit->atom))
	    return TRUE;
	}
      }
    }
    return FALSE;
  }
}  /* constant_check */

/*************
 *
 *   unfold_eq_defs()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void unfold_eq_defs(Clist clauses, int arity_limit, int constant_limit, BOOL print)
{
  Ilist symbols = eq_defs(clauses, arity_limit);
  Ilist p;
  int n = 0;

  // Now we have a list of symbols that can be unfolded.  There can
  // be dependencies, but there are no cycles.  Dependents are earlier.
  // If we were always using LPO or RPO, we could simply give these
  // symbols highest precedence (in the same order).  However,
  // for KBO we want to be able to unfold when there are repeated
  // variables in the right side, e.g., g(x) = f(x,x), which does not
  // satisfy KBO.  Therefore, we do not control unfolding by setting
  // precedences and KBO weights.  Instead, we flag the symbol as "unfold"
  // and the routine that orients equalities checks for that special case.

  if (print)
    printf("Unfolding symbols:");
  for (p = symbols; p; p = p->next) {
    int i = p->i;
    if (constant_check(i, symbols, clauses, constant_limit)) {
      n++;
      // assign_greatest_precedence(i);   /* for LRPO */
      // set_kb_weight(SYMNUM(table[i].alpha), kbo_weight(table[i].beta) + 1);
      set_unfold_symbol(i);
      if (print)
	printf(" %s/%d", sn_to_str(i), sn_to_arity(i));
    }
  }
  if (print)
    printf("%s\n", n > 0 ? "." : " (none).");

  zap_ilist(symbols);
}  /* unfold_eq_defs */

/*************
 *
 *   remove_kb_wt_zero()
 *
 *************/

static
Ilist remove_kb_wt_zero(Ilist syms)
{
  /* Use pointer-to-pointer to remove nodes with kb_wt == 0. */
  Ilist *pp = &syms;
  while (*pp != NULL) {
    if (sn_to_kb_wt((*pp)->i) == 0) {
      Ilist doomed = *pp;
      *pp = doomed->next;
      free_ilist(doomed);
    }
    else {
      pp = &(*pp)->next;
    }
  }
  return syms;
}  /* remove_kb_wt_zero */

/*************
 *
 *   fold_eq_defs()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL fold_eq_defs(Clist clauses, BOOL kbo)
{
  Ilist symbols = eq_defs(clauses, INT_MAX);
  Ilist p;
  BOOL change;

  if (kbo)
    /* required for termination */
    symbols = remove_kb_wt_zero(symbols);

  printf("Folding symbols:");
  for (p = symbols; p; p = p->next)
    printf(" %s/%d", sn_to_str(p->i), sn_to_arity(p->i));
  printf("%s\n", symbols ? "." : " (none).");

  lex_insert_after_initial_constants(symbols);
  change = (symbols != NULL);
  zap_ilist(symbols);
  return change;
}  /* fold_eq_defs */

/*************
 *
 *   one_unary_def()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL one_unary_def(Clist a, Clist b)
{
  Ilist d1 = eq_defs(a, 1);
  Ilist d2 = eq_defs(b, 1);
  BOOL rc = (ilist_count(d1) + ilist_count(d2) == 1);
  zap_ilist(d1);
  zap_ilist(d2);
  return rc;
}  /* one_unary_def */

