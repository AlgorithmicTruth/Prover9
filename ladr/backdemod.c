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

#include "backdemod.h"

/* Private definitions and types */

/*************
 *
 *   index_term_back_demod()
 *
 *************/

static
void index_term_back_demod(Term t, Mindex idx, Indexop op)
{
  if (!VARIABLE(t)) {
    int i;
    mindex_update(idx, t, op);
    for (i = 0; i < ARITY(t); i++)
      index_term_back_demod(ARG(t,i), idx, op);
  }
}  /* index_term_back_demod */

/*************
 *
 *   index_clause_back_demod()
 *
 *************/

/* DOCUMENTATION
This routine indexes or unindexes a clause for back demodulation.
*/

/* PUBLIC */
void index_clause_back_demod(Topform c, Mindex idx, Indexop op)
{
  Literals lit;
  for (lit = c->literals; lit != NULL; lit = lit->next) {
    Term atom = lit->atom;
    int i;
    for (i = 0; i < ARITY(atom); i++) {
      index_term_back_demod(ARG(atom,i), idx, op);
    }
  }
}  /* index_clause_back_demod */

/*************
 *
 *   rewritable_term()
 *
 *************/

static
BOOL rewritable_term(Term alpha, Term t, Context subst)
{
  Trail tr = NULL;
  if (match(alpha, subst, t, &tr)) {
    undo_subst(tr);
    return TRUE;
  }
  else {
    int i;
    BOOL ok = FALSE;
    for (i = 0; i < ARITY(t) && !ok; i++)
      ok = rewritable_term(alpha, ARG(t,i), subst);
    return ok;
  }
}  /* rewritable_term */

/*************
 *
 *   rewritable_clause()
 *
 *************/

/* DOCUMENTATION
This Boolean function checks if Topform c is can be rewritten
by Topform demod, which is assumed to be an oriented (left-to-right)
equation.
*/

/* PUBLIC */
BOOL rewritable_clause(Topform demod, Topform c)
{
  Term alpha = ARG(demod->literals->atom,0);
  Literals lit;
  BOOL ok = FALSE;
  Context subst = get_context();
  for (lit = c->literals; lit != NULL && !ok; lit = lit->next) {
    Term atom = lit->atom;
    int i;
    for (i = 0; i < ARITY(atom) && !ok; i++)
      ok = rewritable_term(alpha, ARG(atom,i), subst);
  }
  free_context(subst);
  return ok;
}  /* rewritable_clause */

/*************
 *
 *   back_demod_linear()
 *
 *************/

/* DOCUMENTATION
This routine returns a Plist: the subset of Clist lst that can be
rewritten with Topform demod (which is assumed to be an oriented
equation).  The Plist which is returned is ordered by decreasing
clause ID.
*/

/* PUBLIC */
Plist back_demod_linear(Topform demod, Clist lst, Plist rewritables)
{
  Clist_pos p;

  for (p = lst->first; p != NULL; p = p->next) {
    Topform c = p->c;
    if (c != demod && rewritable_clause(demod, c)) {
      rewritables = insert_clause_into_plist(rewritables, c, FALSE);
    }
  }
  return(rewritables);
}  /* back_demod_linear */

/*************
 *
 *   lex_rewritable()
 *
 *************/

static
BOOL lex_rewritable(Term subject, Context subst, Term gen,
		    BOOL lex_order_vars)
{
  /* Apply subst to gen, and check if it's less than subject. */
  Term instance = apply(gen, subst);
  BOOL result = term_greater(subject, instance, lex_order_vars);
  zap_term(instance);
  return result;
}  /* lex_rewritable */

/*************
 *
 *   back_demod_indexed()
 *
 *************/

/* DOCUMENTATION
This routine returns a Plist: the set clauses that have terms
that can be rewritten with Topform demod.
<P>
If demod is oriented, demodulation is assumed to be left-to-right.
If demod is not oriented, either way is allowed.
<P>
The Plist which is returned is ordered
by decreasing clause ID.
*/

/* PUBLIC */
Plist back_demod_indexed(Topform demod, int type, Mindex idx,
			 BOOL lex_order_vars)
{
  Term atom = demod->literals->atom;
  Term alpha = ARG(atom,0);
  Term beta  = ARG(atom,1);
  Plist rewritables = NULL;
  Context subst = get_context();

  if (type == ORIENTED) {
    Mindex_pos pos;
    Term t = mindex_retrieve_first(alpha,idx,INSTANCE,subst,NULL,FALSE,&pos);
    while (t != NULL) {
      Topform c = t->container;
      if (c != demod) {          /* in case demod is already in idx */
	rewritables = insert_clause_into_plist(rewritables, c, FALSE);
      }
      t = mindex_retrieve_next(pos);
    }
  }
  else {
    if (type == LEX_DEP_LR || type == LEX_DEP_BOTH) {
      Mindex_pos pos;
      Term t;
      /* Find clauses that can be rewritten left-to-right. */
      t = mindex_retrieve_first(alpha,idx,INSTANCE,subst,NULL,FALSE,&pos);
      while (t != NULL) {
	Topform c = t->container;
	if (c != demod && lex_rewritable(t, subst, beta, lex_order_vars)) {
	  rewritables = insert_clause_into_plist(rewritables, c, FALSE);
	}
	t = mindex_retrieve_next(pos);
      }
    }

    if (type == LEX_DEP_RL || type == LEX_DEP_BOTH) {
      Mindex_pos pos;
      Term t;
      /* Find clauses that can be rewritten right-to-left. */
      t = mindex_retrieve_first(beta,idx,INSTANCE,subst,NULL,FALSE,&pos);
      while (t != NULL) {
	Topform c = t->container;
	if (c != demod && lex_rewritable(t, subst, alpha, lex_order_vars)) {
	  rewritables = insert_clause_into_plist(rewritables, c, FALSE);
	}
	t = mindex_retrieve_next(pos);
      }
    }
  }
  free_context(subst);
  return rewritables;
}  /* back_demod_indexed */


/*************
 *
 *   atom_has_bt_instance()
 *
 *************/

static
BOOL atom_has_bt_instance(Term t, Term alpha)
{
  /* Is any subterm of t (including t itself) an AC instance of
     alpha?  Backtrack (btm) matching with partial match allowed, so
     an AC-rooted alpha matches a sub-multiset at an AC root (x+x
     is found in a+a+b).  Terms are assumed ac_canonical (the btm
     input contract).  Iterative walk with a growable stack. */
  int cap = 256, top = 0;
  Term *stack = safe_malloc(cap * sizeof(Term));
  BOOL found = FALSE;
  Context c = get_context();

  stack[top++] = t;
  while (top > 0 && !found) {
    Term cur = stack[--top];
    if (!VARIABLE(cur)) {
      Btm_state bt = match_bt_first(alpha, c, cur, 1);
      if (bt != NULL) {
        match_bt_cancel(bt);
        found = TRUE;
      }
      else {
        int i;
        if (top + ARITY(cur) > cap) {
          while (top + ARITY(cur) > cap)
            cap *= 2;
          stack = safe_realloc(stack, cap * sizeof(Term));
        }
        for (i = 0; i < ARITY(cur); i++)
          stack[top++] = ARG(cur, i);
      }
    }
  }
  free_context(c);
  safe_free(stack);
  return found;
}  /* atom_has_bt_instance */

/*************
 *
 *   back_demodulatable_ac()
 *
 *************/

/* DOCUMENTATION
AC analog of back_demod_indexed: linear scan of two clause lists
(usable and sos), testing each clause for an AC (btm) instance of
the demodulator's left side.  This is EQP's get_bd_clauses /
has_an_instance.  AC-mode demodulators are ORIENTED only, so only
alpha is tried.  AC extension clauses are skipped (they must not be
back demodulated).  The returned Plist is ordered by decreasing
clause ID, like back_demod_indexed.
*/

/* PUBLIC */
Plist back_demodulatable_ac(Topform demod, Clist lst1, Clist lst2)
{
  Term alpha = ARG(demod->literals->atom, 0);
  Plist rewritables = NULL;
  Clist lists[2];
  int i;

  lists[0] = lst1;
  lists[1] = lst2;

  for (i = 0; i < 2; i++) {
    Clist_pos p;
    if (lists[i] == NULL)
      continue;
    for (p = lists[i]->first; p != NULL; p = p->next) {
      Topform c = p->c;
      if (c != demod && !c->ac_extension) {
        Literals lit;
        BOOL hit = FALSE;
        for (lit = c->literals; lit != NULL && !hit; lit = lit->next)
          hit = atom_has_bt_instance(lit->atom, alpha);
        if (hit)
          rewritables = insert_clause_into_plist(rewritables, c, FALSE);
      }
    }
  }
  return rewritables;
}  /* back_demodulatable_ac */

/*************
 *
 *   back_demodulatable_ac_indexed()
 *
 *************/

/* DOCUMENTATION
Indexed AC analog of back_demod_indexed: retrieve, from a back-demod
Mindex built with FPA + BACKTRACK_UNIF, the clauses containing an AC
(btm) instance of the demodulator's left side.  FPA candidate paths
stop at AC symbols, so the candidate set is a superset of the AC
instances; the mindex retrieval confirms each candidate with
backtrack matching, partial match allowed, so an AC-rooted alpha
matches a sub-multiset at an AC root (x+x is found in a+a+b).  This
is EQP's INDEX_BD / get_bd_clauses.  AC-mode demodulators are
ORIENTED only, so only alpha is tried.  AC extension clauses are
skipped (they must not be back demodulated).  The returned Plist is
ordered by decreasing clause ID, like back_demod_indexed.
*/

/* PUBLIC */
Plist back_demodulatable_ac_indexed(Topform demod, Mindex idx)
{
  Term alpha = ARG(demod->literals->atom, 0);
  Plist rewritables = NULL;
  Context subst = get_context();
  Mindex_pos pos;
  Term t;

  t = mindex_retrieve_first(alpha, idx, INSTANCE, subst, NULL, TRUE, &pos);
  while (t != NULL) {
    Topform c = t->container;
    if (c != demod && !c->ac_extension)
      rewritables = insert_clause_into_plist(rewritables, c, FALSE);
    t = mindex_retrieve_next(pos);
  }
  free_context(subst);
  return rewritables;
}  /* back_demodulatable_ac_indexed */
