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

#include "cnf.h"

#include <setjmp.h>  /* Yikes! */
#include <signal.h>

/* The following has an optimization in which formulas are
   shared.  The main benefit of this is that when checking for
   identical formulas, we can compare pointers instead of
   traversing the formulas.  Another benefit is that when copying
   formulas (i.e., applying distributivity), we can copy pointers
   instead of whole formulas.

   The routine consolidate_formula() causes some subformulas to
   be shared.  It is currently applied to quantifier-free nnf formulas.

   shared:     ATOM, NOT
   not shared: AND, OR, ALL, EXISTS
*/   

/* Private definitions and types */

static jmp_buf Jump_env;        /* for setjmp/longjmp */

static unsigned Fid_call_limit = UINT_MAX;
static unsigned Fid_calls = 0;

static int Cnf_clause_limit = 0;   /* max clauses in distribute; 0 = no limit */
static BOOL Cnf_limit_hit = FALSE; /* set TRUE when limit exceeded */

static time_t Cnf_timeout_deadline = 0;  /* 0 = no timeout */
static BOOL   Cnf_timeout_hit = FALSE;
static int    Cnf_timeout_counter  = 0;
static int    Cnf_timeout_interval = 1000;

static int Cnf_def_threshold = 0;  /* definitional CNF threshold; 0 = disabled */
static int Cnf_def_count = 0;      /* counter for fresh definition predicates */

static void cnf_check_timeout(void);  /* forward declaration */

/*************
 *
 *   share_formula()
 *
 *************/

static
Formula share_formula(Formula f, Hashtab h)
{
  /* Iterative: post-order frame stack. Process children first, then
   * hash-lookup on ATOM/NOT nodes for sharing.
   */
  typedef struct { Formula node; int child; } Sfframe;
  int cap = 1000;
  Sfframe *stack = safe_malloc(cap * sizeof(Sfframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->type == AND_FORM || cur->type == OR_FORM ||
      cur->type == ALL_FORM || cur->type == EXISTS_FORM) {
    if (cur->arity == 0) {
      result = cur;
    }
    else {
      stack[top].node = cur;
      stack[top].child = 1;
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Sfframe)); }
      cur = cur->kids[0];
      goto restart;
    }
  }
  else if (cur->type == NOT_FORM) {
    /* NOT has one child that needs sharing first. */
    stack[top].node = cur;
    stack[top].child = 1;
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Sfframe)); }
    cur = cur->kids[0];
    goto restart;
  }
  else {
    /* ATOM_FORM: hash lookup directly. */
    unsigned hashval = hash_formula(cur);
    Formula g = hash_lookup(cur, hashval, h,
                            (BOOL (*)(void *, void *)) formula_ident);
    if (g) {
      zap_formula(cur);
      g->excess_refs++;
      result = g;
    }
    else {
      hash_insert(cur, hashval, h);
      result = cur;
    }
  }

  /* Pop and assign results. */
  while (top > 0) {
    Sfframe *fr;
    int prev_child;
    top--;
    fr = &stack[top];
    prev_child = fr->child - 1;
    fr->node->kids[prev_child] = result;

    if (fr->child < fr->node->arity) {
      int next = fr->child;
      fr->child = next + 1;
      top++;
      cur = fr->node->kids[next];
      goto restart;
    }
    /* All children processed. For NOT: hash lookup for sharing. */
    if (fr->node->type == NOT_FORM || fr->node->type == ATOM_FORM) {
      unsigned hashval = hash_formula(fr->node);
      Formula g = hash_lookup(fr->node, hashval, h,
                              (BOOL (*)(void *, void *)) formula_ident);
      if (g) {
        zap_formula(fr->node);
        g->excess_refs++;
        result = g;
      }
      else {
        hash_insert(fr->node, hashval, h);
        result = fr->node;
      }
    }
    else {
      result = fr->node;
    }
  }

  safe_free(stack);
  return result;
}  /* share_formula */

/*************
 *
 *   consolidate_formula()
 *
 *************/

static
Formula consolidate_formula(Formula f)
{
  Hashtab h = hash_init(10000);
  f = share_formula(f, h);
  /* hash_info(h); */
  hash_destroy(h);
  return f;
}  /* consolidate_formula */

/*************
 *
 *   formula_ident_share()
 *
 *************/

/* DOCUMENTATION
This Boolean function checks if two formulas are identical.
The routine term_ident() checks identity of atoms.
<P>
The test is for strict identity---it does not consider
renamability of bound variables, permutability of AND or OR,
or symmetry of IFF or equality.
*/

/* PUBLIC */
BOOL formula_ident_share(Formula f, Formula g)
{
  /* Iterative: pair-stack with Fid_calls counter + longjmp on limit. */
  typedef struct { Formula a; Formula b; } Fis_entry;
  int stack_cap = 1000;
  Fis_entry *stack = safe_malloc(stack_cap * sizeof(*stack));
  int top = 0;

  stack[0].a = f;
  stack[0].b = g;

  while (top >= 0) {
    Formula a = stack[top].a;
    Formula b = stack[top].b;
    top--;

    if (Fid_call_limit != 0 && ++Fid_calls > Fid_call_limit) {
      safe_free(stack);
      printf("\n%% Fid_call limit; jumping home.\n");
      longjmp(Jump_env, 1);
    }

    if (a->type != b->type || a->arity != b->arity) {
      safe_free(stack);
      return FALSE;
    }
    else if (a->type == AND_FORM || a->type == OR_FORM) {
      int i;
      for (i = 0; i < a->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top].a = a->kids[i];
        stack[top].b = b->kids[i];
      }
    }
    else if (a->type == ALL_FORM || a->type == EXISTS_FORM) {
      if (!str_ident(a->qvar, b->qvar)) {
        safe_free(stack);
        return FALSE;
      }
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].a = a->kids[0];
      stack[top].b = b->kids[0];
    }
    else {
      /* Shared ATOM/NOT: pointer compare. */
      if (a != b) {
        safe_free(stack);
        return FALSE;
      }
    }
  }
  safe_free(stack);
  return TRUE;
}  /* formula_ident_share */

/*************
 *
 *   formula_copy_share()
 *
 *************/

/* DOCUMENTATION
This function returns a copy of the given formula.
All subformulas, including the atoms, are copied.
*/

/* PUBLIC */
Formula formula_copy_share(Formula f)
{
  /* Iterative: frame stack like formula_copy. Shared ATOM/NOT nodes
   * get excess_refs incremented instead of being copied.
   */
  typedef struct { Formula orig; Formula copy; int child; } Fcsframe;
  int cap = 1000;
  Fcsframe *stack = safe_malloc(cap * sizeof(Fcsframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->type == AND_FORM || cur->type == OR_FORM) {
    Formula g = formula_get(cur->arity, cur->type);
    if (cur->arity == 0) {
      result = g;
    }
    else {
      stack[top].orig = cur;
      stack[top].copy = g;
      stack[top].child = 1;
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Fcsframe)); }
      cur = cur->kids[0];
      goto restart;
    }
  }
  else if (cur->type == ALL_FORM || cur->type == EXISTS_FORM) {
    Formula g = formula_get(1, cur->type);
    g->qvar = cur->qvar;
    stack[top].orig = cur;
    stack[top].copy = g;
    stack[top].child = 1;
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Fcsframe)); }
    cur = cur->kids[0];
    goto restart;
  }
  else {
    /* Shared ATOM/NOT: increment excess_refs, return same pointer. */
    cur->excess_refs++;
    result = cur;
  }

  /* Pop and assign results. */
  while (top > 0) {
    Fcsframe *fr;
    int prev_child;
    top--;
    fr = &stack[top];
    prev_child = fr->child - 1;
    fr->copy->kids[prev_child] = result;

    if (fr->child < fr->orig->arity) {
      int next = fr->child;
      fr->child = next + 1;
      top++;
      cur = fr->orig->kids[next];
      goto restart;
    }
    result = fr->copy;
  }

  safe_free(stack);
  return result;
}  /* formula_copy_share */

/*************
 *
 *   complementary_share()
 *
 *************/

static
BOOL complementary_share(Formula a, Formula b)
{
  return
    (a->type == NOT_FORM && formula_ident_share(a->kids[0], b))
    ||
    (b->type == NOT_FORM && formula_ident_share(a, b->kids[0]));
}  /* complementary_share */

/*************
 *
 *   contains_complements_share()
 *
 *   Assume AND_FORM or OR_FORM.
 *
 *************/

static
BOOL contains_complements_share(Formula f)
{
  int i, j;
  for (i = 0; i < f->arity-1; i++) {
    for (j = i+1; j < f->arity; j++) {
      if (complementary_share(f->kids[i], f->kids[j]))
	return TRUE;
    }
  }
  return FALSE;
}  /* contains_complements_share */

/*************
 *
 *   prop_member_share() -- is f an argument of g?
 *
 *************/

static
BOOL prop_member_share(Formula f, Formula g)
{
  int i;
  for (i = 0; i < g->arity; i++)
    if (formula_ident_share(f, g->kids[i]))
      return TRUE;
  return FALSE;
}  /* prop_member_share */

/*************
 *
 *   prop_subset_share() -- are the arguments of f a subset of the arguments of g?
 *
 *************/

static
BOOL prop_subset_share(Formula f, Formula g)
{
  int i;
  for (i = 0; i < f->arity; i++)
    if (!prop_member_share(f->kids[i], g))
      return FALSE;
  return TRUE;
}  /* prop_subset_share */

/*************
 *
 *   prop_subsume_share()
 *
 *   Assume disjunctions, atomic, TRUE, or FALSE
 *
 *************/

static
BOOL prop_subsume_share(Formula f, Formula g)
{
  if (FALSE_FORMULA(f))
    return TRUE;
  else if  (TRUE_FORMULA(g))
    return TRUE;
  else if (g->type == OR_FORM) {
    if (f->type == OR_FORM)
      return prop_subset_share(f, g);
    else
      return prop_member_share(f, g);
  }
  return formula_ident_share(f, g);
}  /* prop_subsume_share */

/*************
 *
 *   remove_subsumed_share()
 *
 *   Assume flat conjunction.  Always return conjunction.
 *
 *************/

static
Formula remove_subsumed_share(Formula f)
{
  if (f->type != AND_FORM)
    return f;
  else {
    Formula h;
    int new_arity = f->arity;
    int i, j;
    for (i = 0; i < f->arity; i++) {
      for (j = i+1; j < f->arity; j++) {
	cnf_check_timeout();
	if (f->kids[i] && f->kids[j] &&
	    prop_subsume_share(f->kids[i], f->kids[j])) {
	  zap_formula(f->kids[j]);
	  f->kids[j] = NULL;
	  new_arity--;
	}
	else if (f->kids[i] && f->kids[j] &&
		 prop_subsume_share(f->kids[j], f->kids[i])) {
	  zap_formula(f->kids[i]);
	  f->kids[i] = NULL;
	  new_arity--;
	}
      }
    }
    h = formula_get(new_arity, AND_FORM);
    j = 0;
    for (i = 0; i < f->arity; i++) {
      if (f->kids[i])
	h->kids[j++] = f->kids[i];
    }
    free_formula(f);
    return h;
  }
}  /* remove_subsumed_share */

/*************
 *
 *   bbt()
 *
 *************/

static
Formula bbt(Formula f, int start, int end)
{
  if (start == end)
    return f->kids[start];
  else {
    int mid = (start + end) / 2;
    Formula b = formula_get(2, f->type);
    b->kids[0] = bbt(f, start, mid);
    b->kids[1] = bbt(f, mid+1, end); 
    return b;
  }
}  /* bbt */

/*************
 *
 *   balanced_binary()
 *
 *   Take a flat OR or AND, and make it into a balanced binary tree.
 *
 *************/

static
Formula balanced_binary(Formula f)
{
  if (f->type != AND_FORM && f->type != OR_FORM)
    return f;
  else if (f->arity == 0)
    return f;
  else {
    Formula b = bbt(f, 0, f->arity-1);
    free_formula(f);
    return b;
  }
}  /* balanced_binary */

/*************
 *
 *   disjoin_flatten_simplify(a, b)   a OR b
 *
 *   Remove duplicates; if it contains complements, return TRUE.
 *
 *************/

static
Formula disjoin_flatten_simplify(Formula a, Formula b)
{
  Formula c;
  int new_arity, i, j;
  a = make_disjunction(a);
  b = make_disjunction(b);
  new_arity = a->arity + b->arity;
  for (i = 0; i < a->arity; i++) {
    for (j = 0; j < b->arity; j++) {
      if (b->kids[j] != NULL) {
	if (complementary_share(a->kids[i], b->kids[j])) {
	  zap_formula(a);
	  zap_formula(b);  /* this can handle NULL kids */
	  return formula_get(0, AND_FORM);  /* TRUE formula */
	}
	else if (formula_ident_share(a->kids[i], b->kids[j])) {
	  /* Note that this makes b non-well-formed. */
	  zap_formula(b->kids[j]);  /* really FALSE */
	  b->kids[j] = NULL;
	  new_arity--;
	}
      }
    }
  }
  c = formula_get(new_arity, OR_FORM);
  j = 0;
  for (i = 0; i < a->arity; i++)
    c->kids[j++] = a->kids[i];
  for (i = 0; i < b->arity; i++)
    if (b->kids[i] != NULL)
      c->kids[j++] = b->kids[i];
  free_formula(a);
  free_formula(b);
  return c;
}  /* disjoin_flatten_simplify */

/*************
 *
 *   simplify_and_share()
 *
 *   Assume flattened conjunction, and all kids are simplified flat
 *   disjunctions (or atomic, TRUE, FALSE).
 *   
 *
 *************/

static
Formula simplify_and_share(Formula f)
{
  if (f->type != AND_FORM)
    return f;
  else {
    f = remove_subsumed_share(f);  /* still AND */
    if (f->arity == 1) {
      Formula g = f->kids[0];
      free_formula(f);
      return g;
    }
    else if (contains_complements_share(f)) {
      zap_formula(f);
      return formula_get(0, OR_FORM);  /* FALSE */
    }
    else
      return f;
  }
}  /* simplify_and_share */

/*************
 *
 *   cnf_check_timeout() -- adaptive throttle for CNF preprocessing timeout.
 *
 *************/

static
void cnf_check_timeout(void)
{
  if (Cnf_timeout_deadline == 0)
    return;
  Cnf_timeout_counter++;
  if (Cnf_timeout_counter < Cnf_timeout_interval)
    return;
  Cnf_timeout_counter = 0;
  if (time(NULL) >= Cnf_timeout_deadline) {
    fprintf(stderr, "\n%% CNF preprocessing timeout exceeded\n");
    Cnf_timeout_hit = TRUE;
    longjmp(Jump_env, 1);
  }
}  /* cnf_check_timeout */

/*************
 *
 *   distribute_top()
 *
 *   Assume it's a binary disjunction.
 *
 *************/

static
Formula distribute_top(Formula h)
{
  Formula f = h->kids[0];
  Formula g = h->kids[1];
  int arity, i, j, k;
  Formula a;

  cnf_check_timeout();

  free_formula(h);
  /* If not conjunctions, make them so. */
  f = make_conjunction(f);
  g = make_conjunction(g);

  /* printf("DT: %5d x %5d\n", f->arity, g->arity); fflush(stdout); */

  arity = f->arity * g->arity;

  if (Cnf_clause_limit > 0 && arity > Cnf_clause_limit) {
    /* Product exceeds clause limit — bail out via longjmp.
       Partially-transformed formula memory is abandoned (palloc). */
    fprintf(stderr, "\n%% CNF clause limit exceeded: %d x %d = %d > %d\n",
	    f->arity, g->arity, arity, Cnf_clause_limit);
    Cnf_limit_hit = TRUE;
    longjmp(Jump_env, 1);
  }

  a = formula_get(arity, AND_FORM);
  k = 0;
  for (i = 0; i < f->arity; i++) {
    for (j = 0; j < g->arity; j++) {
      Formula fi, gj;
      cnf_check_timeout();
      fi = formula_copy_share(f->kids[i]);
      gj = formula_copy_share(g->kids[j]);
      a->kids[k++] = disjoin_flatten_simplify(fi, gj);
    }
  }
  zap_formula(f);
  zap_formula(g);
  a = simplify_and_share(a);
  return a;
}  /* distribute_top */

/*************
 *
 *   distribute()
 *
 *************/

static
Formula distribute(Formula f)
{
  /* Iterative: post-order on binary OR tree. Process kids[0], kids[1],
   * then distribute_top. Non-OR nodes are leaves.
   */
  typedef struct { Formula node; int child; } Dframe;
  int cap = 1000;
  Dframe *stack = safe_malloc(cap * sizeof(Dframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->type != OR_FORM || cur->arity == 0) {
    result = cur;
  }
  else {
    if (cur->arity != 2)
      cur = balanced_binary(cur);
    stack[top].node = cur;
    stack[top].child = 1;
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Dframe)); }
    cur = cur->kids[0];
    goto restart;
  }

  /* Pop and assign results. */
  while (top > 0) {
    Dframe *fr;
    int prev_child;
    cnf_check_timeout();
    top--;
    fr = &stack[top];
    prev_child = fr->child - 1;
    fr->node->kids[prev_child] = result;

    if (fr->child < 2) {
      fr->child = 2;
      top++;
      cur = fr->node->kids[1];
      goto restart;
    }
    result = distribute_top(fr->node);
  }

  safe_free(stack);
  return result;
}  /* distribute */

/*************
 *
 *   cnf()
 *
 *   Assume NNF and flattened.
 *
 *   This does not go below quantifiers; that is,
 *   quantified formulas are treated as atomic.
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula cnf(Formula f)
{
  /* Iterative: post-order on AND/OR tree. Process children, then:
   * AND: flatten_top + simplify_and_share.
   * OR: dual+remove_subsumed+dual, balanced_binary, distribute.
   */
  typedef struct { Formula node; int child; } Cframe;
  int cap = 1000;
  Cframe *stack = safe_malloc(cap * sizeof(Cframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->type != AND_FORM && cur->type != OR_FORM) {
    result = cur;
  }
  else if (cur->arity == 0) {
    result = cur;
  }
  else {
    stack[top].node = cur;
    stack[top].child = 1;
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Cframe)); }
    cur = cur->kids[0];
    goto restart;
  }

  /* Pop and assign results. */
  while (top > 0) {
    Cframe *fr;
    int prev_child;
    cnf_check_timeout();
    top--;
    fr = &stack[top];
    prev_child = fr->child - 1;
    fr->node->kids[prev_child] = result;

    if (fr->child < fr->node->arity) {
      int next = fr->child;
      fr->child = next + 1;
      top++;
      cur = fr->node->kids[next];
      goto restart;
    }
    /* All children done. Apply CNF transformation. */
    if (fr->node->type == AND_FORM) {
      result = flatten_top(fr->node);
      result = simplify_and_share(result);
    }
    else {
      Formula node = fr->node;
      node = dual(remove_subsumed_share(dual(node)));
      node = balanced_binary(node);
      node = distribute(node);
      result = node;
    }
  }

  safe_free(stack);
  return result;
}  /* cnf */

/*************
 *
 *   dnf()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula dnf(Formula f)
{
  return dual(cnf(dual(f)));
}  /* dnf */

/*************
 *
 *   skolem()
 *
 *************/

static
Formula skolem(Formula f, Ilist uvars)
{
  /* Iterative with tail-call optimization.
   *
   * Frame types:
   *   RESUME (phase=0): returning from child, assign kids[prev_child] = result
   *   CLEANUP (phase=1): ALL_FORM scope exit -- free prepended Ilist + var Term
   *
   * EXISTS is a tail call: Skolemize, free EXISTS node, cur = child, goto restart.
   * ALL pushes cleanup + resume frames, enters child.
   * AND/OR pushes resume frame, processes children sequentially.
   */
  typedef struct {
    Formula node;    /* the formula node (for RESUME) */
    int child;       /* next child index (for RESUME) */
    int phase;       /* 0=resume, 1=cleanup */
    Ilist uv_node;   /* Ilist node to free (for CLEANUP) */
    Term var_term;   /* Term to free (for CLEANUP) */
  } Skframe;
  int cap = 1000;
  Skframe *stack = safe_malloc(cap * sizeof(Skframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;
  Ilist cur_uvars;

  cur = f;
  cur_uvars = uvars;

restart:
  if (cur->type == ATOM_FORM || cur->type == NOT_FORM) {
    result = cur;
  }
  else if (cur->type == ALL_FORM) {
    Term var = get_rigid_term(cur->qvar, 0);
    Ilist uvars_plus;
    if (ilist_member(cur_uvars, SYMNUM(var))) {
      int sn = gen_new_symbol("x", 0, cur_uvars);
      Term newvar = get_rigid_term(sn_to_str(sn), 0);
      subst_free_var(cur->kids[0], var, newvar);
      cur->qvar = sn_to_str(sn);
      free_term(var);
      var = newvar;
    }
    uvars_plus = ilist_prepend(cur_uvars, SYMNUM(var));

    /* Push cleanup frame (processed on pop). */
    if (top + 2 >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Skframe)); }
    stack[top].phase = 1;  /* CLEANUP */
    stack[top].uv_node = uvars_plus;
    stack[top].var_term = var;
    stack[top].node = NULL;
    stack[top].child = 0;
    top++;

    /* Push resume frame for the ALL node. */
    stack[top].phase = 0;  /* RESUME */
    stack[top].node = cur;
    stack[top].child = 1;
    stack[top].uv_node = NULL;
    stack[top].var_term = NULL;
    top++;

    cur_uvars = uvars_plus;
    cur = cur->kids[0];
    goto restart;
  }
  else if (cur->type == EXISTS_FORM) {
    /* Tail call: Skolemize and remove EXISTS node. */
    int n = ilist_count(cur_uvars);
    int sn = next_skolem_symbol(n);
    Term sk = get_rigid_term(sn_to_str(sn), n);
    Term evar = get_rigid_term(cur->qvar, 0);
    Ilist p;
    int i;
    Formula child;

    for (p = cur_uvars, i = n-1; p; p = p->next, i--)
      ARG(sk,i) = get_rigid_term(sn_to_str(p->i), 0);

    subst_free_var(cur->kids[0], evar, sk);
    zap_term(sk);
    zap_term(evar);

    child = cur->kids[0];
    free_formula(cur);
    cur = child;
    goto restart;
  }
  else if (cur->type == AND_FORM || cur->type == OR_FORM) {
    if (cur->arity == 0) {
      result = cur;
    }
    else {
      stack[top].phase = 0;
      stack[top].node = cur;
      stack[top].child = 1;
      stack[top].uv_node = NULL;
      stack[top].var_term = NULL;
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Skframe)); }
      cur = cur->kids[0];
      goto restart;
    }
  }
  else {
    /* Not in NNF! Let the caller beware! */
    result = cur;
  }

  /* Pop and process frames. */
  while (top > 0) {
    Skframe *fr;
    top--;
    fr = &stack[top];

    if (fr->phase == 1) {
      /* CLEANUP: restore uvars scope. */
      cur_uvars = fr->uv_node->next;  /* pop to parent uvars */
      free_term(fr->var_term);
      free_ilist(fr->uv_node);  /* frees first node only */
    }
    else {
      /* RESUME: assign child result. */
      int prev_child = fr->child - 1;
      fr->node->kids[prev_child] = result;

      if (fr->child < fr->node->arity) {
        int next = fr->child;
        fr->child = next + 1;
        top++;
        cur = fr->node->kids[next];
        goto restart;
      }
      result = fr->node;
    }
  }

  safe_free(stack);
  return result;
}  /* skolem */

/*************
 *
 *   skolemize()
 *
 *************/

/* DOCUMENTATION
This routine Skolemizes an NNF formula.
The quantified variables need not be named in any particular way.
If there are universally quantified variables with the same name,
one in the scope of another, the inner variable will be renamed.
(Existential nodes are removed.)
*/

/* PUBLIC */
Formula skolemize(Formula f)
{
  f = skolem(f, NULL);
  return f;
}  /* skolemize */

/*************
 *
 *   unique_qvars()
 *
 *************/

static
Ilist unique_qvars(Formula f, Ilist vars)
{
  /* Iterative: flat stack with threaded Ilist vars (grows monotonically). */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur->type == ATOM_FORM) {
      /* Leaf, nothing to do. */
    }
    else if (quant_form(cur)) {
      Term var = get_rigid_term(cur->qvar, 0);
      if (ilist_member(vars, SYMNUM(var))) {
        int sn = gen_new_symbol("x", 0, vars);
        Term newvar = get_rigid_term(sn_to_str(sn), 0);
        subst_free_var(cur->kids[0], var, newvar);
        cur->qvar = sn_to_str(sn);
        free_term(var);
        var = newvar;
      }
      vars = ilist_prepend(vars, SYMNUM(var));
      /* Push single child. */
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top] = cur->kids[0];
    }
    else {
      int i;
      for (i = 0; i < cur->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = cur->kids[i];
      }
    }
  }
  safe_free(stack);
  return vars;
}  /* unique_qvars */

/*************
 *
 *   unique_quantified_vars()
 *
 *************/

/* DOCUMENTATION
Rename quantified variables, if necessary, so that each is unique.
This works for any formula.
<P>
If you wish to rename a quantified variable only if it occurs in
the scope of of a quantified variable with the same name, you
can use the routine eliminate_rebinding() instead.
<P>
(This could be a void routine, because none of the formula nodes
is changed.)
*/

/* PUBLIC */
Formula unique_quantified_vars(Formula f)
{
  Ilist uvars = unique_qvars(f, NULL);
  zap_ilist(uvars);
  return f;
}  /* unique_quantified_vars */

/*************
 *
 *   mark_free_vars_formula()
 *
 *************/

/* Replace all free occurrences of CONSTANT *varname with
 * a VARIABLE of index varnum.
 */

static
void mark_free_vars_formula(Formula f, char *varname, int varnum)
{
  /* Iterative: flat stack. Modify ATOMs in-place, skip binding quantifiers. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int sn_val = str_to_sn(varname, 0);
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur->type == ATOM_FORM) {
      cur->atom = subst_var_term(cur->atom, sn_val, varnum);
    }
    else if (quant_form(cur) && str_ident(cur->qvar, varname)) {
      /* Bound here; do not descend. */
    }
    else {
      int i;
      for (i = 0; i < cur->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = cur->kids[i];
      }
    }
  }
  safe_free(stack);
}  /* mark_free_vars_formula */

/*************
 *
 *   remove_uni_quant()
 *
 *************/

static
Formula remove_uni_quant(Formula f, int *varnum_ptr)
{
  /* Iterative: ALL_FORM is a tail call (mark, free, continue with child).
   * AND/OR push resume frame for children.
   */
  typedef struct { Formula node; int child; } Rframe;
  int cap = 1000;
  Rframe *stack = safe_malloc(cap * sizeof(Rframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->type == ALL_FORM) {
    /* Tail call: mark vars, free ALL node, continue with child. */
    Formula child = cur->kids[0];
    mark_free_vars_formula(child, cur->qvar, *varnum_ptr);
    *varnum_ptr += 1;
    free_formula(cur);
    cur = child;
    goto restart;
  }
  else if (cur->type == AND_FORM || cur->type == OR_FORM) {
    if (cur->arity == 0) {
      result = cur;
    }
    else {
      stack[top].node = cur;
      stack[top].child = 1;
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Rframe)); }
      cur = cur->kids[0];
      goto restart;
    }
  }
  else {
    result = cur;
  }

  /* Pop and assign results. */
  while (top > 0) {
    Rframe *fr;
    int prev_child;
    top--;
    fr = &stack[top];
    prev_child = fr->child - 1;
    fr->node->kids[prev_child] = result;

    if (fr->child < fr->node->arity) {
      int next = fr->child;
      fr->child = next + 1;
      top++;
      cur = fr->node->kids[next];
      goto restart;
    }
    result = fr->node;
  }

  safe_free(stack);
  return result;
}  /* remove_uni_quant */

/*************
 *
 *   remove_universal_quantifiers()
 *
 *************/

/* DOCUMENTATION
For each universally quantified variable in the given formula,
*/

/* PUBLIC */
Formula remove_universal_quantifiers(Formula f)
{
  int varnum = 0;
  return remove_uni_quant(f, &varnum);
}  /* remove_universal_quantifiers */

/*************
 *
 *   collect_vars_in_formula()
 *
 *   Walk the formula and mark which variable numbers appear.
 *   seen[] must be at least MAX_VARS in size.
 *
 *************/

static
void collect_vars_in_formula(Formula f, BOOL *seen)
{
  /* Iterative: flat formula stack + iterative term walk for ATOMs. */
  int fstack_cap = 1000;
  Formula *fstack = safe_malloc(fstack_cap * sizeof(Formula));
  int ftop = 0;

  fstack[0] = f;

  while (ftop >= 0) {
    Formula cur = fstack[ftop];
    ftop--;

    if (cur->type == ATOM_FORM) {
      /* Walk the atom term tree to find variables. */
      struct { Term t; int child; } tstack[200];
      int ttop = 0;
      tstack[ttop].t = cur->atom;
      tstack[ttop].child = 0;
      ttop++;
      while (ttop > 0) {
        int idx = ttop - 1;
        Term s = tstack[idx].t;
        int c = tstack[idx].child;
        if (VARIABLE(s)) {
          int vn = VARNUM(s);
          if (vn >= 0 && vn < MAX_VARS)
            seen[vn] = TRUE;
          ttop--;
        }
        else if (c >= ARITY(s)) {
          ttop--;
        }
        else {
          tstack[idx].child = c + 1;
          if (ttop < 200) {
            tstack[ttop].t = ARG(s, c);
            tstack[ttop].child = 0;
            ttop++;
          }
        }
      }
    }
    else if (cur->type == NOT_FORM || cur->type == AND_FORM || cur->type == OR_FORM) {
      int i;
      for (i = 0; i < cur->arity; i++) {
        ftop++;
        if (ftop >= fstack_cap) { fstack_cap *= 2; fstack = safe_realloc(fstack, fstack_cap * sizeof(*fstack)); }
        fstack[ftop] = cur->kids[i];
      }
    }
  }
  safe_free(fstack);
}  /* collect_vars_in_formula */

/*************
 *
 *   and_clause_count()
 *
 *   Count the number of clauses in a CNF formula.
 *   If AND, return arity.  Otherwise return 1.
 *
 *************/

static
int and_clause_count(Formula f)
{
  return (f->type == AND_FORM) ? f->arity : 1;
}  /* and_clause_count */

/*************
 *
 *   introduce_definition()
 *
 *   Replace an AND child of an OR node with a fresh predicate atom,
 *   and append the definition clauses to *defs.
 *
 *   The AND child `sub` has children c_1, ..., c_n (each a clause/disjunction).
 *   We create a fresh predicate defn(x1,...,xk) where x_i are the free
 *   variables in sub.
 *
 *   Definition clauses (forward direction, Plaisted-Greenbaum):
 *     ~defn(vars) | c_i   for each i
 *
 *   The AND child is replaced by the atom defn(vars) in the parent.
 *
 *************/

static
Formula introduce_definition(Formula sub, Plist *defs)
{
  BOOL seen[MAX_VARS];
  int num_vars, v, j, i;
  char name[80];
  int sn;
  Term def_atom;
  Formula def_formula;

  /* Collect free variables in the subformula. */
  memset(seen, 0, sizeof(seen));
  collect_vars_in_formula(sub, seen);

  num_vars = 0;
  for (v = 0; v < MAX_VARS; v++)
    if (seen[v])
      num_vars++;

  /* Create a fresh predicate symbol. */
  sprintf(name, "defn_%d", Cnf_def_count++);
  sn = fresh_symbol(name, num_vars);
  set_symbol_type(sn, PREDICATE_SYMBOL);

  /* Build the definition atom: defn_N(x_i1, ..., x_ik) */
  def_atom = get_rigid_term(sn_to_str(sn), num_vars);
  for (j = 0, v = 0; v < MAX_VARS; v++) {
    if (seen[v])
      ARG(def_atom, j++) = get_variable_term(v);
  }

  /* Generate definition clauses: ~defn(vars) | c_i for each clause c_i.
     Each definition clause is a Formula disjunction. */
  if (sub->type == AND_FORM) {
    for (i = 0; i < sub->arity; i++) {
      Formula neg_def, clause, ci;

      /* ~defn(vars) as a Formula */
      neg_def = formula_get(0, ATOM_FORM);
      neg_def->atom = copy_term(def_atom);
      {
        Formula not_f = formula_get(1, NOT_FORM);
        not_f->kids[0] = neg_def;
        neg_def = not_f;
      }

      /* c_i: copy the clause */
      ci = formula_copy_share(sub->kids[i]);

      /* ~defn(vars) | c_i */
      clause = disjoin_flatten_simplify(neg_def, ci);

      *defs = plist_prepend(*defs, clause);
    }
  }
  else {
    /* sub is a single clause (not AND).  Definition: ~defn(vars) | sub */
    Formula neg_def, clause, ci;

    neg_def = formula_get(0, ATOM_FORM);
    neg_def->atom = copy_term(def_atom);
    {
      Formula not_f = formula_get(1, NOT_FORM);
      not_f->kids[0] = neg_def;
      neg_def = not_f;
    }

    ci = formula_copy_share(sub);
    clause = disjoin_flatten_simplify(neg_def, ci);
    *defs = plist_prepend(*defs, clause);
  }

  /* Return the positive definition atom as an ATOM_FORM formula */
  def_formula = formula_get(0, ATOM_FORM);
  def_formula->atom = def_atom;

  /* Zap the old subformula */
  zap_formula(sub);

  return def_formula;
}  /* introduce_definition */

/*************
 *
 *   cnf_def()
 *
 *   Like cnf(), but uses definitional (Tseitin) renaming when
 *   distributivity would produce more than Cnf_def_threshold clauses.
 *
 *   defs accumulates the definition clauses.
 *
 *************/

static
Formula cnf_def(Formula f, Plist *defs)
{
  /* Iterative: like cnf() but with definitional renaming before distribution. */
  typedef struct { Formula node; int child; } Cdframe;
  int cap = 1000;
  Cdframe *stack = safe_malloc(cap * sizeof(Cdframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->type != AND_FORM && cur->type != OR_FORM) {
    result = cur;
  }
  else if (cur->arity == 0) {
    result = cur;
  }
  else {
    stack[top].node = cur;
    stack[top].child = 1;
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Cdframe)); }
    cur = cur->kids[0];
    goto restart;
  }

  /* Pop and assign results. */
  while (top > 0) {
    Cdframe *fr;
    int prev_child;
    cnf_check_timeout();
    top--;
    fr = &stack[top];
    prev_child = fr->child - 1;
    fr->node->kids[prev_child] = result;

    if (fr->child < fr->node->arity) {
      int next = fr->child;
      fr->child = next + 1;
      top++;
      cur = fr->node->kids[next];
      goto restart;
    }
    /* All children done. Apply CNF-def transformation. */
    if (fr->node->type == AND_FORM) {
      result = flatten_top(fr->node);
      result = simplify_and_share(result);
    }
    else {  /* OR_FORM */
      Formula node = fr->node;
      node = dual(remove_subsumed_share(dual(node)));

      /* Definitional renaming check. */
      {
        int product, max_count, max_idx, j;
        BOOL need_rename;

        do {
          need_rename = FALSE;
          product = 1;
          max_count = 0;
          max_idx = -1;

          for (j = 0; j < node->arity; j++) {
            int cc = and_clause_count(node->kids[j]);
            if (product > Cnf_def_threshold) {
              product = Cnf_def_threshold + 1;
              break;
            }
            product *= cc;
            if (cc > max_count) {
              max_count = cc;
              max_idx = j;
            }
          }

          if (product > Cnf_def_threshold && max_count > 1 && max_idx >= 0) {
            node->kids[max_idx] = introduce_definition(node->kids[max_idx], defs);
            need_rename = TRUE;
          }
        } while (need_rename);
      }

      node = balanced_binary(node);
      node = distribute(node);
      result = node;
    }
  }

  safe_free(stack);
  return result;
}  /* cnf_def */

/*************
 *
 *   clausify_prepare()
 *
 *************/

/* DOCUMENTATION
This routine gets a formula all ready for translation into clauses.
The sequence of transformations is
<UL>
<LI> change to negation normal form;
<LI> propositional simplification;
<LI> make the universally quantified variables unique;
<LI> skolemize (nothing fancy here);
<LI> remove universal quantifiers, changing the
     constants-which-represent-variables into genuine variables;
<LI> change to conjunctive normal form
     (with basic propositional simplification).
</UL>
The caller should not refer to the given formula f after the call;
A good way to call is <TT>f = clausify_prepare(f)</TT>
*/

/* PUBLIC */
Formula clausify_prepare(Formula f)
{
  int return_code;

  formula_canon_eq(f);
  f = nnf(f);
  f = unique_quantified_vars(f);
  f = skolemize(f);
  f = remove_universal_quantifiers(f);
  f = formula_flatten(f);

  f = consolidate_formula(f);  /* causes sharing of some subformulas */

  Cnf_limit_hit = FALSE;
  Cnf_timeout_hit = FALSE;

  return_code = setjmp(Jump_env);
  if (return_code != 0) {
    /* We landed from longjmp() because CNF clause limit or timeout was
       exceeded.  The partially-transformed formula is not well-formed and
       cannot be reclaimed (memory is in palloc, never returned to OS anyway). */
    return NULL;
  }

  if (Cnf_def_threshold > 0) {
    Plist defs = NULL;
    f = cnf_def(f, &defs);
    /* Prepend definition clauses as additional AND children. */
    if (defs != NULL) {
      int def_count = 0;
      int orig_arity, new_arity, j;
      Formula result;
      Plist p;

      for (p = defs; p; p = p->next)
        def_count++;

      /* Ensure f is an AND_FORM so we can append. */
      f = make_conjunction(f);
      orig_arity = f->arity;
      new_arity = orig_arity + def_count;

      result = formula_get(new_arity, AND_FORM);
      for (j = 0; j < orig_arity; j++)
        result->kids[j] = f->kids[j];
      for (p = defs; p; p = p->next)
        result->kids[j++] = (Formula) p->v;

      free_formula(f);
      zap_plist(defs);
      f = result;
    }
  }
  else {
    f = cnf(f);
  }
  return f;
}  /* clausify_prepare */

/*************
 *
 *   ms_free_vars()
 *
 *************/

static
Formula ms_free_vars(Formula f)
{
  /* f is ALL_FORM, kids are rms, kids not AND_FORM */
  Formula child = f->kids[0];
  if (child->type != OR_FORM) {
    if (free_variable(f->qvar, child))
      return f;
    else {
      free_formula(f);
      return child;
    }
  }
  else {
    Plist free = NULL;        /* children with qvar free */
    Plist notfree = NULL;     /* children without qvar free */
    int free_count = 0;       /* size of free */
    int notfree_count = 0;    /* size of notfree */
    int i;
    for (i = child->arity-1; i >= 0; i--) {
      if (!free_variable(f->qvar, child->kids[i])) {
	notfree = plist_prepend(notfree, child->kids[i]);
	notfree_count++;
      }
      else {
	free = plist_prepend(free, child->kids[i]);
	free_count++;
      }
    }
    if (notfree_count == 0)
      return f;      /* all children have qvar free */
    else if (free_count == 0) {
      free_formula(f);
      return child;  /* no child has qvar free */
    }
    else {
      Formula or_free = formula_get(free_count , OR_FORM);
      Formula or_top = formula_get(notfree_count + 1 , OR_FORM);
      Plist p;
      for (p = free, i = 0; p; p = p->next, i++)
	or_free->kids[i] = p->v;
      for (p = notfree, i = 0; p; p = p->next, i++)
	or_top->kids[i] = p->v;
      or_top->kids[i] = f;
      f->kids[0] = or_free;
      free_formula(child);
      return or_top;
    }
  }
}  /* ms_free_vars */

/*************
 *
 *   miniscope()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula miniscope(Formula f)
{
  /* Iterative: post-order traversal with multi-phase processing.
   *
   * Phase 0: Entering a node (push frame, descend to children).
   * Phase 1: All children processed; apply node-specific post-processing.
   *
   * EXISTS: tail call -- dual, then process as ALL, then dual result.
   * ALL: process child, then distribute to AND children or ms_free_vars.
   * AND/OR: process children, then flatten/simplify/distribute.
   * ATOM/NOT: leaf (return immediately).
   *
   * Frame: {node, child_index, is_dual_exists, saved_qvar}.
   * is_dual_exists: TRUE if we dual'd an EXISTS into ALL before processing.
   *   When TRUE, we dual() the result before returning.
   */
  typedef struct {
    Formula node;
    int child;
    BOOL is_dual_exists;
    char *saved_qvar;
  } Msframe;
  int cap = 1000;
  Msframe *stack = safe_malloc(cap * sizeof(Msframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->type == ATOM_FORM || cur->type == NOT_FORM) {
    result = cur;
  }
  else if (cur->type == EXISTS_FORM) {
    /* Tail call: dual into ALL, process, dual result. */
    cur = dual(cur);
    /* Push a marker frame to dual the result back. */
    stack[top].node = NULL;
    stack[top].child = 0;
    stack[top].is_dual_exists = TRUE;
    stack[top].saved_qvar = NULL;
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Msframe)); }
    goto restart;  /* cur is now ALL_FORM */
  }
  else if (cur->type == ALL_FORM) {
    /* Push frame and process single child. */
    stack[top].node = cur;
    stack[top].child = 1;
    stack[top].is_dual_exists = FALSE;
    stack[top].saved_qvar = cur->qvar;
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Msframe)); }
    cur = cur->kids[0];
    goto restart;
  }
  else if (cur->type == AND_FORM || cur->type == OR_FORM) {
    if (cur->arity == 0) {
      result = cur;
    }
    else {
      stack[top].node = cur;
      stack[top].child = 1;
      stack[top].is_dual_exists = FALSE;
      stack[top].saved_qvar = NULL;
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Msframe)); }
      cur = cur->kids[0];
      goto restart;
    }
  }
  else {
    safe_free(stack);
    fatal_error("miniscope: formula not in nnf");
    return NULL;
  }

  /* Pop and process frames. */
  while (top > 0) {
    Msframe *fr;
    int prev_child;
    top--;
    fr = &stack[top];

    /* Check for dual-exists marker frame. */
    if (fr->is_dual_exists) {
      result = dual(result);
      continue;
    }

    prev_child = fr->child - 1;
    fr->node->kids[prev_child] = result;

    if (fr->child < fr->node->arity) {
      int next = fr->child;
      fr->child = next + 1;
      top++;
      cur = fr->node->kids[next];
      goto restart;
    }

    /* All children processed. Post-processing by node type. */
    if (fr->node->type == AND_FORM) {
      result = flatten_top(fr->node);
      result = simplify_and_share(result);
    }
    else if (fr->node->type == OR_FORM) {
      Formula node = fr->node;
      node = flatten_top(node);
      node = dual(remove_subsumed_share(dual(node)));
      node = balanced_binary(node);
      node = distribute(node);
      result = node;
    }
    else if (fr->node->type == ALL_FORM) {
      /* Child has been miniscoped. Check if result is AND. */
      if (fr->node->kids[0]->type == AND_FORM) {
        /* Distribute ALL to children. */
        int i;
        Formula and_node = fr->node->kids[0];
        char *qv = fr->saved_qvar;
        free_formula(fr->node);  /* shallow free of ALL node */
        for (i = 0; i < and_node->arity; i++) {
          Formula g = get_quant_form(ALL_FORM, qv, and_node->kids[i]);
          g = ms_free_vars(g);
          and_node->kids[i] = g;
        }
        result = and_node;
      }
      else {
        result = ms_free_vars(fr->node);
      }
    }
    else {
      result = fr->node;
    }
  }

  safe_free(stack);
  return result;
}  /* miniscope */

/*************
 *
 *   miniscope_formula()
 *
 *************/

typedef void (*sighandler_t)(int);

/* DOCUMENTATION
*/

/* PUBLIC */
Formula miniscope_formula(Formula f, unsigned mega_fid_call_limit)
{
  int return_code;
  if (mega_fid_call_limit <= 0)
    Fid_call_limit = 0;  /* no limit */
  else {
    Fid_call_limit = mega_fid_call_limit * 1000000;
    Fid_calls = 0;
  }

  return_code = setjmp(Jump_env);
  if (return_code != 0) {
    /* We just landed from longjmp(), because the limit was exceeded.
       (I'd like to reclaim the formula memory, but that would take some
       thought, because the partly transformed formula is not well formed.)
    */
    Fid_call_limit = 0;  /* no limit */
    return NULL;
  }
  else {
    /* ordinary execution */
    Formula f2 = NULL;

    formula_canon_eq(f);  /* canonicalize (naively) eqs for maximum sharing */
    f = nnf(f);
    f = formula_flatten(f);
    f = consolidate_formula(f);  /* share some subformulas */
  
    f = miniscope(f);  /* do the work */

    /* return a formula without shared subformulas */

    f2 = formula_copy(f);
    zap_formula(f);

    Fid_call_limit = 0;  /* no limit */
    return f2;
  }
}  /* miniscope_formula */

/*************
 *
 *   set_cnf_clause_limit() / cnf_limit_was_hit()
 *
 *************/

/* PUBLIC */
void set_cnf_clause_limit(int n)
{
  Cnf_clause_limit = (n > 0 ? n : 0);
}

/* PUBLIC */
int cnf_clause_limit(void)
{
  return Cnf_clause_limit;
}

/* PUBLIC */
BOOL cnf_limit_was_hit(void)
{
  return Cnf_limit_hit;
}

/*************
 *
 *   set_cnf_timeout() / cnf_timeout_was_hit()
 *
 *************/

/* PUBLIC */
void set_cnf_timeout(int seconds)
{
  if (seconds > 0)
    Cnf_timeout_deadline = time(NULL) + (time_t)seconds;
  else
    Cnf_timeout_deadline = 0;
  Cnf_timeout_counter = 0;
  Cnf_timeout_interval = 1000;
}

/* PUBLIC */
BOOL cnf_timeout_was_hit(void)
{
  return Cnf_timeout_hit;
}

/*************
 *
 *   set_cnf_def_threshold()
 *
 *************/

/* PUBLIC */
void set_cnf_def_threshold(int n)
{
  Cnf_def_threshold = (n > 0 ? n : 0);
  Cnf_def_count = 0;
}

/*************
 *
 *   cnf_max_clauses()
 *
 *************/

/* DOCUMENTATION
Given an NNF formula, return the maximum number of clauses that
it can produce.  (The maximum happens if no simplification occurs.)
*/

/* PUBLIC */
int cnf_max_clauses(Formula f)
{
  /* Iterative: frame stack with sum/product accumulation. */
  typedef struct { Formula node; int child; int accum; } Cmframe;
  int cap = 1000;
  Cmframe *stack = safe_malloc(cap * sizeof(Cmframe));
  int top = 0;
  int result = 0;
  Formula cur;

  cur = f;

restart:
  /* Skip quantifiers (tail call). */
  while (cur->type == ALL_FORM || cur->type == EXISTS_FORM)
    cur = cur->kids[0];

  if (cur->type == ATOM_FORM || cur->type == NOT_FORM) {
    result = 1;
  }
  else if (cur->type == AND_FORM || cur->type == OR_FORM) {
    if (cur->arity == 0) {
      result = (cur->type == AND_FORM) ? 0 : 1;
    }
    else {
      /* Push frame and enter first child. */
      stack[top].node = cur;
      stack[top].child = 1;
      stack[top].accum = (cur->type == AND_FORM) ? 0 : 1;
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Cmframe)); }
      cur = cur->kids[0];
      goto restart;
    }
  }
  else {
    safe_free(stack);
    fatal_error("cnf_max_clauses, formula not NNF");
    return -1;
  }

  /* Pop and combine results. */
  while (top > 0) {
    Cmframe *fr;
    top--;
    fr = &stack[top];
    if (fr->node->type == AND_FORM)
      fr->accum += result;
    else
      fr->accum *= result;

    if (fr->child < fr->node->arity) {
      /* More children to process. */
      int next = fr->child;
      fr->child = next + 1;
      top++;
      cur = fr->node->kids[next];
      goto restart;
    }
    result = fr->accum;
  }

  safe_free(stack);
  return result;
}  /* cnf_max_clauses */

