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

#include "formula.h"
#include "memory.h"

/* Private definitions and types */

/*
 * memory management
 */

#define PTRS_FORMULA PTRS(sizeof(struct formula))
static unsigned Formula_gets, Formula_frees;

static unsigned Arg_mem;  /* memory (pointers) for arrays of args */

/*************
 *
 *   Formula get_formula()
 *
 *************/

static
Formula get_formula(int arity)
{
  Formula p = get_cmem(PTRS_FORMULA);
  p->kids = get_cmem(arity);
  p->arity = arity;
  Formula_gets++;
  Arg_mem += arity;
  return(p);
}  /* get_formula */

/*************
 *
 *    free_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void free_formula(Formula p)
{
  if (p->excess_refs != 0)
    fatal_error("free_formula: freeing shared formula");
  free_mem(p->kids, p->arity);
  Arg_mem -= p->arity;
  free_mem(p, PTRS_FORMULA);
  Formula_frees++;
}  /* free_formula */

/*************
 *
 *   fprint_formula_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for data types
associated with the formula package.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_formula_mem(FILE *fp, BOOL heading)
{
  int n;
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");

  n = sizeof(struct formula);
  fprintf(fp, "formula (%4d)      %11u%11u%11u%9.1f K\n",
          n, Formula_gets, Formula_frees,
          Formula_gets - Formula_frees,
          ((Formula_gets - Formula_frees) * n) / 1024.);

  fprintf(fp, "    formula arg arrays:                              %9.1f K\n",
	  Arg_mem * BYTES_POINTER / 1024.); 

}  /* fprint_formula_mem */

/*************
 *
 *   p_formula_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) memory usage statistics for data types
associated with the formula package.
*/

/* PUBLIC */
void p_formula_mem()
{
  fprint_formula_mem(stdout, TRUE);
}  /* p_formula_mem */

/*
 *  end of memory management
 */

/*************
 *
 *   formula_megs()
 *
 *************/

/* DOCUMENTATION
Return the approximate number of megabytes in use for storage of formulas.
*/

/* PUBLIC */
unsigned formula_megs(void)
{
  unsigned bytes =
    (Formula_gets - Formula_frees) * sizeof(struct formula)
    +
    Arg_mem * BYTES_POINTER;

  return bytes / (1024 * 1024);
}  /* formula_megs */

/*************
 *
 *   formula_get()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula formula_get(int arity, Ftype type)
{
  Formula f = get_formula(arity);
  f->type = type;
  return f;
}  /* formula_get */

/*************
 *
 *   zap_formula()
 *
 *************/

/* DOCUMENTATION
Free a formula, including all of its subformulas, including its atoms.
If a subformula as excess references, the refcount is decremented instead.
*/

/* PUBLIC */
void zap_formula(Formula f)
{
  int capacity = 1000;
  Formula *stack = safe_malloc(capacity * sizeof(Formula));
  int top = 0;

  if (f == NULL) {
    safe_free(stack);
    return;
  }

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur == NULL)
      continue;
    if (cur->excess_refs > 0) {
      cur->excess_refs--;
      continue;
    }

    if (cur->type == ATOM_FORM)
      zap_term(cur->atom);
    else {
      int i;
      for (i = 0; i < cur->arity; i++) {
        top++;
        if (top >= capacity) {
          capacity *= 2;
          stack = safe_realloc(stack, capacity * sizeof(Formula));
        }
        stack[top] = cur->kids[i];
      }
    }
    if (cur->attributes)
      zap_attributes(cur->attributes);
    free_formula(cur);
  }
  safe_free(stack);
}  /* zap_formula */

/*************
 *
 *   logic_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL logic_term(Term t)
{
  return (is_term(t, true_sym(), 0) ||
	  is_term(t, false_sym(), 0) ||
	  is_term(t, not_sym(), 1) ||
	  is_term(t, and_sym(), 2) ||
	  is_term(t, or_sym(), 2) ||
	  is_term(t, imp_sym(), 2) ||
	  is_term(t, impby_sym(), 2) ||
	  is_term(t, iff_sym(), 2) ||
	  is_term(t, quant_sym(), 3));
}  /* logic_term */

/*************
 *
 *   gather_symbols_in_term()
 *
 *************/

static
void gather_symbols_in_term(Term t, int *rcounts, int *fcounts)
{
  /* Iterative pre-order traversal.  For "if" terms, the condition
     (ARG 0) is a formula-term and handled by gather_symbols_in_formula_term. */
  int stack_cap = 1000;
  Term *stack = safe_malloc(stack_cap * sizeof(Term));
  int top = 0;
  stack[0] = t;

  while (top >= 0) {
    Term cur = stack[top];
    top--;

    if (VARIABLE(cur))
      continue;

    if (is_term(cur, "if", 3)) {
      gather_symbols_in_formula_term(ARG(cur,0), rcounts, fcounts);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top] = ARG(cur, 2);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top] = ARG(cur, 1);
    }
    else {
      int i;
      fcounts[SYMNUM(cur)]++;
      for (i = ARITY(cur) - 1; i >= 0; i--) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = ARG(cur, i);
      }
    }
  }
  safe_free(stack);
}  /* gather_symbols_in_term */

/*************
 *
 *   gather_symbols_in_formula_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void gather_symbols_in_formula_term(Term t, int *rcounts, int *fcounts)
{
  /* Iterative traversal of formula-term structure. */
  int fstack_cap = 1000;
  Term *fstack = safe_malloc(fstack_cap * sizeof(Term));
  int ftop = 0;
  fstack[0] = t;

  while (ftop >= 0) {
    Term cur = fstack[ftop];
    ftop--;

    if (logic_term(cur)) {
      int i;
      for (i = ARITY(cur) - 1; i >= 0; i--) {
        if (is_term(cur, quant_sym(), 3) && i != 3)
          ;  /* skip quantifier and quantified variable */
        else {
          ftop++;
          if (ftop >= fstack_cap) { fstack_cap *= 2; fstack = safe_realloc(fstack, fstack_cap * sizeof(*fstack)); }
          fstack[ftop] = ARG(cur, i);
        }
      }
    }
    else {
      int i;
      rcounts[SYMNUM(cur)]++;
      for (i = 0; i < ARITY(cur); i++)
        gather_symbols_in_term(ARG(cur, i), rcounts, fcounts);
    }
  }
  safe_free(fstack);
}  /* gather_symbols_in_formula_term */

/*************
 *
 *   gather_symbols_in_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void gather_symbols_in_formula(Formula f, int *rcounts, int *fcounts)
{
  int fstack_cap = 1000;
  Formula *fstack = safe_malloc(fstack_cap * sizeof(Formula));
  int ftop = 0;
  fstack[0] = f;

  while (ftop >= 0) {
    Formula cur = fstack[ftop];
    ftop--;

    if (cur->type == ATOM_FORM) {
      if (is_term(cur->atom, "if", 3)) {
        gather_symbols_in_formula_term(ARG(cur->atom,0), rcounts, fcounts);
        gather_symbols_in_formula_term(ARG(cur->atom,1), rcounts, fcounts);
        gather_symbols_in_formula_term(ARG(cur->atom,2), rcounts, fcounts);
      }
      else
        gather_symbols_in_formula_term(cur->atom, rcounts, fcounts);
    }
    else {
      int i;
      for (i = cur->arity - 1; i >= 0; i--) {
        ftop++;
        if (ftop >= fstack_cap) { fstack_cap *= 2; fstack = safe_realloc(fstack, fstack_cap * sizeof(*fstack)); }
        fstack[ftop] = cur->kids[i];
      }
    }
  }
  safe_free(fstack);
}  /* gather_symbols_in_formula */

/*************
 *
 *   gather_symbols_in_formulas()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void gather_symbols_in_formulas(Plist lst, int *rcounts, int *fcounts)
{
  Plist p;
  for (p = lst; p; p = p->next)
    gather_symbols_in_formula(p->v, rcounts, fcounts);
}  /* gather_symbols_in_formulas */

/*************
 *
 *   function_symbols_in_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist function_symbols_in_formula(Formula f)
{
  int n = greatest_symnum() + 1;
  int *rcounts = safe_calloc(n, sizeof(int));
  int *fcounts = safe_calloc(n, sizeof(int));
  Ilist p;
  gather_symbols_in_formula(f, rcounts, fcounts);
  p = counts_to_set(fcounts, n);
  safe_free(rcounts);
  safe_free(fcounts);
  return p;
}  /* function_symbols_in_formula */

/*************
 *
 *   relation_symbols_in_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist relation_symbols_in_formula(Formula f)
{
  int n = greatest_symnum() + 1;
  int *rcounts = safe_calloc(n, sizeof(int));
  int *fcounts = safe_calloc(n, sizeof(int));
  Ilist p;
  gather_symbols_in_formula(f, rcounts, fcounts);
  p = counts_to_set(rcounts, n);
  safe_free(rcounts);
  safe_free(fcounts);
  return p;
}  /* relation_symbols_in_formula */

/*************
 *
 *   relation_symbol_in_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL relation_symbol_in_formula(int sn, Formula f)
{
  Ilist p = relation_symbols_in_formula(f);
  BOOL found = ilist_member(p, sn);
  zap_ilist(p);
  return found;
}  /* relation_symbol_in_formula */

/*************
 *
 *   term_to_formula()
 *
 *************/

/* DOCUMENTATION
Assume that no subterm (of t) representing a formula is a
term of type VARIABLE.  The given Term is not changed.
*/

/* PUBLIC */
Formula term_to_formula(Term t)
{
  /* Iterative version.  Phase 1: build formula tree top-down, storing
     attributes on each node.  Phase 2: post-order flatten_top pass,
     preserving attributes across flatten_top (which may free the old node). */

  /* Phase 1: build tree.  Stack entries record work items: convert
     source term tsrc and link result into parent->kids[ci]. */
  typedef struct { Term src; Formula parent; int ci; } Ttf_entry;
  int stack_cap = 1000;
  Ttf_entry *stack = safe_malloc(stack_cap * sizeof(*stack));
  int top = -1;
  Formula result = NULL;

  /* Push the root as a work item with NULL parent. */
  top++;
  stack[top].src = t;
  stack[top].parent = NULL;
  stack[top].ci = 0;

  while (top >= 0) {
    Term tsrc = stack[top].src;
    Formula parent = stack[top].parent;
    int ci = stack[top].ci;
    Attribute attributes = NULL;
    Formula f;
    Ftype type;
    top--;

    /* Strip attribute wrapper. */
    if (is_term(tsrc, attrib_sym(), 2)) {
      attributes = term_to_attributes(ARG(tsrc,1), attrib_sym());
      tsrc = ARG(tsrc,0);
    }

    if (is_term(tsrc, quant_sym(), 3)) {
      Term quant = ARG(tsrc,0);
      Term var = ARG(tsrc,1);
      Ftype qtype = (is_term(quant, all_sym(), 0) ? ALL_FORM : EXISTS_FORM);
      f = formula_get(1, qtype);
      f->qvar = sn_to_str(SYMNUM(var));
      f->attributes = attributes;
      /* Push body as child 0. */
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = ARG(tsrc,2);
      stack[top].parent = f;
      stack[top].ci = 0;
    }
    else {
      if (is_term(tsrc, true_sym(), 0))       type = AND_FORM;
      else if (is_term(tsrc, false_sym(), 0))  type = OR_FORM;
      else if (is_term(tsrc, not_sym(), 1))    type = NOT_FORM;
      else if (is_term(tsrc, and_sym(), 2))    type = AND_FORM;
      else if (is_term(tsrc, or_sym(), 2))     type = OR_FORM;
      else if (is_term(tsrc, iff_sym(), 2))    type = IFF_FORM;
      else if (is_term(tsrc, imp_sym(), 2))    type = IMP_FORM;
      else if (is_term(tsrc, impby_sym(), 2))  type = IMPBY_FORM;
      else                                     type = ATOM_FORM;

      if (type == ATOM_FORM) {
	f = formula_get(0, ATOM_FORM);
	f->atom = copy_term(tsrc);
	f->attributes = attributes;
      }
      else if (ARITY(tsrc) == 0) {
	f = formula_get(0, type);
	f->attributes = attributes;
      }
      else if (type == NOT_FORM) {
	f = formula_get(1, NOT_FORM);
	f->attributes = attributes;
	top++;
	if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
	stack[top].src = ARG(tsrc,0);
	stack[top].parent = f;
	stack[top].ci = 0;
      }
      else {
	f = formula_get(2, type);
	f->attributes = attributes;
	/* Push children: child 1 first (processed second). */
	top++;
	if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
	stack[top].src = ARG(tsrc,1);
	stack[top].parent = f;
	stack[top].ci = 1;
	top++;
	if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
	stack[top].src = ARG(tsrc,0);
	stack[top].parent = f;
	stack[top].ci = 0;
      }
    }

    /* Link into parent. */
    if (parent == NULL)
      result = f;
    else
      parent->kids[ci] = f;
  }
  safe_free(stack);

  /* Phase 2: post-order flatten_top pass.  flatten_top may free the old
     node and return a new one, so we save/restore attributes. */
  {
    typedef struct { Formula node; int child; } Ttf_p2_entry;
    int pstack_cap = 1000;
    Ttf_p2_entry *pstack = safe_malloc(pstack_cap * sizeof(*pstack));
    int ptop = 0;
    pstack[0].node = result;
    pstack[0].child = 0;

    while (ptop >= 0) {
      Formula cur = pstack[ptop].node;
      if (pstack[ptop].child < cur->arity) {
	int c = pstack[ptop].child++;
	ptop++;
	if (ptop >= pstack_cap) { pstack_cap *= 2; pstack = safe_realloc(pstack, pstack_cap * sizeof(*pstack)); }
	pstack[ptop].node = cur->kids[c];
	pstack[ptop].child = 0;
      }
      else {
	Attribute saved_attr = cur->attributes;
	cur->attributes = NULL;  /* prevent flatten_top from freeing attributes */
	Formula flat = flatten_top(cur);
	flat->attributes = saved_attr;
	if (ptop > 0) {
	  int pc = pstack[ptop-1].child - 1;
	  pstack[ptop-1].node->kids[pc] = flat;
	}
	else {
	  result = flat;
	}
	ptop--;
      }
    }
    safe_free(pstack);
  }

  return result;
}  /* term_to_formula */

/*************
 *
 *   formula_to_term()
 *
 *************/

/* DOCUMENTATION
Returns an entirely new term.
*/

/* PUBLIC */
Term formula_to_term(Formula f)
{
  /* Iterative conversion using a stack of {Formula src, Term dst, int child}.
   * We build terms top-down: create the parent Term, then push entries
   * that say "fill dst->args[child] with the conversion of src".
   */
  typedef struct { Formula src; Term dst; int child; } Ftt_entry;
  int stack_cap = 1000;
  Ftt_entry *stack = safe_malloc(stack_cap * sizeof(*stack));
  int top = -1;
  Term result = NULL;

  /* Phase 1: Create the root term for f, push children onto stack. */
  {
    Formula cur = f;
    Term t = NULL;

    switch (cur->type) {
    case ATOM_FORM:
      t = copy_term(cur->atom);
      break;
    case NOT_FORM:
      t = get_rigid_term(not_sym(), 1);
      /* Push child: kids[0] -> ARG(t,0) */
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0];
      stack[top].dst = t;
      stack[top].child = 0;
      break;
    case IFF_FORM:
      t = get_rigid_term(iff_sym(), 2);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[1]; stack[top].dst = t; stack[top].child = 1;
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0]; stack[top].dst = t; stack[top].child = 0;
      break;
    case IMP_FORM:
      t = get_rigid_term(imp_sym(), 2);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[1]; stack[top].dst = t; stack[top].child = 1;
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0]; stack[top].dst = t; stack[top].child = 0;
      break;
    case IMPBY_FORM:
      t = get_rigid_term(impby_sym(), 2);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[1]; stack[top].dst = t; stack[top].child = 1;
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0]; stack[top].dst = t; stack[top].child = 0;
      break;
    case AND_FORM:
    case OR_FORM:
      if (cur->arity == 0)
        t = get_rigid_term(cur->type == AND_FORM ? true_sym() : false_sym(), 0);
      else {
        /* Build right-associated binary chain: op(k0, op(k1, op(k2, ... kn))) */
        /* Create all the binary op nodes and the leaf slot for the last kid. */
        int i;
        char *sym = (cur->type == AND_FORM ? and_sym() : or_sym());
        /* Build chain from right: start with rightmost kid as a pending src. */
        /* First, create (arity-1) binary nodes chained right-associatively. */
        int nops = cur->arity - 1;
        Term *chain_terms = safe_calloc(nops, sizeof(Term));
        if (chain_terms == NULL)
          fatal_error("formula_to_term: malloc failed");
        for (i = 0; i < nops; i++)
          chain_terms[i] = get_rigid_term(sym, 2);
        /* Link them: chain_terms[i]->args[1] = chain_terms[i+1] */
        for (i = 0; i < nops - 1; i++)
          ARG(chain_terms[i], 1) = chain_terms[i + 1];
        t = chain_terms[0];
        /* The rightmost op node's ARG(,1) gets the last kid. Push it. */
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top].src = cur->kids[cur->arity - 1];
        stack[top].dst = chain_terms[nops - 1];
        stack[top].child = 1;
        /* Each chain_terms[i]->args[0] gets kids[i]. Push them. */
        for (i = nops - 1; i >= 0; i--) {
          top++;
          if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
          stack[top].src = cur->kids[i];
          stack[top].dst = chain_terms[i];
          stack[top].child = 0;
        }
        safe_free(chain_terms);
      }
      break;
    case ALL_FORM:
    case EXISTS_FORM:
      t = get_rigid_term(quant_sym(), 3);
      ARG(t,0) = get_rigid_term(cur->type == ALL_FORM ? all_sym() : exists_sym(), 0);
      ARG(t,1) = get_rigid_term(cur->qvar, 0);
      /* Push child: kids[0] -> ARG(t,2) */
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0];
      stack[top].dst = t;
      stack[top].child = 2;
      break;
    }

    if (cur->attributes && t != NULL)
      t = build_binary_term(str_to_sn(attrib_sym(), 2),
                            t,
                            attributes_to_term(cur->attributes, attrib_sym()));
    result = t;
  }

  /* Phase 2: Process stack entries. */
  while (top >= 0) {
    Formula cur = stack[top].src;
    Term parent = stack[top].dst;
    int ci = stack[top].child;
    top--;

    Term t = NULL;

    switch (cur->type) {
    case ATOM_FORM:
      t = copy_term(cur->atom);
      break;
    case NOT_FORM:
      t = get_rigid_term(not_sym(), 1);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0];
      stack[top].dst = t;
      stack[top].child = 0;
      break;
    case IFF_FORM:
      t = get_rigid_term(iff_sym(), 2);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[1]; stack[top].dst = t; stack[top].child = 1;
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0]; stack[top].dst = t; stack[top].child = 0;
      break;
    case IMP_FORM:
      t = get_rigid_term(imp_sym(), 2);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[1]; stack[top].dst = t; stack[top].child = 1;
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0]; stack[top].dst = t; stack[top].child = 0;
      break;
    case IMPBY_FORM:
      t = get_rigid_term(impby_sym(), 2);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[1]; stack[top].dst = t; stack[top].child = 1;
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0]; stack[top].dst = t; stack[top].child = 0;
      break;
    case AND_FORM:
    case OR_FORM:
      if (cur->arity == 0)
        t = get_rigid_term(cur->type == AND_FORM ? true_sym() : false_sym(), 0);
      else {
        int i;
        char *sym = (cur->type == AND_FORM ? and_sym() : or_sym());
        int nops = cur->arity - 1;
        Term *chain_terms = safe_calloc(nops, sizeof(Term));
        if (chain_terms == NULL)
          fatal_error("formula_to_term: malloc failed");
        for (i = 0; i < nops; i++)
          chain_terms[i] = get_rigid_term(sym, 2);
        for (i = 0; i < nops - 1; i++)
          ARG(chain_terms[i], 1) = chain_terms[i + 1];
        t = chain_terms[0];
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top].src = cur->kids[cur->arity - 1];
        stack[top].dst = chain_terms[nops - 1];
        stack[top].child = 1;
        for (i = nops - 1; i >= 0; i--) {
          top++;
          if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
          stack[top].src = cur->kids[i];
          stack[top].dst = chain_terms[i];
          stack[top].child = 0;
        }
        safe_free(chain_terms);
      }
      break;
    case ALL_FORM:
    case EXISTS_FORM:
      t = get_rigid_term(quant_sym(), 3);
      ARG(t,0) = get_rigid_term(cur->type == ALL_FORM ? all_sym() : exists_sym(), 0);
      ARG(t,1) = get_rigid_term(cur->qvar, 0);
      top++;
      if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
      stack[top].src = cur->kids[0];
      stack[top].dst = t;
      stack[top].child = 2;
      break;
    }

    if (cur->attributes && t != NULL)
      t = build_binary_term(str_to_sn(attrib_sym(), 2),
                            t,
                            attributes_to_term(cur->attributes, attrib_sym()));
    ARG(parent, ci) = t;
  }
  safe_free(stack);

  return result;
}  /* formula_to_term */

/*************
 *
 *   fprint_formula()
 *
 *************/

/* DOCUMENTATION
This routine prints a formula to a file.
If you wish to have a formula printed without extra parentheses,
you can call fprint_formula_term() instead.
*/

/* PUBLIC */
void fprint_formula(FILE *fp, Formula f)
{
  if (f->type == ATOM_FORM) {
    /* fprintf(fp, "("); */
    fprint_term(fp, f->atom);
    /* fprintf(fp, ")"); */
  }
  else if (f->type == NOT_FORM) {
    /* fprintf(fp, "(%s ", not_sym()); */
    fprintf(fp, "%s ", not_sym());
    fprint_formula(fp, f->kids[0]);
    /* fprintf(fp, ")"); */
  }
  else if (f->type == IFF_FORM) {
    fprintf(fp, "(");
    fprint_formula(fp, f->kids[0]);
    fprintf(fp, " %s ", iff_sym());
    fprint_formula(fp, f->kids[1]);
    fprintf(fp, ")");
  }
  else if (f->type == IMP_FORM) {
    fprintf(fp, "(");
    fprint_formula(fp, f->kids[0]);
    fprintf(fp, " %s ", imp_sym());
    fprint_formula(fp, f->kids[1]);
    fprintf(fp, ")");
  }
  else if (f->type == IMPBY_FORM) {
    fprintf(fp, "(");
    fprint_formula(fp, f->kids[0]);
    fprintf(fp, " %s ", impby_sym());
    fprint_formula(fp, f->kids[1]);
    fprintf(fp, ")");
  }
  else if (quant_form(f)) {
    fprintf(fp, "(%s %s ", f->type==ALL_FORM ? all_sym() : exists_sym(), f->qvar);
    fprint_formula(fp, f->kids[0]);
    fprintf(fp, ")");
  }
  else if (f->type == AND_FORM || f->type == OR_FORM) {
    if (f->arity == 0)
      fprintf(fp, "%s", f->type == AND_FORM ? true_sym() : false_sym());
    else {
      int i;
      fprintf(fp, "(");
      for (i = 0; i < f->arity; i++) {
	fprint_formula(fp, f->kids[i]);
	if (i < f->arity-1)
	  fprintf(fp, " %s ", f->type == AND_FORM ? and_sym() : or_sym());
      }
      fprintf(fp, ")");
    }
  }
}  /* fprint_formula */

/*************
 *
 *   p_formula()
 *
 *************/

/* DOCUMENTATION
This routine prints a formula, followed by ".\n" and fflush, to stdout.
If you wish to have a formula printed without extra parentheses,
you can call p_formula_term() instead.
If you don't want the newline, use fprint_formula() instead.
*/

/* PUBLIC */
void p_formula(Formula c)
{
  fprint_formula(stdout, c);
  printf(".\n");
  fflush(stdout);
}  /* p_formula */

/*************
 *
 *   hash_formula()
 *
 *************/

/* DOCUMENTATION
This is a simple hash function for formulas.
It shifts symbols by 3 bits and does exclusive ORs.
*/

/* PUBLIC */
unsigned hash_formula(Formula f)
{
  /* Iterative post-order hash using a frame stack.
   * Hash is order-dependent (left-to-right with bit shifts), so we use
   * a frame stack {node, child_index, accum} to process children in order.
   */
  typedef struct { Formula node; int child; unsigned accum; } Hframe;
  int cap = 1000;
  Hframe *stack = safe_malloc(cap * sizeof(Hframe));
  int top = 0;
  unsigned result = 0;

  stack[0].node = f;
  stack[0].child = 0;
  stack[0].accum = 0;

  while (top >= 0) {
    Hframe *fr = &stack[top];
    Formula cur = fr->node;

    if (cur->type == ATOM_FORM) {
      result = hash_term(cur->atom);
      top--;
    }
    else if (quant_form(cur)) {
      result = (cur->type << 3) ^ (unsigned) cur->qvar[0];
      top--;
    }
    else if (fr->child == 0) {
      /* First visit: initialize accumulator with the type */
      fr->accum = cur->type;
      if (cur->arity == 0) {
        result = fr->accum;
        top--;
      }
      else {
        /* Push first child */
        fr->child = 1;
        top++;
        if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Hframe)); }
        stack[top].node = cur->kids[0];
        stack[top].child = 0;
        stack[top].accum = 0;
      }
    }
    else {
      /* Returning from child: fold result into accumulator */
      fr->accum = (fr->accum << 3) ^ result;
      if (fr->child < cur->arity) {
        /* Push next child */
        int next = fr->child;
        fr->child = next + 1;
        top++;
        if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Hframe)); }
        stack[top].node = cur->kids[next];
        stack[top].child = 0;
        stack[top].accum = 0;
      }
      else {
        result = fr->accum;
        top--;
      }
    }
  }
  safe_free(stack);
  return result;
}  /* hash_formula */

/*************
 *
 *   formula_ident()
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
BOOL formula_ident(Formula f, Formula g)
{
  /* Iterative comparison using a stack of pairs. */
  typedef struct { Formula a; Formula b; } Fi_entry;
  int stack_cap = 1000;
  Fi_entry *stack = safe_malloc(stack_cap * sizeof(*stack));
  int top = 0;

  stack[0].a = f;
  stack[0].b = g;

  while (top >= 0) {
    Formula a = stack[top].a;
    Formula b = stack[top].b;
    top--;

    if (a->type != b->type || a->arity != b->arity) {
      safe_free(stack);
      return FALSE;
    }
    else if (a->type == ATOM_FORM) {
      if (!term_ident(a->atom, b->atom)) {
        safe_free(stack);
        return FALSE;
      }
    }
    else {
      int i;
      if (quant_form(a) && !str_ident(a->qvar, b->qvar)) {
        safe_free(stack);
        return FALSE;
      }
      for (i = 0; i < a->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top].a = a->kids[i];
        stack[top].b = b->kids[i];
      }
    }
  }
  safe_free(stack);
  return TRUE;
}  /* formula_ident */

/*************
 *
 *   formula_copy()
 *
 *************/

/* DOCUMENTATION
This function returns a copy of the given formula.
All subformulas, including the atoms, are copied.
*/

/* PUBLIC */
Formula formula_copy(Formula f)
{
  /* Iterative: frame stack {orig, new_node, child_index}.
   * Post-order: process children L-to-R, assign kids, return new_node.
   * Single 'result' variable for child-to-parent communication.
   */
  typedef struct { Formula orig; Formula copy; int child; } Fcframe;
  int cap = 1000;
  Fcframe *stack = safe_malloc(cap * sizeof(Fcframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->type == ATOM_FORM) {
    Formula g = formula_get(0, ATOM_FORM);
    g->atom = copy_term(cur->atom);
    result = g;
  }
  else {
    Formula g = formula_get(cur->arity, cur->type);
    if (quant_form(cur))
      g->qvar = cur->qvar;
    if (cur->arity == 0) {
      result = g;
    }
    else {
      /* Push frame and enter first child. */
      stack[top].orig = cur;
      stack[top].copy = g;
      stack[top].child = 1;
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Fcframe)); }
      cur = cur->kids[0];
      goto restart;
    }
  }

  /* Pop and assign results. */
  while (top > 0) {
    Fcframe *fr;
    int prev_child;
    top--;
    fr = &stack[top];
    prev_child = fr->child - 1;
    fr->copy->kids[prev_child] = result;

    if (fr->child < fr->orig->arity) {
      /* More children to process. */
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
}  /* formula_copy */

/*************
 *
 *   dual_type()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ftype dual_type(Ftype op)
{
  switch (op) {
  case AND_FORM: return OR_FORM;
  case OR_FORM: return AND_FORM;
  case ALL_FORM: return EXISTS_FORM;
  case EXISTS_FORM: return ALL_FORM;
  default: return op;
  }
}  /* dual */

/*************
 *
 *   dual()
 *
 *************/

/* DOCUMENTATION
Change a formula into its dual.  This is destructive.
*/

/* PUBLIC */
Formula dual(Formula f)
{
  /* Iterative traversal: visit every node, change its type. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    cur->type = dual_type(cur->type);

    {
      int i;
      for (i = 0; i < cur->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = cur->kids[i];
      }
    }
  }
  safe_free(stack);
  return f;
}  /* dual */

/*************
 *
 *   and()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula and(Formula a, Formula b)
{
  Formula f = formula_get(2, AND_FORM);
  f->kids[0] = a;
  f->kids[1] = b;
  return f;
}  /* and */

/*************
 *
 *   or()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula or(Formula a, Formula b)
{
  Formula f = formula_get(2, OR_FORM);
  f->kids[0] = a;
  f->kids[1] = b;
  return f;
}  /* or */

/*************
 *
 *   imp()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula imp(Formula a, Formula b)
{
  Formula f = formula_get(2, IMP_FORM);
  f->kids[0] = a;
  f->kids[1] = b;
  return f;
}  /* imp */

/*************
 *
 *   impby()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula impby(Formula a, Formula b)
{
  Formula f = formula_get(2, IMPBY_FORM);
  f->kids[0] = a;
  f->kids[1] = b;
  return f;
}  /* impby */

/*************
 *
 *   not()
 *
 *************/

static
Formula not(Formula a)
{
  Formula f = formula_get(1, NOT_FORM);
  f->kids[0] = a;
  return f;
}  /* not */

/*************
 *
 *   negate()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula negate(Formula a)
{
  return not(a);
}  /* negate */

/*************
 *
 *   quant_form()  -- is it a quantified formula?
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL quant_form(Formula f)
{
  return (f->type == ALL_FORM || f->type == EXISTS_FORM);
}  /* quant_form */

/*************
 *
 *   flatten_top() -- applies to AND and OR.
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula flatten_top(Formula f)
{
  if (f->type != AND_FORM && f->type != OR_FORM)
    return f;
  else {
    BOOL operate = FALSE;
    int n = 0;  /* count new arity */
    int i;
    for (i = 0; i < f->arity; i++) {
      if (f->type != f->kids[i]->type)
	n++;
      else {
	n += (f->kids[i]->arity);
	operate = TRUE;
      }
    }
    if (!operate)
      return f;
    else {
      Formula g = formula_get(n, f->type);
      int i, j;
      j = 0;
      for (i = 0; i < f->arity; i++) {
	if (f->kids[i]->type != f->type)
	  g->kids[j++] = f->kids[i];
	else {
	  int k;
	  for (k = 0; k < f->kids[i]->arity; k++)
	    g->kids[j++] = f->kids[i]->kids[k];
	  free_formula(f->kids[i]);
	}
      }
      free_formula(f);
      /* If the new formula has just one argument, return that argument. */
      if (g->arity == 1) {
	Formula h = g->kids[0];
	free_formula(g);
	return h;
      }
      else
	return g;
    }
  }
}  /* flatten_top */

/*************
 *
 *   formula_flatten()
 *
 *************/

/* DOCUMENTATION
This routine (recursively) flattens all AND and OR subformulas.
*/

/* PUBLIC */
Formula formula_flatten(Formula f)
{
  /* Iterative: post-order traversal. Process children first, then flatten_top.
   * Frame stack {node, child_index}. Result variable for child-to-parent.
   */
  typedef struct { Formula node; int child; } Ffframe;
  int cap = 1000;
  Ffframe *stack = safe_malloc(cap * sizeof(Ffframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->arity == 0) {
    result = flatten_top(cur);
  }
  else {
    /* Push frame and enter first child. */
    stack[top].node = cur;
    stack[top].child = 1;
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Ffframe)); }
    cur = cur->kids[0];
    goto restart;
  }

  /* Pop and assign results. */
  while (top > 0) {
    Ffframe *fr;
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
    result = flatten_top(fr->node);
  }

  safe_free(stack);
  return result;
}  /* flatten */
  
/*************
 *
 *   nnf2()
 *
 *************/

/* DOCUMENTATION
Transform a formula into negation normal form (NNF).  (NNF means
that all propositional connectives have been rewritten in terms of
AND, OR and NOT, and all negation signs ar up against atomic formulas).
<P>
The argument "pref" should be either CONJUNCTION or DISJUNCTION,
and it specifies the preferred form to use when translating IFFs.
<P>
This rouine is destructive; a good way to call
it is <TT>f = nnf2(f, CONJUNCTION)</TT>.
*/

/* PUBLIC */
Formula nnf2(Formula f, Fpref pref)
{
  /* Iterative with tail-call optimization.
   * Frame stack {node, child_index} for QUANT, AND/OR, NOT+QUANT, NOT+AND/OR.
   * Tail calls (IMP, IMPBY, IFF, NOT+NOT, NOT+IMP, NOT+IMPBY, NOT+IFF)
   * rewrite the node and loop back without growing the stack.
   * Single 'result' variable for child-to-parent communication.
   */
  typedef struct { Formula node; int child; } Nframe;
  int cap = 1000;
  Nframe *stack = safe_malloc(cap * sizeof(Nframe));
  int top = 0;
  Formula result = NULL;
  Formula cur;

  cur = f;

restart:
  if (cur->type == ATOM_FORM) {
    result = cur;
  }
  else if (quant_form(cur)) {
    /* Push resume frame, enter child. */
    stack[top].node = cur;
    stack[top].child = 1;
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Nframe)); }
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
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Nframe)); }
      cur = cur->kids[0];
      goto restart;
    }
  }
  else if (cur->type == IMP_FORM) {
    /* Tail call: or(not(kids[0]), kids[1]) */
    Formula g = or(not(cur->kids[0]), cur->kids[1]);
    free_formula(cur);
    cur = g;
    goto restart;
  }
  else if (cur->type == IMPBY_FORM) {
    /* Tail call: or(kids[0], not(kids[1])) */
    Formula g = or(cur->kids[0], not(cur->kids[1]));
    free_formula(cur);
    cur = g;
    goto restart;
  }
  else if (cur->type == IFF_FORM) {
    /* Tail call: rewrite IFF and retry. */
    Formula a = cur->kids[0];
    Formula b = cur->kids[1];
    Formula ac = formula_copy(a);
    Formula bc = formula_copy(b);
    Formula g;
    if (pref == CONJUNCTION)
      g = and(imp(a,b), impby(ac,bc));
    else
      g = or(and(a,b), and(not(ac),not(bc)));
    free_formula(cur);
    cur = g;
    goto restart;
  }
  else if (cur->type == NOT_FORM) {
    Formula h = cur->kids[0];
    if (h->type == ATOM_FORM) {
      result = cur;
    }
    else if (h->type == NOT_FORM) {
      /* Tail call: unwrap double negation. */
      Formula inner = h->kids[0];
      free_formula(h);
      free_formula(cur);
      cur = inner;
      goto restart;
    }
    else if (quant_form(h)) {
      /* NOT+QUANT: build dual, push resume, enter not(child). */
      Formula g = formula_get(1, dual_type(h->type));
      Formula nkid = not(h->kids[0]);
      g->qvar = h->qvar;
      free_formula(h);
      free_formula(cur);
      stack[top].node = g;
      stack[top].child = 1;
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Nframe)); }
      cur = nkid;
      goto restart;
    }
    else if (h->type == AND_FORM || h->type == OR_FORM) {
      /* NOT+AND/OR: De Morgan. Build dual node with not(kids). */
      Formula g = formula_get(h->arity, dual_type(h->type));
      int i;
      for (i = 0; i < h->arity; i++)
        g->kids[i] = not(h->kids[i]);
      free_formula(h);
      free_formula(cur);
      if (g->arity == 0) {
        result = g;
      }
      else {
        stack[top].node = g;
        stack[top].child = 1;
        top++;
        if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Nframe)); }
        cur = g->kids[0];
        goto restart;
      }
    }
    else if (h->type == IMP_FORM) {
      /* Tail call: and(kids[0], not(kids[1])) */
      Formula g = and(h->kids[0], not(h->kids[1]));
      free_formula(h);
      free_formula(cur);
      cur = g;
      goto restart;
    }
    else if (h->type == IMPBY_FORM) {
      /* Tail call: and(not(kids[0]), kids[1]) */
      Formula g = and(not(h->kids[0]), h->kids[1]);
      free_formula(h);
      free_formula(cur);
      cur = g;
      goto restart;
    }
    else if (h->type == IFF_FORM) {
      /* Tail call: rewrite NOT+IFF and retry. */
      Formula a = h->kids[0];
      Formula b = h->kids[1];
      Formula ac = formula_copy(a);
      Formula bc = formula_copy(b);
      Formula g;
      if (pref == CONJUNCTION)
        g = and(or(a,b), or(not(ac),not(bc)));
      else
        g = or(and(a,not(b)), and(not(ac),bc));
      free_formula(h);
      free_formula(cur);
      cur = g;
      goto restart;
    }
    else {
      result = cur;
    }
  }
  else {
    result = cur;
  }

  /* Pop and assign results. */
  while (top > 0) {
    Nframe *fr;
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
}  /* nnf2 */

/*************
 *
 *   nnf()
 *
 *************/

/* DOCUMENTATION
Transform a formula into negation normal form (NNF).  (NNF means
that all propositional connectives have been rewritten in terms of
AND, OR and NOT, and all negation signs ar up against atomic formulas).
<P>
This routine is destructive; a good way to call
it is <TT>f = nnf(f)</TT>.
*/

/* PUBLIC */
Formula nnf(Formula f)
{
  return nnf2(f, CONJUNCTION);
}  /* nnf */

/*************
 *
 *   make_conjunction()
 *
 *************/

/* DOCUMENTATION
If the formula is not a conjunction, make it so.
*/

/* PUBLIC */
Formula make_conjunction(Formula f)
{
  if (f->type == AND_FORM)
    return f;
  else {
    Formula h = formula_get(1, AND_FORM);
    h->kids[0] = f;
    return h;
  }
}  /* make_conjunction */

/*************
 *
 *   make_disjunction()
 *
 *************/

/* DOCUMENTATION
If the formula is not a dismunction, make it so.
*/

/* PUBLIC */
Formula make_disjunction(Formula f)
{
  if (f->type == OR_FORM)
    return f;
  else {
    Formula h = formula_get(1, OR_FORM);
    h->kids[0] = f;
    return h;
  }
}  /* make_disjunction */

/*************
 *
 *   formula_canon_eq()
 *
 *************/

/* DOCUMENTATION
For each equality in the formula, if the right side greater
according to "term_compare_ncv", flip the equality.
*/

/* PUBLIC */
void formula_canon_eq(Formula f)
{
  /* Iterative: flat stack, modify ATOMs in-place. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur->type == ATOM_FORM) {
      Term a = cur->atom;
      if (eq_term(a)) {
        Term left = ARG(a,0);
        Term right = ARG(a,1);
        if (term_compare_ncv(left, right) == LESS_THAN) {
          ARG(a,0) = right;
          ARG(a,1) = left;
        }
      }
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
}  /* formula_canon_eq */

/*************
 *
 *   formula_size()
 *
 *************/

/* DOCUMENTATION
How many nodes are in the formula.  (Atomic formulae count as 1.)
*/

/* PUBLIC */
int formula_size(Formula f)
{
  /* Iterative traversal with accumulator. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;
  int n = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;
    n++;

    if (cur->type != ATOM_FORM) {
      int i;
      for (i = 0; i < cur->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = cur->kids[i];
      }
    }
  }
  safe_free(stack);
  return n;
}  /* formula_size */

/*************
 *
 *   greatest_qvar()
 *
 *************/

/* DOCUMENTATION
Return the greatest SYMNUM of a quantified variable in Formula f.
<P>
Recall that in Formulas, a quantified variable is represented
as a constant (which is bound by the quantifier).
If the formula has no quantified variables, return -1.
*/

/* PUBLIC */
int greatest_qvar(Formula f)
{
  /* Iterative traversal with max accumulator. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;
  int max = -1;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (quant_form(cur)) {
      int sn = str_to_sn(cur->qvar, 0);
      if (sn > max)
        max = sn;
    }

    {
      int i;
      for (i = 0; i < cur->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = cur->kids[i];
      }
    }
  }
  safe_free(stack);
  return max;
}  /* greatest_qvar */

/*************
 *
 *   greatest_symnum_in_formula()
 *
 *************/

/* DOCUMENTATION
Return the greatest SYMNUM of a any subterm.  This includes quantifed
variables that don't occur in any term.
<P>
This routine is intended to be used if you need malloc an array
for indexing by SYMNUM.
*/

/* PUBLIC */
int greatest_symnum_in_formula(Formula f)
{
  /* Iterative: flat stack + running max (commutative). */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;
  int max = -1;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    int val;
    top--;

    if (cur->type == ATOM_FORM) {
      val = greatest_symnum_in_term(cur->atom);
      if (val > max) max = val;
    }
    else {
      int i;
      if (quant_form(cur)) {
        val = str_to_sn(cur->qvar, 0);
        if (val > max) max = val;
      }
      for (i = 0; i < cur->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = cur->kids[i];
      }
    }
  }
  safe_free(stack);
  return max;
}  /* greatest_symnum_in_formula */

/*************
 *
 *   subst_free_var()
 *
 *************/

/* DOCUMENTATION
In formula f, substitute free occurrences of target
with replacement.  The function term_ident() is used,
and the target can be any term.
*/

/* PUBLIC */
void subst_free_var(Formula f, Term target, Term replacement)
{
  /* Iterative traversal. Skip subtrees under quantifiers that bind target. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur->type == ATOM_FORM)
      cur->atom = subst_term(cur->atom, target, replacement);
    else if (quant_form(cur) && str_ident(sn_to_str(SYMNUM(target)), cur->qvar)) {
      ; /* Do nothing, because we have a quantified variable of the same name. */
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
}  /* subst_free_var */

/*************
 *
 *   elim_rebind()
 *
 *************/

static
Formula elim_rebind(Formula f, Ilist uvars)
{
  /* Iterative version.  We use a work stack.  Each entry is either:
   *   - A formula to process (phase == 0), with the current uvars context.
   *   - A cleanup marker (phase == 1) indicating we should pop a uvars node
   *     and free a term when we leave a quantifier scope.
   */
  typedef struct { Formula node; Ilist uvars_ctx; Term var_to_free; int phase; } Er_entry;
  int stack_cap = 1000;
  Er_entry *stack = safe_malloc(stack_cap * sizeof(*stack));
  int top = 0;

  stack[0].node = f;
  stack[0].uvars_ctx = uvars;
  stack[0].var_to_free = NULL;
  stack[0].phase = 0;

  while (top >= 0) {
    if (stack[top].phase == 1) {
      /* Cleanup: pop a uvars node we prepended. */
      Ilist node_to_free = stack[top].uvars_ctx;
      if (stack[top].var_to_free)
        free_term(stack[top].var_to_free);
      if (node_to_free)
        free_ilist(node_to_free);  /* frees first node only */
      top--;
      continue;
    }

    {
      Formula cur = stack[top].node;
      Ilist cur_uvars = stack[top].uvars_ctx;
      top--;

      if (quant_form(cur)) {
        Term var = get_rigid_term(cur->qvar, 0);
        Ilist uvars_plus;

        if (ilist_member(cur_uvars, SYMNUM(var))) {
          int sn = gen_new_symbol("y", 0, cur_uvars);
          Term newvar = get_rigid_term(sn_to_str(sn), 0);
          subst_free_var(cur->kids[0], var, newvar);
          cur->qvar = sn_to_str(sn);
          free_term(var);
          var = newvar;
        }

        uvars_plus = ilist_prepend(cur_uvars, SYMNUM(var));

        /* Push cleanup marker first (will be processed after child). */
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top].node = NULL;
        stack[top].uvars_ctx = uvars_plus;
        stack[top].var_to_free = var;
        stack[top].phase = 1;

        /* Push the child with the extended uvars context. */
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top].node = cur->kids[0];
        stack[top].uvars_ctx = uvars_plus;
        stack[top].var_to_free = NULL;
        stack[top].phase = 0;
      }
      else {
        int i;
        for (i = 0; i < cur->arity; i++) {
          top++;
          if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
          stack[top].node = cur->kids[i];
          stack[top].uvars_ctx = cur_uvars;
          stack[top].var_to_free = NULL;
          stack[top].phase = 0;
        }
      }
    }
  }
  safe_free(stack);
  return f;
}  /* elim_rebind */

/*************
 *
 *   eliminate_rebinding()
 *
 *************/

/* DOCUMENTATION
This routine renames quantified variables so that
no quantified variable occurs in the scope of a quantified variable
with the same name.
<P>
If you wish to rename variables so that each
quantifer has a unique variable,
you can use the routine unique_quantified_vars() instead.
<P>
The argument f is "used up" during the procedure.
<P>
(This could be a void routine, because
none of the formula nodes is changed; I made it return the Formula
so that it is consistent with its friends.)
*/

/* PUBLIC */
Formula eliminate_rebinding(Formula f)
{
  f = elim_rebind(f, NULL);
  return f;
}  /* eliminate_rebinding */

/*************
 *
 *   free_vars()
 *
 *************/

static
Plist free_vars(Formula f, Plist vars)
{
  /* Iterative: frame stack with scoped quantifier variable handling.
   *
   * Non-QUANT nodes (AND/OR/NOT): thread vars through children sequentially.
   * QUANT nodes: start child with fresh NULL vars, on resume remove qvar
   * from child vars, union with parent vars.
   *
   * Frame: {node, child_index, parent_vars, is_quant, qvar_term}.
   */
  typedef struct {
    Formula node;
    int child;
    Plist parent_vars;
    BOOL is_quant;
    Term qvar_term;
  } Fvframe;
  int cap = 1000;
  Fvframe *stack = safe_malloc(cap * sizeof(Fvframe));
  int top = 0;
  Plist cur_vars;
  Formula cur;

  cur = f;
  cur_vars = vars;

restart:
  if (cur->type == ATOM_FORM) {
    cur_vars = free_vars_term(cur->atom, cur_vars);
    /* result is cur_vars; fall through to pop loop */
  }
  else if (quant_form(cur)) {
    /* Save parent vars, process child with fresh NULL vars. */
    stack[top].node = cur;
    stack[top].child = 1;
    stack[top].parent_vars = cur_vars;
    stack[top].is_quant = TRUE;
    stack[top].qvar_term = get_rigid_term(cur->qvar, 0);
    top++;
    if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Fvframe)); }
    cur_vars = NULL;
    cur = cur->kids[0];
    goto restart;
  }
  else {
    if (cur->arity == 0) {
      /* No children, cur_vars unchanged. */
    }
    else {
      /* Push frame and enter first child. */
      stack[top].node = cur;
      stack[top].child = 1;
      stack[top].parent_vars = (Plist) 0;  /* unused for non-quant */
      stack[top].is_quant = FALSE;
      stack[top].qvar_term = NULL;
      top++;
      if (top >= cap) { cap *= 2; stack = safe_realloc(stack, cap * sizeof(Fvframe)); }
      cur = cur->kids[0];
      goto restart;
    }
  }

  /* Pop and combine results. */
  while (top > 0) {
    Fvframe *fr;
    top--;
    fr = &stack[top];

    if (fr->is_quant) {
      /* Returning from QUANT child. cur_vars = child's free vars. */
      cur_vars = tlist_remove(fr->qvar_term, cur_vars);
      cur_vars = tlist_union(fr->parent_vars, cur_vars);
      zap_term(fr->qvar_term);
      /* QUANT has exactly 1 child, so we're done with this frame. */
    }
    else {
      /* Non-QUANT: check for more children. */
      if (fr->child < fr->node->arity) {
        int next = fr->child;
        fr->child = next + 1;
        top++;
        cur = fr->node->kids[next];
        goto restart;
      }
      /* All children done; cur_vars has accumulated result. */
    }
  }

  return cur_vars;
}  /* free_vars */

/*************
 *
 *   closed_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL closed_formula(Formula f)
{
  Plist vars = free_vars(f, NULL);  /* deep (returns new terms) */
  BOOL ok = (vars == NULL);
  zap_tlist(vars);
  return ok;
}  /* closed_formula */

/*************
 *
 *   get_quant_form()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Formula get_quant_form(Ftype type, char *qvar, Formula subformula)
{
  Formula f = formula_get(1, type);
  f->qvar = qvar;
  f->kids[0] = subformula;
  return f;
}  /* get_quant_form */

/*************
 *
 *   uni_close()
 *
 *************/

static
Formula uni_close(Formula f, Plist vars)
{
  /* The recursive version wraps f starting from the last variable in the list
   * (innermost quantifier) back to the first (outermost).  We iterate by
   * first finding the end, then wrapping from end to beginning.
   * Alternatively, we can collect the vars into an array and iterate backwards.
   */
  Plist p;
  /* Count the variables. */
  int n = 0;
  for (p = vars; p; p = p->next)
    n++;
  if (n == 0)
    return f;
  else {
    /* Walk the list; wrap f from last to first. */
    Plist arr[1000];
    int i;
    if (n > 1000) fatal_error("uni_close: stack overflow");
    i = 0;
    for (p = vars; p; p = p->next)
      arr[i++] = p;
    /* Wrap from last (innermost) to first (outermost). */
    for (i = n - 1; i >= 0; i--) {
      Term v = arr[i]->v;
      f = get_quant_form(ALL_FORM, sn_to_str(SYMNUM(v)), f);
    }
    return f;
  }
}  /* uni_close */

/*************
 *
 *   universal_closure()
 *
 *************/

/* DOCUMENTATION
Construct the universal closure of Formula f.  The Formula
is consumed during the construction.
*/

/* PUBLIC */
Formula universal_closure(Formula f)
{
  Plist vars = free_vars(f, NULL);  /* deep (returns new terms) */
  f = uni_close(f, vars);
  zap_tlist(vars);
  return f;
}  /* universal_closure */

/*************
 *
 *   free_var()
 *
 *************/

static
BOOL free_var(char *svar, Term tvar, Formula f)
{
  /* Iterative: flat stack, early exit on TRUE. Stops at binding quantifiers. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur->type == ATOM_FORM) {
      if (occurs_in(tvar, cur->atom)) {
        safe_free(stack);
        return TRUE;
      }
    }
    else if (quant_form(cur) && str_ident(svar, cur->qvar)) {
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
  return FALSE;
}  /* free_var */

/*************
 *
 *   free_variable()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL free_variable(char *svar, Formula f)
{
  Term tvar = get_rigid_term(svar, 0);
  BOOL free = free_var(svar, tvar, f);
  free_term(tvar);
  return free;
}  /* free_variable */

/*************
 *
 *   formulas_to_conjunction
 *
 *************/

/* DOCUMENTATION
Given a Plist of formulas, form a conjunction of the members.
The formulas are not copied, and the Plist is not freed, so
you may wish to call zap_plist after the call to this routine.
<p>
Note that the empty conjunction is TRUE.
*/

/* PUBLIC */
Formula formulas_to_conjunction(Plist formulas)
{
  Plist p;
  int n = plist_count(formulas);
  Formula f = formula_get(n, AND_FORM);
  int i = 0;
  for (p = formulas; p; p = p->next) {
    f->kids[i++] = p->v;
  }
  return f;
}  /* formulas_to_conjunction */

/*************
 *
 *   formulas_to_disjunction
 *
 *************/

/* DOCUMENTATION
Given a Plist of formulas, form a disjunction of the members.
The formulas are not copied, and the Plist is not freed, so
you may wish to call zap_plist after the call to this routine.
<p>
Note that the empty disjunction is FALSE.
*/

/* PUBLIC */
Formula formulas_to_disjunction(Plist formulas)
{
  Plist p;
  int n = plist_count(formulas);
  Formula f = formula_get(n, OR_FORM);
  int i = 0;
  for (p = formulas; p; p = p->next) {
    f->kids[i++] = p->v;
  }
  return f;
}  /* formulas_to_disjunction */

/*************
 *
 *   copy_plist_of_formulas()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist copy_plist_of_formulas(Plist formulas)
{
  Plist head = NULL;
  Plist *tail = &head;
  while (formulas != NULL) {
    Plist node = get_plist();
    node->v = formula_copy(formulas->v);
    node->next = NULL;
    *tail = node;
    tail = &node->next;
    formulas = formulas->next;
  }
  return head;
}  /* copy_plist_of_formulas */

/*************
 *
 *   literal_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL literal_formula(Formula f)
{
  if (f->type == ATOM_FORM)
    return TRUE;
  else if (f->type == NOT_FORM)
    return f->kids[0]->type == ATOM_FORM;
  else
    return FALSE;
}  /* literal_formula */

/*************
 *
 *   clausal_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL clausal_formula(Formula f)
{
  /* Iterative: flat stack on OR children, check literal_formula on non-OR. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur->type == OR_FORM) {
      int i;
      for (i = 0; i < cur->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = cur->kids[i];
      }
    }
    else if (!literal_formula(cur)) {
      safe_free(stack);
      return FALSE;
    }
  }
  safe_free(stack);
  return TRUE;
}  /* clausal_formula */

/*************
 *
 *   formula_set_vars_recurse()
 *
 *************/

static
void formula_set_vars_recurse(Formula f, char *vnames[], int max_vars)
{
  /* Iterative: flat stack, modify ATOMs in-place. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur->type == ATOM_FORM)
      cur->atom = set_vars_recurse(cur->atom, vnames, max_vars);
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
}  /* formula_set_vars_recurse */

/*************
 *
 *   formula_set_variables()
 *
 *************/

/* DOCUMENTATION
This routine traverses a formula and changes the constants
that should be variables, into variables.  On input, the formula
should have no variables.  The new variables are numbered
0, 1, 2 ... according the the first occurrence, reading from the
left.
<P>
A fatal error occurs if there are more than max_vars variables.
<P>
The intended is use is for input formulas that
are built without regard to variable/constant distinction.
*/

/* PUBLIC */
void formula_set_variables(Formula f, int max_vars)
{
  char *a[MAX_VARS], **vmap;
  int i;

  if (max_vars > MAX_VARS)
    vmap = safe_malloc((max_vars * sizeof(char *)));
  else
    vmap = a;

  for (i = 0; i < max_vars; i++)
    vmap[i] = NULL;

  formula_set_vars_recurse(f, vmap, max_vars);

  /* Now do any answer attributes (with the same vmap). */

  if (f->attributes) {
    set_vars_attributes(f->attributes, vmap, max_vars);
#if 0
    /* Make sure that answer vars also occur in formula. */
    Plist attr_vars = vars_in_attributes(c->attributes);
    Plist formula_vars = vars_in_formula(c);
    if (!plist_subset(attr_vars, formula_vars)) {
      Plist p;
      printf("Variables in answers must also occur ordinary literals:\n");
      p_formula(c);
      for (p = attr_vars; p; p = p->next) {
	if (!plist_member(formula_vars, p->v)) {
	  Term t = p->v;
	  printf("Answer variable not in ordinary literal: %s.\n",
		 vmap[VARNUM(t)]);
	}
      }
      fatal_error("formula_set_variables, answer variable not in literal");
    }
    zap_plist(formula_vars);
    zap_plist(attr_vars);
#endif
  }
  
  if (max_vars > MAX_VARS)
    safe_free(vmap);

}  /* formula_set_variables */

/*************
 *
 *   positive_formula()
 *
 *************/

/* DOCUMENTATION
Ignoring quantifiers, does the formula consist of an atomic
formula or the conjunction of atomic formulas?
*/

/* PUBLIC */
BOOL positive_formula(Formula f)
{
  /* Iterative: stack-based check with early exit on FALSE. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula g = stack[top];
    top--;

    /* Skip quantifiers. */
    while (quant_form(g))
      g = g->kids[0];

    if (g->type == ATOM_FORM)
      ;  /* ok, continue checking rest of stack */
    else if (g->type != AND_FORM) {
      safe_free(stack);
      return FALSE;
    }
    else {
      int i;
      for (i = 0; i < g->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = g->kids[i];
      }
    }
  }
  safe_free(stack);
  return TRUE;
}  /* positive_formula */

/*************
 *
 *   formula_contains_attributes()
 *
 *************/

/* DOCUMENTATION
Does the formula or any of its subformulas contain attributes?
*/

/* PUBLIC */
BOOL formula_contains_attributes(Formula f)
{
  /* Iterative: flat stack, early exit on TRUE. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur->attributes != NULL) {
      safe_free(stack);
      return TRUE;
    }
    if (cur->type != ATOM_FORM) {
      int i;
      for (i = 0; i < cur->arity; i++) {
        top++;
        if (top >= stack_cap) { stack_cap *= 2; stack = safe_realloc(stack, stack_cap * sizeof(*stack)); }
        stack[top] = cur->kids[i];
      }
    }
  }
  safe_free(stack);
  return FALSE;
}  /* formula_contains_attributes */

/*************
 *
 *   subformula_contains_attributes()
 *
 *************/

/* DOCUMENTATION
Does any proper subformula contain attributes?
*/

/* PUBLIC */
BOOL subformula_contains_attributes(Formula f)
{
  if (f->type == ATOM_FORM)
    return FALSE;
  else {
    int i;
    for (i = 0; i < f->arity; i++)
      if (formula_contains_attributes(f->kids[i]))
	return TRUE;
    return FALSE;
  }
}  /* subformula_contains_attributes */

/*************
 *
 *   constants_in_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist constants_in_formula(Formula f)
{
  Ilist p = function_symbols_in_formula(f);
  p = symnums_of_arity(p, 0);
  return p;
}  /* constants_in_formula */

/*************
 *
 *   relation_in_formula()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL relation_in_formula(Formula f, int symnum)
{
  /* Iterative: flat stack, early exit on TRUE. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (cur->type == ATOM_FORM) {
      if (SYMNUM(cur->atom) == symnum) {
        safe_free(stack);
        return TRUE;
      }
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
  return FALSE;
}  /* relation_in_formula */

/*************
 *
 *   rename_all_bound_vars()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void rename_all_bound_vars(Formula f)
{
  /* Iterative traversal. Process quantifier nodes and push children. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (quant_form(cur)) {
      Term var = get_rigid_term(cur->qvar, 0);
      int sn = fresh_symbol("x", 0);
      Term newvar = get_rigid_term(sn_to_str(sn), 0);
      subst_free_var(cur->kids[0], var, newvar);
      cur->qvar = sn_to_str(sn);
      free_term(var);
      free_term(newvar);
      /* Push the child (now with substituted variable) for further processing. */
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
}  /* rename_all_bound_vars */

/*************
 *
 *   rename_these_bound_vars()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void rename_these_bound_vars(Formula f, Ilist vars)
{
  /* Iterative: flat stack. QUANT: check & rename qvar. */
  int stack_cap = 1000;
  Formula *stack = safe_malloc(stack_cap * sizeof(Formula));
  int top = 0;

  stack[0] = f;

  while (top >= 0) {
    Formula cur = stack[top];
    top--;

    if (quant_form(cur)) {
      Term var = get_rigid_term(cur->qvar, 0);
      if (ilist_member(vars, SYMNUM(var))) {
        int sn = fresh_symbol("x", 0);
        Term newvar = get_rigid_term(sn_to_str(sn), 0);
        subst_free_var(cur->kids[0], var, newvar);
        cur->qvar = sn_to_str(sn);
        free_term(var);
      }
      /* Push child for further processing */
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
}  /* rename_these_bound_vars */



