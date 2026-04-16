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

#include "weight.h"
#include "weight2.h"
#include "parse.h"
#include "complex.h"

/* Private definitions and types */

static Plist Rules;

/* Wos-style resonators (see init_resonators). */
struct resonator {
  Term pattern;  /* the match template (raw term) */
  double wt;     /* the integer weight assigned to matching clauses */
};
static Plist Resonators = NULL;
static int Num_resonators = 0;
static int Num_resonator_matches = 0;

static double Constant_weight;
static double Sk_constant_weight;
static double Not_weight;
static double Or_weight;
static double Prop_atom_weight;
static double Variable_weight;
static double Nest_penalty;
static double Depth_penalty;
static double Var_penalty;
static double Complexity;
static BOOL Not_rules;  /* any rules for not_sym()? */
static BOOL Or_rules;   /* any rules for or_sym()? */

/* Cache the symnums */

static int Eq_sn;      /* equality */
static int Weight_sn;  /* weight function*/

static int Sum_sn;     /* integer arithmetic */
static int Prod_sn;    /* integer arithmetic */
static int Neg_sn;     /* integer arithmetic */
static int Div_sn;     /* integer arithmetic */
static int Max_sn;     /* integer arithmetic */
static int Min_sn;     /* integer arithmetic */
static int Depth_sn;   /* depth */
static int Vars_sn;    /* vars */
static int Call_sn;    /* vars */
/* Avar_sn removed -- replaced by anyvar_ctx[] in match_weight calls */

/*************
 *
 *   weight_beta_check()
 *
 *************/

static
BOOL weight_beta_check(Term b)
{
  /* Iterative check using explicit stack. */
  Term stack[1000];
  int top = 0;
  stack[0] = b;

  while (top >= 0) {
    Term cur = stack[top];
    top--;

    if (SYMNUM(cur) == Sum_sn ||
        SYMNUM(cur) == Prod_sn ||
        SYMNUM(cur) == Div_sn ||
        SYMNUM(cur) == Min_sn ||
        SYMNUM(cur) == Max_sn) {
      top++; stack[top] = ARG(cur, 0);
      top++; stack[top] = ARG(cur, 1);
    }
    else if (SYMNUM(cur) == Neg_sn) {
      top++; stack[top] = ARG(cur, 0);
    }
    else if (SYMNUM(cur) == Depth_sn ||
             SYMNUM(cur) == Vars_sn ||
             SYMNUM(cur) == Call_sn ||
             SYMNUM(cur) == Weight_sn) {
      /* ok -- leaf in the check */
    }
    else {
      double d;
      if (!term_to_number(cur, &d)) {
        printf("weight_rule_check, right side of rule not understood\n");
        return FALSE;
      }
    }
  }
  return TRUE;
}  /* weight_beta_check */

/*************
 *
 *   weight_rule_check()
 *
 *************/

static
BOOL weight_rule_check(Term rule)
{
  if (!is_eq_symbol(SYMNUM(rule))) {
    printf("weight_rule_check, rule is not equality\n");
    return FALSE;
  }
  else  if (SYMNUM(ARG(rule, 0)) != Weight_sn) {
    printf("weight_rule_check, left side must be weight(...)\n");
    return FALSE;
  }
  else
    return weight_beta_check(ARG(rule, 1));
}  /* weight_rule_check */

/*************
 *
 *   init_weight()
 *
 *************/

/* DOCUMENTATION
Initialize weighting.  The rules are copied.
*/

/* PUBLIC */
void init_weight(Plist rules,
		 double variable_weight,
		 double constant_weight,
		 double not_weight,
		 double or_weight,
		 double sk_constant_weight,
		 double prop_atom_weight,
		 double nest_penalty,
		 double depth_penalty,
		 double var_penalty,
		 double complexity)
{
  Plist p;

  Variable_weight = variable_weight;
  Constant_weight = constant_weight;
  Not_weight = not_weight;
  Or_weight = or_weight;
  Prop_atom_weight = prop_atom_weight;
  Sk_constant_weight = sk_constant_weight;
  Nest_penalty = nest_penalty;
  Depth_penalty = depth_penalty;
  Var_penalty = var_penalty;
  Complexity = complexity;

  /* Cache symbol numbers. */

  Weight_sn  = str_to_sn("weight", 1);
  Eq_sn  = str_to_sn(eq_sym(), 2);

  Sum_sn  = str_to_sn("+", 2);
  Prod_sn = str_to_sn("*", 2);
  Div_sn  = str_to_sn("/", 2);
  Max_sn  = str_to_sn("max", 2);
  Min_sn  = str_to_sn("min", 2);
  Depth_sn  = str_to_sn("depth", 1);
  Vars_sn  = str_to_sn("vars", 1);
  Call_sn  = str_to_sn("call", 2);
  Neg_sn  = str_to_sn("-", 1);
  /* Process the rules. */

  Rules = NULL;
  for (p = rules; p; p = p->next) {
    Term rule = copy_term(p->v);
    if (!weight_rule_check(rule)) {
      p_term(rule);
      fatal_error("init_weight, bad rule");
    }
    else {
      term_set_variables(rule, MAX_VARS);
      Rules = plist_append(Rules, rule);
      if (is_term(ARG(ARG(rule,0),0), not_sym(), 1))
	Not_rules = TRUE;
      if (is_term(ARG(ARG(rule,0),0), or_sym(), 2))
	Or_rules = TRUE;
    }
  }
}  /* init_weight */

/*************
 *
 *   init_resonators()
 *
 *************/

/* DOCUMENTATION
Install Wos-style resonators for clause weighting.  Each resonator
in the rules list must be a term of the form weight(pattern, N),
where N is an integer or numeric constant giving the flat weight
assigned to clauses whose literals match the pattern under Wos
semantics (every variable position -- named or anonymous -- is an
independent wildcard that matches any subterm, including complex
terms).  Resonators are consulted before ordinary weight rules
(first-match-wins across the resonator list); a clause matching
any resonator gets that resonator's weight in place of its normal
symbol-count weight.  This supports both Otter-style given-clause
selection bias (lower weight = higher priority) and Otter-style
pick_and_purge retention (max_weight deletion uses the same rule
set).  Pass NULL or an empty list to install no resonators (the
default; existing list(weights) behavior is unchanged).
*/

/* PUBLIC */
void init_resonators(Plist resonators)
{
  Plist p;
  Resonators = NULL;
  Num_resonators = 0;
  Num_resonator_matches = 0;
  for (p = resonators; p; p = p->next) {
    Term t = p->v;
    Term pattern;
    double wt;
    struct resonator *r;
    if (!is_term(t, "weight", 2)) {
      p_term(t);
      fatal_error("init_resonators: each resonator must be weight(pattern, N)");
    }
    pattern = copy_term(ARG(t, 0));
    if (!term_to_number(ARG(t, 1), &wt)) {
      p_term(t);
      fatal_error("init_resonators: second argument must be numeric");
    }
    term_set_variables(pattern, MAX_VARS);
    r = safe_malloc(sizeof(struct resonator));
    r->pattern = pattern;
    r->wt = wt;
    Resonators = plist_append(Resonators, r);
    Num_resonators++;
  }
}  /* init_resonators */

/*************
 *
 *   resonator_match_weight()
 *
 *************/

/* DOCUMENTATION
Try to match the given term against the installed resonators.  If
any resonator matches (first-match-wins), store that resonator's
weight in *wt_out and return TRUE.  Otherwise return FALSE and
leave *wt_out unchanged.  Wos semantics: every variable position
in the resonator pattern is an independent wildcard matching any
subterm.
*/

/* PUBLIC */
BOOL resonator_match_weight(Term t, double *wt_out)
{
  Plist p;
  for (p = Resonators; p; p = p->next) {
    struct resonator *r = p->v;
    if (match_resonator(r->pattern, t)) {
      if (wt_out)
        *wt_out = r->wt;
      Num_resonator_matches++;
      return TRUE;
    }
  }
  return FALSE;
}  /* resonator_match_weight */

/*************
 *
 *   number_of_resonators()
 *
 *************/

/* PUBLIC */
int number_of_resonators(void)
{
  return Num_resonators;
}  /* number_of_resonators */

/*************
 *
 *   number_of_resonator_matches()
 *
 *************/

/* PUBLIC */
int number_of_resonator_matches(void)
{
  return Num_resonator_matches;
}  /* number_of_resonator_matches */

/*************
 *
 *   apply_depth()
 *
 *************/

static
int apply_depth(Term t, Context subst)
{
  /* Iterative depth computation using explicit stack. */
  struct { Term node; int child; int depth; } stack[1000];
  int top = 0;
  int result = 0;

  if (VARIABLE(t))
    return term_depth(subst->terms[VARNUM(t)]);
  if (CONSTANT(t))
    return 0;

  stack[0].node = t;
  stack[0].child = 0;
  stack[0].depth = 0;

  while (top >= 0) {
    Term cur = stack[top].node;
    if (stack[top].child < ARITY(cur)) {
      int ci = stack[top].child;
      Term ch = ARG(cur, ci);
      stack[top].child++;
      if (VARIABLE(ch)) {
        int d = term_depth(subst->terms[VARNUM(ch)]);
        stack[top].depth = IMAX(stack[top].depth, d);
      }
      else if (CONSTANT(ch)) {
        /* depth 0 -- doesn't change max */
      }
      else {
        top++;
        stack[top].node = ch;
        stack[top].child = 0;
        stack[top].depth = 0;
      }
    }
    else {
      int my_depth = stack[top].depth + 1;
      top--;
      if (top >= 0) {
        stack[top].depth = IMAX(stack[top].depth, my_depth);
      }
      else {
        result = my_depth;
      }
    }
  }
  return result;
}  /* apply_depth */

/*************
 *
 *   weight_calc() -- mutually recursive with weight
 *
 *************/

static
double weight_calc(Term b, Context subst)
{
  /* Iterative postfix evaluation of the arithmetic expression tree.
     We use an operand stack for computed values and a traversal stack
     for pending nodes.  Operators are pushed with a marker so we know
     when to apply them after their operands are evaluated. */
  enum { EVAL_NODE, APPLY_BINARY, APPLY_NEG };
  struct { int op; int sn; Term node; } wstack[1000];
  double vstack[1000];
  int wtop = -1;
  int vtop = -1;

  /* Push initial node. */
  wtop++;
  wstack[wtop].op = EVAL_NODE;
  wstack[wtop].node = b;
  wstack[wtop].sn = 0;

  while (wtop >= 0) {
    int op = wstack[wtop].op;
    Term cur = wstack[wtop].node;
    int sn = wstack[wtop].sn;
    wtop--;

    if (op == APPLY_BINARY) {
      double v2 = vstack[vtop]; vtop--;
      double v1 = vstack[vtop]; vtop--;
      double result;
      if (sn == Sum_sn) result = v1 + v2;
      else if (sn == Prod_sn) result = v1 * v2;
      else if (sn == Div_sn) result = v1 / v2;
      else if (sn == Max_sn) result = IMAX((int)v1, (int)v2);
      else /* Min_sn */ result = IMIN((int)v1, (int)v2);
      vtop++; vstack[vtop] = result;
      continue;
    }
    if (op == APPLY_NEG) {
      vstack[vtop] = -vstack[vtop];
      continue;
    }

    /* op == EVAL_NODE */
    if (VARIABLE(cur)) {
      fatal_error("weight_calc, variable in rule");
    }
    else if (SYMNUM(cur) == Weight_sn) {
      Term b_prime = apply(ARG(cur,0), subst);
      Context subst2 = get_context();
      double wt = weight(b_prime, subst2);
      free_context(subst2);
      zap_term(b_prime);
      vtop++; vstack[vtop] = wt;
    }
    else if (SYMNUM(cur) == Sum_sn || SYMNUM(cur) == Prod_sn ||
             SYMNUM(cur) == Div_sn || SYMNUM(cur) == Max_sn ||
             SYMNUM(cur) == Min_sn) {
      /* Push: apply_op, then right child, then left child (so left evals first). */
      wtop++;
      wstack[wtop].op = APPLY_BINARY;
      wstack[wtop].sn = SYMNUM(cur);
      wstack[wtop].node = NULL;
      wtop++;
      wstack[wtop].op = EVAL_NODE;
      wstack[wtop].node = ARG(cur, 1);
      wstack[wtop].sn = 0;
      wtop++;
      wstack[wtop].op = EVAL_NODE;
      wstack[wtop].node = ARG(cur, 0);
      wstack[wtop].sn = 0;
    }
    else if (SYMNUM(cur) == Neg_sn) {
      wtop++;
      wstack[wtop].op = APPLY_NEG;
      wstack[wtop].sn = 0;
      wstack[wtop].node = NULL;
      wtop++;
      wstack[wtop].op = EVAL_NODE;
      wstack[wtop].node = ARG(cur, 0);
      wstack[wtop].sn = 0;
    }
    else if (SYMNUM(cur) == Depth_sn) {
      vtop++; vstack[vtop] = apply_depth(ARG(cur,0), subst);
    }
    else if (SYMNUM(cur) == Vars_sn) {
      Term b_prime = apply(ARG(cur,0), subst);
      int n = number_of_vars_in_term(b_prime);
      zap_term(b_prime);
      vtop++; vstack[vtop] = n;
    }
    else if (SYMNUM(cur) == Call_sn) {
      char *prog = term_symbol(ARG(cur,0));
      Term b_prime = apply(ARG(cur,1), subst);
      double x = call_weight(prog, b_prime);
      zap_term(b_prime);
      vtop++; vstack[vtop] = x;
    }
    else {
      double wt;
      if (term_to_number(cur, &wt))
        { vtop++; vstack[vtop] = wt; }
      else {
        fatal_error("weight_calc, bad rule");
      }
    }
  }
  return vstack[0];
}  /* weight_calc */

/*************
 *
 *   weight() -- mutually recursive with weight_calc
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
double weight(Term t, Context subst)
{
  /* Iterative term weighting using explicit stack. */
  struct { Term node; int child; double wt; } stack[1000];
  int top = -1;
  double result = 0;

  /* Handle top-level variable. */
  if (VARIABLE(t))
    return Variable_weight;

  /* Resonators take precedence over ordinary weight rules.  A
     resonator match yields a flat weight (no arithmetic RHS), and
     because Wos-matching uses no binding there is no substitution
     to undo. */
  {
    double rwt;
    if (resonator_match_weight(t, &rwt))
      return rwt;
  }

  /* Check if a rule matches the top-level term. */
  {
    Plist p;
    for (p = Rules; p; p = p->next) {
      Term rule = p->v;
      Term alpha = ARG(rule,0);
      Term beta  = ARG(rule,1);
      Trail tr = NULL;
      int anyvar_ctx[MAX_ANYVARS];
      int av_i;
      for (av_i = 0; av_i < MAX_ANYVARS; av_i++)
        anyvar_ctx[av_i] = -1;
      if (match_weight(ARG(alpha,0), subst, t, &tr, anyvar_ctx)) {
        double wt = weight_calc(beta, subst);
        undo_subst(tr);
        return wt;
      }
    }
  }

  if (CONSTANT(t)) {
    if (skolem_term(t) && Sk_constant_weight != 1)
      return Sk_constant_weight;
    else if (relation_symbol(SYMNUM(t)))
      return Prop_atom_weight;
    else
      return Constant_weight;
  }

  /* Complex term with no matching rule -- push onto stack. */
  top = 0;
  stack[0].node = t;
  stack[0].child = 0;
  stack[0].wt = 1;

  while (top >= 0) {
    Term cur = stack[top].node;

    if (stack[top].child >= ARITY(cur)) {
      /* This node is done. Pop and add weight to parent. */
      double my_wt = stack[top].wt;
      top--;
      if (top >= 0) {
        /* Check nest penalty on the previous child (the one that just finished). */
        /* The child index was already incremented, so the child that just
           finished is at child-1. But we handle nest penalty when pushing. */
        stack[top].wt += my_wt;
      }
      else {
        result = my_wt;
      }
      continue;
    }

    {
      int ci = stack[top].child;
      Term ch = ARG(cur, ci);
      stack[top].child++;

      /* Add nest penalty if applicable. */
      if (Nest_penalty != 0 &&
          ARITY(cur) <= 2 &&
          !VARIABLE(ch) &&
          SYMNUM(cur) == SYMNUM(ch))
        stack[top].wt += Nest_penalty;

      if (VARIABLE(ch)) {
        stack[top].wt += Variable_weight;
        continue;
      }

      /* Resonators take precedence over ordinary weight rules. */
      {
        double rwt;
        if (resonator_match_weight(ch, &rwt)) {
          stack[top].wt += rwt;
          continue;
        }
      }

      /* Check if a rule matches this child. */
      {
        Plist p;
        BOOL matched = FALSE;
        for (p = Rules; p; p = p->next) {
          Term rule = p->v;
          Term alpha = ARG(rule,0);
          Term beta  = ARG(rule,1);
          Trail tr = NULL;
          int anyvar_ctx[MAX_ANYVARS];
          int av_i;
          for (av_i = 0; av_i < MAX_ANYVARS; av_i++)
            anyvar_ctx[av_i] = -1;
          if (match_weight(ARG(alpha,0), subst, ch, &tr, anyvar_ctx)) {
            double wt = weight_calc(beta, subst);
            undo_subst(tr);
            stack[top].wt += wt;
            matched = TRUE;
            break;
          }
        }
        if (matched)
          continue;
      }

      if (CONSTANT(ch)) {
        if (skolem_term(ch) && Sk_constant_weight != 1)
          stack[top].wt += Sk_constant_weight;
        else if (relation_symbol(SYMNUM(ch)))
          stack[top].wt += Prop_atom_weight;
        else
          stack[top].wt += Constant_weight;
      }
      else {
        /* Complex child with no matching rule -- push. */
        top++;
        stack[top].node = ch;
        stack[top].child = 0;
        stack[top].wt = 1;
      }
    }
  }
  return result;
}  /* weight */

/*************
 *
 *   clause_weight()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
double clause_weight(Literals lits)
{
  double wt;
  
  if (!Not_rules && !Or_rules) {
    /* There are no rules for OR or NOT, so we don't need to construct a
       Term representation of the clause. */
    Literals lit;
    wt = 0;
    for (lit = lits; lit; lit = lit->next) {
      Context subst = get_context();
      wt += weight(lit->atom, subst);
      free_context(subst);
    }
    wt += (negative_literals(lits) * Not_weight);
    wt += ((number_of_literals(lits)-1) * Or_weight);
  }
  else {
    /* Build a temporary Term representation of the clause and weigh that.
       This is done in case there are weight rules for OR or NOT. */
    Term temp = lits_to_term(lits);
    Context subst = get_context();
    wt = weight(temp, subst);
    free_context(subst);
    free_lits_to_term(temp);

    /* If there are no Not_rules, we have already added one for each not;
       so we undo that and add the correct amount.  Same for Or_rules. */
       
    if (!Not_rules)
      wt += (negative_literals(lits) * (Not_weight - 1));
    if (!Or_rules)
      wt += ((number_of_literals(lits) - 1) * (Or_weight - 1));
  }

  if (Depth_penalty != 0)
    wt += Depth_penalty * literals_depth(lits);

  if (Var_penalty != 0)
    wt += Var_penalty * number_of_variables(lits);
 
  if (Complexity != 0)
    wt += Complexity * (1 - clause_complexity(lits, 4, 0));

  return wt;

}  /* clause_weight */
