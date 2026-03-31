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

#include "giv_select.h"
#include "semantics.h"
#include "../ladr/avltree.h"
#include "../ladr/clause_eval.h"

/* Private definitions and types */

enum { GS_ORDER_WEIGHT,
       GS_ORDER_AGE,
       GS_ORDER_HINT_AGE,
       GS_ORDER_RANDOM
};  /* order */

typedef struct giv_select *Giv_select;

struct giv_select {
  char         *name;
  int          order;
  Clause_eval  property;
  int          part;
  int          selected;
  Ordertype (*compare) (void *, void *);  /* function for ordering idx */
  Avl_node idx;          /* index of clauses (binary search (AVL) tree) */
};  /* struct giv_select */

typedef struct select_state *Select_state;

/* Static variables */

static struct select_state {
  Plist selectors;    /* list of Giv_select */
  int occurrences;    /* occurrences of clauses in selectors */
  Plist current;      /* for ratio state */
  int  count;         /* for ratio state */
  int  cycle_size;
} High, Low; /* The two lists of selectors and their positions */

static BOOL Rule_needs_semantics = FALSE;
static int Sos_size = 0;
static double Low_water_keep = INT_MAX;
static double Low_water_displace = INT_MAX;
static int Sos_deleted = 0;
static int Sos_displaced = 0;

static BOOL Debug = FALSE;

/*
 * memory management
 */

#define PTRS_GIV_SELECT CEILING(sizeof(struct giv_select), BYTES_POINTER)
static unsigned Giv_select_gets, Giv_select_frees;

/*************
 *
 *   Giv_select get_giv_select()
 *
 *************/

static
Giv_select get_giv_select(void)
{
  Giv_select p = get_cmem(PTRS_GIV_SELECT);
  Giv_select_gets++;
  return(p);
}  /* get_giv_select */

/*************
 *
 *    free_giv_select()
 *
 *************/

static
void free_giv_select(Giv_select p)
{
  free_mem(p, PTRS_GIV_SELECT);
  Giv_select_frees++;
}  /* free_giv_select */

/*************
 *
 *   current_cycle_size()
 *
 *************/

static
int current_cycle_size(Select_state s)
{
  int sum = 0;
  Plist p;
  for (p = s->selectors; p; p = p->next) {
    Giv_select gs = p->v;
    if (avl_size(gs->idx) > 0)
      sum += gs->part;
  }
  return sum;
}  /* current_cycle_size */

/*************
 *
 *   reset_selector_indexes()
 *
 *   Clear all selector AVL trees and counters.  Used by checkpoint
 *   restore to discard stale entries before reinserting from checkpoint.
 *
 *************/

/* PUBLIC */
void reset_selector_indexes(void)
{
  Plist p;
  for (p = High.selectors; p; p = p->next) {
    Giv_select gs = p->v;
    gs->idx = NULL;  /* leak old AVL nodes (small, one-time) */
    gs->selected = 0;
  }
  High.occurrences = 0;
  for (p = Low.selectors; p; p = p->next) {
    Giv_select gs = p->v;
    gs->idx = NULL;
    gs->selected = 0;
  }
  Low.occurrences = 0;
  Sos_size = 0;
}  /* reset_selector_indexes */

/*************
 *
 *   init_giv_select()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_giv_select(Plist rules)
{
  Plist p;

  for (p = rules; p; p = p->next) {
    Term t = p->v;
    int n = 0;
    Term order_term;
    Term property_term;
    Giv_select gs;
    if (!is_term(t, "=", 2) ||
	!is_term(ARG(t,0), "part", 4) ||
	!CONSTANT(ARG(ARG(t,0),0)) ||
	!(is_constant(ARG(ARG(t,0),1), "high") ||
	  is_constant(ARG(ARG(t,0),1), "low")) ||
	!((n = natural_constant_term(ARG(t,1))) > 0))
      fatal_error("Given selection rule must be: "
		  "part(<name>,high|low,age|wt|random,<property>)=<n>");

    order_term = ARG(ARG(t,0),2);
    property_term = ARG(ARG(t,0),3);
    gs = get_giv_select();
    
    if (is_constant(ARG(ARG(t,0),1), "high")) {
      High.selectors = plist_append(High.selectors, gs);
      if (n > INT_MAX - High.cycle_size)
	High.cycle_size = INT_MAX;  /* saturate to avoid overflow */
      else
	High.cycle_size += n;
    }
    else {
      Low.selectors  = plist_append(Low.selectors,  gs);
      if (n > INT_MAX - Low.cycle_size)
	Low.cycle_size = INT_MAX;  /* saturate to avoid overflow */
      else
	Low.cycle_size += n;
    }

    gs->name = term_symbol(ARG(ARG(t,0),0));
    gs->part = n;
    if (is_constant(order_term,"weight")) {
      gs->order = GS_ORDER_WEIGHT;
      gs->compare = (Ordertype (*) (void *, void *)) cl_wt_id_compare;
    }
    else if (is_constant(order_term,"age")) {
      gs->order = GS_ORDER_AGE;
      gs->compare = (Ordertype (*) (void *, void *)) cl_id_compare;
    }
    else if (is_constant(order_term,"hint_age")) {
      gs->order = GS_ORDER_HINT_AGE;
      gs->compare = (Ordertype (*) (void *, void *)) cl_hint_id_compare;
    }
    else if (is_constant(order_term,"random")) {
      gs->order = GS_ORDER_RANDOM;
      gs->compare = (Ordertype (*) (void *, void *)) cl_id_compare;
    }
    else
      fatal_error("Given selection order must be weight, age, hint_age, or random.");
    gs->property = compile_clause_eval_rule(property_term);
    if (gs->property == NULL)
      fatal_error("Error in clause-property expression of given selection rule");
    else if (rule_contains_semantics(gs->property))
      Rule_needs_semantics = TRUE;
  }
  High.current = High.selectors;
  Low.current = Low.selectors;
}  /* init_giv_select */

/*************
 *
 *   update_selectors()
 *
 *************/

static
void update_selectors(Topform c, BOOL insert)
{
  BOOL matched = FALSE;
  Plist p;
  for (p = High.selectors; p; p = p->next) {
    Giv_select gs = p->v;
    if (eval_clause_in_rule(c, gs->property)) {
      matched = TRUE;
      if (insert) {
	gs->idx = avl_insert(gs->idx, c, gs->compare);
	High.occurrences++;
      }
      else {
	gs->idx = avl_delete(gs->idx, c, gs->compare);
	High.occurrences--;
      }
    }
  }
  /* If it is high-priority, don't let it also be low priority. */
  if (!matched) {
    for (p = Low.selectors; p; p = p->next) {
      Giv_select gs = p->v;
      if (eval_clause_in_rule(c, gs->property)) {
	matched = TRUE;
	if (insert) {
	  gs->idx = avl_insert(gs->idx, c, gs->compare);
	  Low.occurrences++;
	}
	else {
	  gs->idx = avl_delete(gs->idx, c, gs->compare);
	  Low.occurrences--;
	}
      }
    }
  }
  if (!matched) {
    static BOOL Already_warned = FALSE;

    if (!Already_warned) {
      fprintf(stderr, "\n\nWARNING: one or more kept clauses do not match "
	     "any given_selection rules (see output).\n\n");
      printf("\nWARNING: the following clause does not match "
	     "any given_selection rules.\n"
	     "This message will not be repeated.\n");
      f_clause(c);
      Already_warned = TRUE;
    }
  }
}  /* update_selectors */

/*************
 *
 *   insert_into_sos2()
 *
 *************/

/* DOCUMENTATION
This routine appends a clause to the sos list and updates
the (private) index for extracting sos clauses.
*/

/* PUBLIC */
void insert_into_sos2(Topform c, Clist sos)
{
  if (Rule_needs_semantics)
    set_semantics(c);  /* in case not yet evaluated */

  update_selectors(c, TRUE);
  clist_append(c, sos);
  Sos_size++;
}  /* insert_into_sos2 */

/*************
 *
 *   remove_from_sos2()
 *
 *************/

/* DOCUMENTATION
This routine removes a clause from the sos list and updates
the index for extracting the lightest and heaviest clauses.
*/

/* PUBLIC */
void remove_from_sos2(Topform c, Clist sos)
{
  update_selectors(c, FALSE);
  clist_remove(c, sos);
  Sos_size--;
}  /* remove_from_sos2 */

/*************
 *
 *   bulk_insert_into_sos2()
 *
 *   Bulk-insert all clauses from a Clist into the SOS selector AVL trees.
 *   Uses sorted-array AVL construction: O(n log n) for qsort + O(n) for
 *   tree build, vs O(n log n) for n individual AVL inserts but with much
 *   better constant factor (no rotations, no per-insert rule evaluation
 *   overhead via batching).
 *
 *************/

/* qsort comparator wrapper — uses a static function pointer */
static Ordertype (*Bulk_compare)(void *, void *);

static int bulk_qsort_compare(const void *a, const void *b)
{
  Ordertype r = Bulk_compare(*(void **)a, *(void **)b);
  return (r == LESS_THAN) ? -1 : (r == GREATER_THAN) ? 1 : 0;
}

/* PUBLIC */
void bulk_insert_into_sos2(Clist sos)
{
  int n, i;
  void **all;
  Clist_pos cp;
  Plist p;

  n = sos->length;
  if (n == 0) return;

  /* Build array of all clauses */
  all = (void **) safe_malloc(n * sizeof(void *));
  i = 0;
  for (cp = sos->first; cp != NULL; cp = cp->next)
    all[i++] = cp->c;

  /* For each selector, filter matching clauses, sort, build AVL */
  {
    void **matched = (void **) safe_malloc(n * sizeof(void *));
    Select_state states[2];
    int si;

    states[0] = &High;
    states[1] = &Low;

    for (si = 0; si < 2; si++) {
      for (p = states[si]->selectors; p; p = p->next) {
        Giv_select gs = p->v;
        int nm = 0;

        /* Collect clauses matching this selector's property */
        for (i = 0; i < n; i++) {
          if (eval_clause_in_rule((Topform) all[i], gs->property))
            matched[nm++] = all[i];
        }

        if (nm > 0) {
          /* Sort by selector's compare function */
          Bulk_compare = gs->compare;
          qsort(matched, nm, sizeof(void *), bulk_qsort_compare);

          /* Build balanced AVL tree from sorted array */
          gs->idx = avl_build_sorted(matched, nm);

          states[si]->occurrences += nm;
        }
      }
    }
    safe_free(matched);
  }

  Sos_size = n;
  safe_free(all);
}  /* bulk_insert_into_sos2 */

/*************
 *
 *   next_selector()
 *
 *************/

static
Giv_select next_selector(Select_state s)
{
  if (s->selectors == NULL)
    return NULL;
  else {
    Plist start = s->current;
    Giv_select gs = s->current->v;
    while (gs->idx == NULL || s->count >= gs->part) {
      s->current = s->current->next;
      if (!s->current)
	s->current = s->selectors;
      gs = s->current->v;
      s->count = 0;
      if (s->current == start)
	break;  /* we're back to the start */
    }
    if (gs->idx == NULL)
      return NULL;
    else {
      s->count++;  /* for next call */
      return gs;
    }
  }
}  /* next_selector */

/*************
 *
 *   givens_available()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL givens_available(void)
{
  return (High.occurrences > 0 || Low.occurrences > 0);
}  /* givens_available */

/*************
 *
 *   get_given_clause2()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Topform get_given_clause2(Clist sos, int num_given,
			 Prover_options opt, char **type)
{
  Topform giv;
  Giv_select gs = next_selector(&High);
  if (gs == NULL)
    gs = next_selector(&Low);
  if (gs == NULL)
    return NULL;  /* no clauses are available */
    
  if (gs->order == GS_ORDER_RANDOM) {
    int n = avl_size(gs->idx);
    int i = (rand() % n) + 1;
    giv = avl_nth_item(gs->idx, i);
  }
  else
    giv = avl_smallest(gs->idx);

  *type = gs->name;
  gs->selected += 1;

  remove_from_sos2(giv, sos);
  return giv;
}  /* get_given_clause2 */

/*************
 *
 *   iterations_to_selection()
 *
 *************/

static
double iterations_to_selection(int part, int n,
			       int cycle_size, int occurrences, int sos_size)
{
  /* This approximates the number of iterations (of given selection) until
     the n-th clause in the selector is selected.  Simplyfying assumptions:
       1. High-priority selectors are empty.
       2. Other selectors don't become empty.
       3. No clauses are inserted before the n-th clause.  (unrealistic)
   */
  double x = n * ((double) cycle_size / part);
  return x / ((double) occurrences / sos_size);
}  /* iterations_to_selection */

/*************
 *
 *   least_iters_to_selection()
 *
 *************/

static
double least_iters_to_selection(Topform c, Select_state s, Plist ignore)
{
  Plist p;
  double least = INT_MAX;  /* where is DOUBLE_MAX?? */
  for (p = s->selectors; p; p = p->next) {
    if (p != ignore) {
      Giv_select gs = p->v;
      if (Rule_needs_semantics)
	set_semantics(c);  /* in case not yet evaluated */

      if (eval_clause_in_rule(c, gs->property)) {
	int n, cycle;
	double x;
	if (gs->order == GS_ORDER_AGE && c->id == INT_MAX)
	  n = avl_size(gs->idx) + 1;
	else
	  n = avl_place(gs->idx, c, gs->compare);
	cycle = current_cycle_size(s);
	x = iterations_to_selection(gs->part, n, cycle,
				    s->occurrences, Sos_size);
	if (Debug)
	  printf("%s(%.3f),cycle=%d,part=%d,place=%d,size=%d,iters=%.2f\n",
		 gs->name, c->weight, cycle, gs->part, n,avl_size(gs->idx),x);
	least = (x < least ? x : least);
      }
    }
  }
  return least;
}  /* least_iters_to_selection */

/***************
 *
 *   sos_keep2()
 *
 **************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL sos_keep2(Topform c, Clist sos, Prover_options opt)
{
  int keep_factor = parm(opt->sos_keep_factor);
  int sos_size = clist_length(sos);
  int sos_limit = (parm(opt->sos_limit)== -1 ? INT_MAX : parm(opt->sos_limit));
  BOOL keep;
  if (sos_size < sos_limit / keep_factor)
    keep = TRUE;
  else {
    int iters;
    c->id = INT_MAX;
    iters = least_iters_to_selection(c, &Low, NULL);
    if (Debug)
      printf("iters=%d, wt=%.3f\n", iters, c->weight);
    if (iters < sos_limit / keep_factor)
      keep = TRUE;
    else {
      if (c->weight < Low_water_keep) {
	Low_water_keep = c->weight;
	if (!flag(opt->quiet)) {
	  printf("\nLow Water (keep): wt=%.3f, iters=%d\n", c->weight, iters);
	  if (stringparm(opt->stats, "all"))
	    selector_report();
	  fflush(stdout);
	}
      }
      Sos_deleted++;
      keep = FALSE;  /* delete clause */
    }
    c->id = 0;
  }
  return keep;
}  /* sos_keep2 */

/*************
 *
 *   worst_clause_of_priority_group()
 *
 *************/

static
Topform worst_clause_of_priority_group(Select_state ss)
{
  Topform worst = NULL; /* worst clause (with most iterations_to_selection)  */
  double max = 0.0;     /* iterations_to_selection for current worst clause  */
  Plist p;
  for (p = ss->selectors; p; p = p->next) {
    Giv_select gs = p->v;
    if (gs->idx) {
      Topform c = avl_largest(gs->idx);
      double x = iterations_to_selection(gs->part, avl_size(gs->idx),
					 current_cycle_size(ss),
					 ss->occurrences,
					 Sos_size);

      /* If that clause occurs in other selectors,
         find the lowest iterations_to_selection. */

      double y = least_iters_to_selection(c, ss, p);  /* ignore p */

      double least = (x < y ? x : y);

      if (least > max) {
	max = least;
	worst = c;
      }
    }
  }
  return worst;
}  /* worst_clause_of_priority_group */

/*************
 *
 *   worst_clause()
 *
 *************/

static
Topform worst_clause(void)
{
  Topform worst = worst_clause_of_priority_group(&Low);
  if (worst == NULL) {
    worst = worst_clause_of_priority_group(&High);
    if (worst)
      printf("\nWARNING: worst clause (id=%llu, wt=%.3f) has high priority.\n",
	     worst->id, worst->weight);
  }
  return worst;
}  /* worst_clause */

/*************
 *
 *   sos_displace2() - delete the worst sos clause
 *
 *************/

/* DOCUMENTATION
Disable the "worst" clause.
*/

/* PUBLIC */
void sos_displace2(void (*disable_proc) (Topform), BOOL quiet)
{
  Topform worst = worst_clause();
  if (worst == NULL) {
    selector_report();
    fatal_error("sos_displace2, cannot find worst clause");
  }
  else {
    if (worst->weight < Low_water_displace) {
      Low_water_displace = worst->weight;
      if (!quiet) {
	printf("\nLow Water (displace): id=%llu, wt=%.3f\n",
	       worst->id, worst->weight);
	fflush(stdout);
      }
    }
    Sos_displaced++;
    disable_proc(worst);
  }
}  /* sos_displace2 */

/*************
 *
 *   zap_given_selectors()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void zap_given_selectors(void)
{
  Plist p;
  for (p = High.selectors; p; p = p->next) {
    Giv_select gs = p->v;
    zap_clause_eval_rule(gs->property);
    avl_zap(gs->idx);
    free_giv_select(gs);
  }
  zap_plist(High.selectors);  /* shallow */
  for (p = Low.selectors; p; p = p->next) {
    Giv_select gs = p->v;
    zap_clause_eval_rule(gs->property);
    avl_zap(gs->idx);
  }
  zap_plist(Low.selectors);  /* shallow */
}  /* zap_given_selectors */

/*************
 *
 *   get_low_selector_state()
 *
 *************/

/* PUBLIC */
void get_low_selector_state(const char **name, int *count)
{
  if (Low.current) {
    Giv_select gs = Low.current->v;
    *name = gs->name;
    *count = Low.count;
  }
  else {
    *name = "";
    *count = 0;
  }
}  /* get_low_selector_state */

/*************
 *
 *   set_low_selector_state()
 *
 *************/

/* PUBLIC */
void set_low_selector_state(const char *name, int count)
{
  Plist p;
  for (p = Low.selectors; p; p = p->next) {
    Giv_select gs = p->v;
    if (strcmp(gs->name, name) == 0) {
      Low.current = p;
      Low.count = count;
      return;
    }
  }
  /* Name not found — leave at default (first selector, count=0). */
}  /* set_low_selector_state */

/*************
 *
 *   get_high_selector_state()
 *
 *************/

/* PUBLIC */
void get_high_selector_state(const char **name, int *count)
{
  if (High.current) {
    Giv_select gs = High.current->v;
    *name = gs->name;
    *count = High.count;
  }
  else {
    *name = "";
    *count = 0;
  }
}  /* get_high_selector_state */

/*************
 *
 *   set_high_selector_state()
 *
 *************/

/* PUBLIC */
void set_high_selector_state(const char *name, int count)
{
  Plist p;
  for (p = High.selectors; p; p = p->next) {
    Giv_select gs = p->v;
    if (strcmp(gs->name, name) == 0) {
      High.current = p;
      High.count = count;
      return;
    }
  }
}  /* set_high_selector_state */

/*************
 *
 *   selector_report()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void selector_report(void)
{
  Plist p;
  print_separator(stdout, "SELECTOR REPORT", TRUE);
  printf("Sos_deleted=%d, Sos_displaced=%d, Sos_size=%d\n",
	 Sos_deleted, Sos_displaced, Sos_size);
  printf("%10s %10s %10s %10s %10s %10s\n",
	 "SELECTOR", "PART", "PRIORITY", "ORDER", "SIZE", "SELECTED");
  for (p = High.selectors; p; p = p->next) {
    Giv_select gs = p->v;
    char *s1, *s2;
    s1 = "high";
    switch (gs->order) {
    case GS_ORDER_WEIGHT: s2 = "weight"; break;
    case GS_ORDER_AGE: s2 = "age"; break;
    case GS_ORDER_HINT_AGE: s2 = "hint_age"; break;
    case GS_ORDER_RANDOM: s2 = "random"; break;
    default: s2 = "???"; break;
    }
    printf("%10s %10d %10s %10s %10d %10d\n",
	   gs->name, gs->part, s1, s2, avl_size(gs->idx), gs->selected);
  }
  for (p = Low.selectors; p; p = p->next) {
    Giv_select gs = p->v;
    char *s1, *s2;
    s1 = "low";
    switch (gs->order) {
    case GS_ORDER_WEIGHT: s2 = "weight"; break;
    case GS_ORDER_AGE: s2 = "age"; break;
    case GS_ORDER_HINT_AGE: s2 = "hint_age"; break;
    case GS_ORDER_RANDOM: s2 = "random"; break;
    default: s2 = "???"; break;
    }
    printf("%10s %10d %10s %10s %10d %10d\n",
	   gs->name, gs->part, s1, s2, avl_size(gs->idx), gs->selected);
  }
  print_separator(stdout, "end of selector report", FALSE);  
  fflush(stdout);
}  /* selector_report */

/*************
 *
 *   selector_rule_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Term selector_rule_term(char *name, char *priority,
			char *order, char *rule, int part)
{
  Term left =  get_rigid_term("part", 4);
  Term right = nat_to_term(part);
  ARG(left,0) = get_rigid_term(name, 0);
  ARG(left,1) = get_rigid_term(priority, 0);
  ARG(left,2) = get_rigid_term(order, 0);
  ARG(left,3) = get_rigid_term(rule, 0);
  return build_binary_term_safe("=", left, right);
}  /* selector_rule_term */

/*************
 *
 *   selector_rules_from_options()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist selector_rules_from_options(Prover_options opt)
{
  Plist p = NULL;

  if (flag(opt->input_sos_first)) {
    p = plist_append(p, selector_rule_term("I", "high", "age",
					   "initial", INT_MAX));
  }

  if (parm(opt->hints_part) == INT_MAX) {
    p = plist_append(p, selector_rule_term("H", "high", "weight",
					   "hint", 1));
  }
  else if (parm(opt->hints_part) > 0) {
    p = plist_append(p, selector_rule_term("H", "low", "weight",
					   "hint", parm(opt->hints_part)));
  }

  if (parm(opt->age_part) > 0) {
    p = plist_append(p, selector_rule_term("A", "low", "age",
					   "all", parm(opt->age_part)));
  }
  if (parm(opt->false_part) > 0) {
    p = plist_append(p, selector_rule_term("F", "low", "weight",
					   "false", parm(opt->false_part)));
  }
  if (parm(opt->true_part) > 0) {
    p = plist_append(p, selector_rule_term("T", "low", "weight",
					   "true", parm(opt->true_part)));
  }
  if (parm(opt->weight_part) > 0) {
    p = plist_append(p, selector_rule_term("W", "low", "weight",
					   "all", parm(opt->weight_part)));
  }
  if (parm(opt->random_part) > 0) {
    p = plist_append(p, selector_rule_term("R", "low", "random",
					   "all", parm(opt->random_part)));
  }

  return p;
}  /* selector_rules_from_options */

