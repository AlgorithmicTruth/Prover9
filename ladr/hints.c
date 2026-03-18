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

#include "hints.h"

/* Private definitions and types */

static Lindex Hints_idx = NULL;       /* FPA index for hints */
static Clist Redundant_hints = NULL;  /* list of hints not indexed */
static Mindex Back_demod_idx;        /* to index hints for back demodulation */
static int Bsub_wt_attr;
static BOOL Back_demod_hints;
static BOOL Collect_labels;

/* pointer to procedure for demodulating hints (when back demod hints) */

static void (*Demod_proc) (Topform, int, int, BOOL, BOOL);

/* stats */

static int Hint_id_count = 0;
static int Active_hints_count = 0;
static int Redundant_hints_count = 0;

/* given-clause counter for hint expiry */

static unsigned long long Current_given_for_hints = 0;

/* Re-match delta histogram: delta = current_given - last_matched_given.
   Only recorded on 2nd+ match (weight > 0 before increment). */

#define DELTA_BUCKETS 16
static int Delta_bucket[DELTA_BUCKETS];  /* initialized to 0 */
static int Delta_total = 0;
static unsigned long long Delta_min = 0;
static unsigned long long Delta_max = 0;
static double Delta_sum = 0;

/*************
 *
 *   init_hints()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_hints(Uniftype utype,
		int bsub_wt_attr,
		BOOL collect_labels,
		BOOL back_demod_hints,
		int fpa_depth,
		void (*demod_proc) (Topform, int, int, BOOL, BOOL))
{
  Bsub_wt_attr = bsub_wt_attr;
  Collect_labels = collect_labels;
  Back_demod_hints = back_demod_hints;
  Demod_proc = demod_proc;
  Hints_idx = lindex_init(FPA, utype, fpa_depth, FPA, utype, fpa_depth);
  if (Back_demod_hints)
    Back_demod_idx = mindex_init(FPA, utype, fpa_depth);
  Redundant_hints = clist_init("redundant_hints");
}  /* init_hints */

/*************
 *
 *   done_with_hints()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void done_with_hints(void)
{
  if (!lindex_empty(Hints_idx) ||
      !clist_empty(Redundant_hints))
    printf("ERROR: Hints index not empty!\n");
  lindex_destroy(Hints_idx);
  if (Back_demod_hints)
    mindex_destroy(Back_demod_idx);
  Hints_idx = NULL;
  clist_free(Redundant_hints);
  Redundant_hints = NULL;
}  /* done_with_hints */

/*************
 *
 *   redundant_hints()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int redundant_hints(void)
{
  return clist_length(Redundant_hints);
}  /* redundant_hints */

/*************
 *
 *   find_equivalent_hint()
 *
 *************/

static
Topform find_equivalent_hint(Topform c, Lindex idx)
{
  Topform equiv_hint = NULL;
  Plist subsumees = back_subsume(c, idx);
  Plist p;
  for (p = subsumees; p && equiv_hint == NULL; p = p->next) {
    if (subsumes(p->v, c))
      equiv_hint = p->v;
  }
  zap_plist(subsumees);
  return equiv_hint;
}  /* find_equivalent_hint */

/*************
 *
 *   find_matching_hint()
 *
 *   Return the first equivalent hint;  if none, return the last
 *   subsumed hint.
 *
 *   "First" and "last" refer to the order returned by the index,
 *   which is not necessarily the order in which the hints were
 *   inserted into the index.  In fact, it is likely that the
 *   clauses are returned in the reverse order.
 *
 *************/

static
Topform find_matching_hint(Topform c, Lindex idx)
{
  Topform hint = NULL;
  Plist subsumees = back_subsume(c, idx);
  Plist p;
  BOOL equivalent = FALSE;
  for (p = subsumees; p && !equivalent; p = p->next) {
    /* printf("subsumee: "); f_clause(p->v); */
    hint = p->v;
    if (subsumes(p->v, c))
      equivalent = TRUE;
  }
  zap_plist(subsumees);
  return hint;
}  /* find_matching_hint */

/*************
 *
 *   index_hint()
 *
 *************/

/* DOCUMENTATION
Index a clause C as a hint (make sure to call init_hints first).
If the clause is equivalent to a previously indexed hint H, any
labels on C are copied to H, and C is not indexed.
*/

/* PUBLIC */
/*************
 *
 *   hint_contains_anyconst() -- check if a hint has generic _AnyConst
 *
 *************/

static BOOL hint_contains_anyconst(Topform c)
{
  Literals lit;
  int sn = any_const_sn(0);  /* symnum for _AnyConst */
  for (lit = c->literals; lit; lit = lit->next) {
    if (lit->atom != NULL && symbol_in_term(sn, lit->atom))
      return TRUE;
  }
  return FALSE;
}  /* hint_contains_anyconst */

void index_hint(Topform c)
{
  Topform h;

  /* Disable _AnyConst matching during redundancy check so that
     hints with _AnyConst are not marked redundant vs concrete hints. */
  AnyConstsEnabled = FALSE;
  h = find_equivalent_hint(c, Hints_idx);
  AnyConstsEnabled = TRUE;

  c->weight = 0;  /* this is used in hints degradation to count matches */
  if (h != NULL) {
    /* copy any bsub_hint_wt attrs from rundundant hint to the indexed hint */
    h->attributes = copy_int_attribute(c->attributes, h->attributes,
				       Bsub_wt_attr);
    if (Collect_labels) {
      /* copy any labels from rundundant hint to the indexed hint */
      h->attributes = copy_string_attribute(c->attributes, h->attributes,
					    label_att());
    }
    clist_append(c, Redundant_hints);
    Redundant_hints_count++;
    /*
    printf("redundant hint: "); f_clause(c);
    printf("      original: "); f_clause(h);
    */
  }
  else {
    Active_hints_count++;
    Hint_id_count++;
    /* Keep the original id on re-index (back-demod).  Reassigning the
       id would change the hint_age key used by AVL trees in the
       hint_age given selection rule, making avl_delete unable to find
       clauses that were inserted under the old id.  (BV 2016-jun-17) */
    if (c->id == 0)
      c->id = Hint_id_count;
    lindex_update(Hints_idx, c, INSERT);
    if (Back_demod_hints) {
      /* Do not index hints containing generic _AnyConst for back-demod.
         Back-demodulating _AnyConst would be unsound. */
      if (MATCH_HINTS_ANYCONST && hint_contains_anyconst(c))
        ;  /* skip back-demod indexing */
      else
        index_clause_back_demod(c, Back_demod_idx, INSERT);
    }
  }
}  /* index_hint */

/*************
 *
 *   unindex_hint()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void unindex_hint(Topform c)
{
  if (clist_member(c, Redundant_hints)) {
    clist_remove(c, Redundant_hints);
    Redundant_hints_count--;
  }
  else {
    lindex_update(Hints_idx, c, DELETE);
    if (Back_demod_hints)
      index_clause_back_demod(c, Back_demod_idx, DELETE);
    Active_hints_count--;
  }
}  /* unindex_hint */

/*************
 *
 *   adjust_weight_with_hints()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void adjust_weight_with_hints(Topform c,
			      BOOL degrade,
			      BOOL breadth_first_hints)
{
  Topform hint = find_matching_hint(c, Hints_idx);

  if (hint == NULL &&
      unit_clause(c->literals) &&
      eq_term(c->literals->atom) &&
      !oriented_eq(c->literals->atom)) {

    /* Try to find a hint that matches the flipped equality. */

    Term save_atom = c->literals->atom;
    c->literals->atom = top_flip(save_atom);
    hint = find_matching_hint(c, Hints_idx);
    zap_top_flip(c->literals->atom);
    c->literals->atom = save_atom;
    if (hint != NULL)
      c->attributes = set_string_attribute(c->attributes, label_att(),
					   "flip_matches_hint");
  }

  if (hint != NULL) {

    int bsub_wt = get_int_attribute(hint->attributes, Bsub_wt_attr, 1);

    if (bsub_wt != INT_MAX)
      c->weight = bsub_wt;
    else if (breadth_first_hints)
      c->weight = 0;

    /* If the hint has label attributes, copy them to the clause. */
    
    {
      int i = 0;
      char *s = get_string_attribute(hint->attributes, label_att(), ++i);
      while (s) {
	if (!string_attribute_member(c->attributes, label_att(), s))
	  c->attributes = set_string_attribute(c->attributes, label_att(), s);
	s = get_string_attribute(hint->attributes, label_att(), ++i);
      }
    }

    /* Veroff's hint degradation strategy. */

    if (degrade) {
      /* for now, add 1000 for each previous match */
      int i;
      for (i = 0; i < hint->weight; i++) 
	c->weight = c->weight + 1000;
    }
    c->matching_hint = hint;
    /* If/when c is eventually kept, the hint will have its weight
       field incremented in case hint degradation is being used. */
  }
}  /* adjust_weight_with_hints */

/*************
 *
 *   keep_hint_matcher()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void keep_hint_matcher(Topform c)
{
  Topform hint = c->matching_hint;

  /* Record re-match delta (only when hint was previously matched) */
  if (hint->weight > 0 && hint->last_matched_given > 0) {
    unsigned long long delta = Current_given_for_hints - hint->last_matched_given;
    int bucket;

    if (delta <= 500)       bucket = 0;
    else if (delta <= 1000) bucket = 1;
    else if (delta <= 1500) bucket = 2;
    else if (delta <= 2000) bucket = 3;
    else if (delta <= 2500) bucket = 4;
    else if (delta <= 3000) bucket = 5;
    else if (delta <= 3500) bucket = 6;
    else if (delta <= 4000) bucket = 7;
    else if (delta <= 4500) bucket = 8;
    else if (delta <= 5000) bucket = 9;
    else if (delta <= 5500) bucket = 10;
    else if (delta <= 6000) bucket = 11;
    else if (delta <= 6500) bucket = 12;
    else if (delta <= 7000) bucket = 13;
    else if (delta <= 7500) bucket = 14;
    else                    bucket = 15;

    Delta_bucket[bucket]++;
    Delta_total++;
    Delta_sum += (double) delta;
    if (Delta_total == 1 || delta < Delta_min) Delta_min = delta;
    if (delta > Delta_max) Delta_max = delta;
  }

  hint->weight++;
  hint->last_matched_given = Current_given_for_hints;
}  /* keep_hint_matcher */

/*************
 *
 *   back_demod_hints()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void back_demod_hints(Topform demod, int type, BOOL lex_order_vars)
{
  if (Back_demod_hints) {
    Plist rewritables = back_demod_indexed(demod, type, Back_demod_idx,
					   lex_order_vars);
    Plist p;
    for (p = rewritables; p; p = p->next) {
      Topform hint = p->v;
      /* printf("\nBEFORE: "); f_clause(hint); */
      unindex_hint(hint);
      (*Demod_proc)(hint, 1000, 1000, FALSE, lex_order_vars);

      orient_equalities(hint, TRUE);
      simplify_literals2(hint);
      merge_literals(hint);
      renumber_variables(hint, MAX_VARS);

      /* printf("AFTER : "); f_clause(hint); */
      index_hint(hint);
      hint->weight = 0;  /* reset count of number of matches */
    }
  }
}  /* back_demod_hints */

/*************
 *
 *   set_hints_given_count()
 *
 *************/

/* PUBLIC */
void set_hints_given_count(unsigned long long n)
{
  Current_given_for_hints = n;
}  /* set_hints_given_count */

/*************
 *
 *   expire_old_hints()
 *
 *   Remove hints that were matched but not recently.
 *   Never-matched hints (weight == 0) are kept.
 *   Returns the number of expired hints.
 *
 *************/

/* PUBLIC */
int expire_old_hints(unsigned long long current_given,
		     unsigned long long expiry_distance,
		     int min_matches,
		     Clist hint_list)
{
  Plist to_expire = NULL;
  Clist_pos p;
  int expired_count = 0;
  Plist q;

  /* Pass 1: collect expired hints */
  for (p = hint_list->first; p; p = p->next) {
    Topform c = p->c;
    if (c->weight >= min_matches &&
	current_given - c->last_matched_given > expiry_distance)
      to_expire = plist_prepend(to_expire, c);
  }

  /* Pass 2: unindex and remove from clist.
     Do NOT zap the topform -- kept clauses hold matching_hint pointers
     to these hints, and the hint_age AVL tree uses matching_hint->id
     as a comparison key.  Freeing the hint would create dangling pointers. */
  for (q = to_expire; q; q = q->next) {
    Topform c = q->v;
    unindex_hint(c);
    clist_remove(c, hint_list);
    expired_count++;
  }
  zap_plist(to_expire);
  return expired_count;
}  /* expire_old_hints */

/*************
 *
 *   active_hints()
 *
 *************/

/* PUBLIC */
int active_hints(void)
{
  return Active_hints_count;
}  /* active_hints */

/*************
 *
 *   compare_doubles() -- qsort comparator
 *
 *************/

static int compare_doubles(const void *a, const void *b)
{
  double da = *(const double *)a;
  double db = *(const double *)b;
  if (da < db) return -1;
  if (da > db) return 1;
  return 0;
}  /* compare_doubles */

/*************
 *
 *   print_hint_match_stats()
 *
 *   Print min/mean/median/max of match counts for hints
 *   that were matched at least once (weight > 0).
 *
 *************/

/* PUBLIC */
void print_hint_match_stats(FILE *fp, Clist hint_list)
{
  int total, n, i;
  double *counts;
  double min_v, max_v, sum, mean, median;
  Clist_pos p;

  if (hint_list == NULL)
    return;

  /* Count hints with at least one match */
  total = 0;
  for (p = hint_list->first; p; p = p->next) {
    if (p->c->weight > 0)
      total++;
  }

  if (total == 0) {
    fprintf(fp, "\n%% Hint match stats: no hints were matched.\n");
    return;
  }

  /* Collect match counts */
  counts = malloc(total * sizeof(double));
  i = 0;
  for (p = hint_list->first; p; p = p->next) {
    if (p->c->weight > 0)
      counts[i++] = p->c->weight;
  }

  qsort(counts, total, sizeof(double), compare_doubles);

  min_v = counts[0];
  max_v = counts[total - 1];
  sum = 0;
  for (i = 0; i < total; i++)
    sum += counts[i];
  mean = sum / total;

  if (total % 2 == 1)
    median = counts[total / 2];
  else
    median = (counts[total / 2 - 1] + counts[total / 2]) / 2.0;

  /* Count never-matched */
  n = 0;
  for (p = hint_list->first; p; p = p->next) {
    if (p->c->weight == 0)
      n++;
  }

  fprintf(fp,
    "\n%% Hint match stats (matched hints only):\n"
    "%%   matched=%d, unmatched=%d, total=%d\n"
    "%%   match counts: min=%.0f, mean=%.1f, median=%.0f, max=%.0f\n",
    total, n, total + n, min_v, mean, median, max_v);

  /* Re-match delta histogram */
  if (Delta_total > 0) {
    static const char *labels[DELTA_BUCKETS] = {
      "0-500", "501-1000", "1001-1500", "1501-2000", "2001-2500",
      "2501-3000", "3001-3500", "3501-4000", "4001-4500", "4501-5000",
      "5001-5500", "5501-6000", "6001-6500", "6501-7000", "7001-7500",
      "7501+"
    };
    fprintf(fp,
      "%%   re-match deltas: n=%d, min=%llu, mean=%.1f, max=%llu\n"
      "%%   delta histogram:\n",
      Delta_total, Delta_min, Delta_sum / Delta_total, Delta_max);
    for (i = 0; i < DELTA_BUCKETS; i++) {
      if (Delta_bucket[i] > 0)
        fprintf(fp, "%%     %10s: %d\n", labels[i], Delta_bucket[i]);
    }
  }

  free(counts);
}  /* print_hint_match_stats */
