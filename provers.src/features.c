/*  Copyright (C) 2026 Jeffrey Machado, Larry Lesyna

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

/* Adapted from LADR-selector src/features.c.
   Uses LADR's Scan_result (struct scan_result) instead of
   the standalone selector's struct scan_data. */

#include "features.h"

#include <stdlib.h>
#include <string.h>

const char *feature_names[NUM_FEATURES] = {
  "n_formulas",        /* 0 */
  "n_axioms",          /* 1 */
  "n_goals",           /* 2 */
  "n_symbols",         /* 3 */
  "has_goal",          /* 4 */
  "has_neg_conj",      /* 5 */
  "is_cnf_only",       /* 6 */
  "is_fof_only",       /* 7 */
  "has_hypothesis",    /* 8 */
  "max_syms_per_form", /* 9 */
  "avg_syms_per_form", /* 10 */
  "max_body_len",      /* 11 */
  "avg_body_len",      /* 12 */
  "domain_hash",       /* 13 */
  "has_equality",      /* 14 */
  "max_depth_est",     /* 15 */
  "avg_depth_est",     /* 16 */
  "max_literals_est",  /* 17 */
  "avg_literals_est",  /* 18 */
  "all_unit_est",      /* 19 */
  "all_horn_est",      /* 20 */
  "neg_nonunit_count", /* 21 */
  "axiom_sym_ratio",   /* 22 */
  "goal_sym_count",    /* 23 */
  "singleton_syms",    /* 24 */
  "multi_form_syms",   /* 25 */
  "log2_n_axioms",     /* 26 */
  "log2_n_symbols",    /* 27 */
  "log2_max_body",     /* 28 */
  "reserved_29",       /* 29 */
  "reserved_30",       /* 30 */
  "reserved_31"        /* 31 */
};

/* Integer log2 approximation (returns 100*log2(n) for n>=1, 0 otherwise) */
static int ilog2x100(int n)
{
  int bits = 0;
  int v;
  if (n <= 0) return 0;
  v = n;
  while (v > 1) {
    v >>= 1;
    bits++;
  }
  /* Linear interpolation within the power-of-2 interval */
  {
    int lo = 1 << bits;
    int frac;
    if (lo == 0) return bits * 100;
    frac = ((n - lo) * 100) / lo;
    return bits * 100 + frac;
  }
}

void extract_features(Scan_result sd, int *fv)
{
  int i, n;
  int has_fof = 0, has_cnf = 0, has_hyp = 0;
  int has_eq = 0;
  int max_syms = 0, sum_syms = 0;
  int max_body = 0;
  long sum_body = 0;
  int max_depth = 0;
  long sum_depth = 0;
  int max_lits = 0;
  long sum_lits = 0;
  int all_unit = 1, all_horn = 1;
  int neg_nonunit = 0;
  int goal_sym_count = 0;
  int *sym_freq = NULL;
  int singleton_syms = 0, multi_form_syms = 0;

  memset(fv, 0, NUM_FEATURES * sizeof(int));

  n = sd->n_entries;
  if (n == 0) return;

  /* Allocate symbol frequency table */
  if (sd->n_symbols > 0) {
    sym_freq = (int *) calloc(sd->n_symbols, sizeof(int));
  }

  for (i = 0; i < n; i++) {
    struct scan_entry *e = &sd->entries[i];
    int lits_est;
    int j;

    if (e->is_fof) has_fof = 1; else has_cnf = 1;
    if (e->role == SCAN_ROLE_HYPOTHESIS) has_hyp = 1;
    if (e->eq_count > 0) has_eq = 1;

    /* Symbols per formula */
    if (e->nsyms > max_syms) max_syms = e->nsyms;
    sum_syms += e->nsyms;

    /* Body length */
    if (e->body_len > max_body) max_body = e->body_len;
    sum_body += e->body_len;

    /* Depth estimate: max_paren_depth from scan */
    if (e->max_paren_depth > max_depth)
      max_depth = e->max_paren_depth;
    sum_depth += e->max_paren_depth;

    /* Literal count estimate: pipe_count + 1 for CNF, rough for FOF */
    lits_est = e->pipe_count + 1;
    if (lits_est > max_lits) max_lits = lits_est;
    sum_lits += lits_est;

    /* Unit / Horn estimates (CNF only) */
    if (!e->is_fof) {
      if (lits_est > 1) all_unit = 0;
      /* Horn estimate: at most 1 positive literal.
         Rough: tilde_count >= lits_est - 1 means at most 1 positive */
      if (e->tilde_count < lits_est - 1) all_horn = 0;
      /* Negative non-unit: all literals negated, >1 literal */
      if (lits_est > 1 && e->tilde_count >= lits_est)
        neg_nonunit++;
    }

    /* Goal symbol count */
    if (e->role == SCAN_ROLE_GOAL || e->role == SCAN_ROLE_NEG_CONJ)
      goal_sym_count += e->nsyms;

    /* Symbol frequency: count how many formulas each symbol appears in */
    if (sym_freq != NULL) {
      for (j = 0; j < e->nsyms; j++) {
        if (e->syms[j] >= 0 && e->syms[j] < sd->n_symbols)
          sym_freq[e->syms[j]]++;
      }
    }
  }

  /* Count singleton and multi-formula symbols */
  if (sym_freq != NULL) {
    for (i = 0; i < sd->n_symbols; i++) {
      if (sym_freq[i] == 1) singleton_syms++;
      else if (sym_freq[i] > 1) multi_form_syms++;
    }
    free(sym_freq);
  }

  /* Fill feature vector */
  fv[F_N_FORMULAS]        = n;
  fv[F_N_AXIOMS]          = sd->n_axioms;
  fv[F_N_GOALS]           = sd->n_goals;
  fv[F_N_SYMBOLS]         = sd->n_symbols;
  fv[F_HAS_GOAL]          = (sd->n_goals > 0) ? 1 : 0;
  fv[F_HAS_NEG_CONJ]      = sd->has_neg_conj ? 1 : 0;
  fv[F_IS_CNF_ONLY]       = (has_cnf && !has_fof) ? 1 : 0;
  fv[F_IS_FOF_ONLY]       = (has_fof && !has_cnf) ? 1 : 0;
  fv[F_HAS_HYPOTHESIS]    = has_hyp;
  fv[F_MAX_SYMS_PER_FORM] = max_syms;
  fv[F_AVG_SYMS_PER_FORM] = (sum_syms * 100) / n;
  fv[F_MAX_BODY_LEN]      = max_body;
  fv[F_AVG_BODY_LEN]      = (int)(sum_body * 100 / n);
  fv[F_DOMAIN_HASH]       = 0;  /* set by caller if filename known */
  fv[F_HAS_EQUALITY]      = has_eq;
  fv[F_MAX_DEPTH_EST]     = max_depth;
  fv[F_AVG_DEPTH_EST]     = (int)(sum_depth * 100 / n);
  fv[F_MAX_LITERALS_EST]  = max_lits;
  fv[F_AVG_LITERALS_EST]  = (int)(sum_lits * 100 / n);
  fv[F_ALL_UNIT_EST]      = all_unit;
  fv[F_ALL_HORN_EST]      = all_horn;
  fv[F_NEG_NONUNIT_COUNT] = neg_nonunit;

  /* Axiom/symbol ratio x100 */
  if (sd->n_symbols > 0)
    fv[F_AXIOM_SYM_RATIO] = (sd->n_axioms * 100) / sd->n_symbols;
  else
    fv[F_AXIOM_SYM_RATIO] = 0;

  fv[F_GOAL_SYM_COUNT]    = goal_sym_count;
  fv[F_SINGLETON_SYMS]    = singleton_syms;
  fv[F_MULTI_FORM_SYMS]   = multi_form_syms;
  fv[F_LOG2_N_AXIOMS]     = ilog2x100(sd->n_axioms);
  fv[F_LOG2_N_SYMBOLS]    = ilog2x100(sd->n_symbols);
  fv[F_LOG2_MAX_BODY]     = ilog2x100(max_body);
}

void set_domain_hash(int *fv, const char *filename)
{
  const char *base;
  const char *p;
  unsigned int h = 0;
  int i;

  if (filename == NULL) return;

  base = filename;
  p = strrchr(filename, '/');
  if (p != NULL) base = p + 1;

  for (i = 0; i < 3 && base[i] != '\0'; i++) {
    if (base[i] >= 'A' && base[i] <= 'Z')
      h = h * 31 + (unsigned int)(base[i] - 'A');
    else if (base[i] >= 'a' && base[i] <= 'z')
      h = h * 31 + (unsigned int)(base[i] - 'a');
    else
      break;
  }
  fv[F_DOMAIN_HASH] = (int)(h % 10000);
}
