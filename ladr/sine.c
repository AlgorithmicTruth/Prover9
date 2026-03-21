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

#include "sine.h"
#include "tptp_parse.h"
#include "symbols.h"
#include <limits.h>
#include <stdlib.h>
#include <string.h>

static int Sine_depth_attr_id = -1;

/*************
 *
 *   sine_depth_attr()
 *
 *   Register (on first call) and return the attribute ID for "sine_depth".
 *
 *************/

int sine_depth_attr(void)
{
  if (Sine_depth_attr_id < 0)
    Sine_depth_attr_id = register_attribute("sine_depth", INT_ATTRIBUTE);
  return Sine_depth_attr_id;
}  /* sine_depth_attr */

/*************
 *
 *   collect_formula_symbols()
 *
 *   Iterative DFS collecting unique symnums from a Formula into buf[].
 *   Uses seen[] (pre-allocated, size >= greatest_symnum()+1) for O(1) dedup.
 *   Caller is responsible for clearing only the entries that were set.
 *
 *************/

static void collect_formula_symbols(Formula f, BOOL *seen, int *buf, int *buf_len)
{
  /* Phase 1: walk the formula tree (AND/OR/NOT/QUANT nodes) to find atoms */
  int fstack_cap = 256;
  Formula *fstack = safe_malloc(fstack_cap * sizeof(Formula));
  int ftop = 0;
  int i, sn;
  fstack[0] = f;

  while (ftop >= 0) {
    Formula cur = fstack[ftop--];

    if (cur->type == ATOM_FORM) {
      /* Phase 2: walk the term tree rooted at cur->atom */
      int tstack_cap = 256;
      Term *tstack = safe_malloc(tstack_cap * sizeof(Term));
      int ttop = 0;
      tstack[0] = cur->atom;

      while (ttop >= 0) {
        Term t = tstack[ttop--];
        if (VARIABLE(t))
          continue;
        sn = SYMNUM(t);
        /* Skip logical/non-content symbols: equality and
           formula-level variables (arity-0 with variable name,
           not yet converted to proper variables). */
        if (is_eq_symbol(sn))
          ;  /* skip = but still traverse children */
        else if (ARITY(t) == 0 && variable_name(sn_to_str(sn)))
          ;  /* skip formula-level variable */
        else if (!seen[sn]) {
          seen[sn] = TRUE;
          buf[(*buf_len)++] = sn;
        }
        for (i = ARITY(t) - 1; i >= 0; i--) {
          if (++ttop >= tstack_cap) {
            tstack_cap *= 2;
            tstack = safe_realloc(tstack, tstack_cap * sizeof(*tstack));
          }
          tstack[ttop] = ARG(t, i);
        }
      }
      safe_free(tstack);
    }
    else {
      for (i = cur->arity - 1; i >= 0; i--) {
        if (++ftop >= fstack_cap) {
          fstack_cap *= 2;
          fstack = safe_realloc(fstack, fstack_cap * sizeof(*fstack));
        }
        fstack[ftop] = cur->kids[i];
      }
    }
  }
  safe_free(fstack);
}  /* collect_formula_symbols */

/*************
 *
 *   sine_filter()
 *
 *   SInE premise selection: given axioms and goals (Plists of Formula),
 *   return a filtered Plist of axioms relevant to the goals.
 *
 *   tolerance_pct: tight trigger tolerance as percentage (e.g. 200 = 2.0x).
 *     Symbol s triggers axiom A iff occ(s)*100 <= tolerance_pct * min_occ(A).
 *   tolerance2_pct: wide trigger tolerance for usable (e.g. 300 = 3.0x).
 *     0 = disabled (single-threshold mode).
 *     When >0, axioms passing tight threshold -> SOS, axioms passing only
 *     wide threshold -> usable, rest -> unselected.  Both thresholds use
 *     the same BFS propagation (wide tolerance drives symbol activation).
 *   max_depth: BFS depth limit (0 = iterate to fixpoint).
 *
 *   Outputs three Plists (preserving original order).  Caller owns all.
 *   When tolerance2_pct==0: tight-selected -> SOS, unselected -> usable,
 *     unselected list is empty (soft filter for backward compatibility).
 *
 *************/

void sine_filter(Plist axioms, Plist goals,
                 int tolerance_pct, int tolerance2_pct,
                 int max_depth,
                 Plist *p_sos, Plist *p_usable, Plist *p_unselected)
{
  int n_axioms = plist_count(axioms);
  int sn_size, i, j, depth;
  int **axiom_syms;
  int *axiom_nsyms, *occ, *sym_buf, *min_occ;
  int *sel_depth;    /* tight-selected: BFS depth (1-based), 0=not tight */
  int *loose_depth;  /* wide-selected:  BFS depth (1-based), 0=not wide  */
  BOOL *seen, *active, *next_active;
  Plist sos_result, usable_result, unsel_result;
  int eff_tol2;

  if (n_axioms == 0 || goals == NULL) {
    *p_sos = axioms;
    *p_usable = NULL;
    *p_unselected = NULL;
    return;
  }

  sn_size = greatest_symnum() + 1;
  if (sn_size <= 0) {
    *p_sos = axioms;
    *p_usable = NULL;
    *p_unselected = NULL;
    return;
  }

  /* Effective wide tolerance: must be >= tight tolerance */
  eff_tol2 = tolerance2_pct;
  if (eff_tol2 > 0 && eff_tol2 < tolerance_pct)
    eff_tol2 = tolerance_pct;

  /* Per-axiom symbol lists: axiom_syms[i] is an array of symnums,
     axiom_nsyms[i] is the count. */
  axiom_syms = safe_calloc(n_axioms, sizeof(int *));
  axiom_nsyms = safe_calloc(n_axioms, sizeof(int));

  /* occ[s] = number of axioms containing symbol s */
  occ = safe_calloc(sn_size, sizeof(int));

  /* seen[] for dedup in collect_formula_symbols */
  seen = safe_calloc(sn_size, sizeof(BOOL));

  /* Temporary buffer for collecting symbols from one formula */
  sym_buf = safe_malloc(sn_size * sizeof(int));

  /* Phase 1: collect symbols per axiom and compute occ[] */
  {
    Plist p;
    int idx;
    for (p = axioms, idx = 0; p; p = p->next, idx++) {
      int buf_len = 0;
      collect_formula_symbols((Formula) p->v, seen, sym_buf, &buf_len);

      /* Copy symbols for this axiom */
      axiom_syms[idx] = safe_malloc(buf_len * sizeof(int));
      memcpy(axiom_syms[idx], sym_buf, buf_len * sizeof(int));
      axiom_nsyms[idx] = buf_len;

      /* Increment occ[] for each unique symbol */
      for (j = 0; j < buf_len; j++)
        occ[sym_buf[j]]++;

      /* Clear seen[] for entries we set (avoid O(sn_size) memset) */
      for (j = 0; j < buf_len; j++)
        seen[sym_buf[j]] = FALSE;
    }
  }

  /* Phase 2: compute min_occ[i] for each axiom */
  min_occ = safe_malloc(n_axioms * sizeof(int));
  for (i = 0; i < n_axioms; i++) {
    int mo = INT_MAX;
    for (j = 0; j < axiom_nsyms[i]; j++) {
      int o = occ[axiom_syms[i][j]];
      if (o < mo)
        mo = o;
    }
    min_occ[i] = (mo == INT_MAX) ? 0 : mo;
  }

  /* Phase 3: seed active symbols from goals */
  active = safe_calloc(sn_size, sizeof(BOOL));
  next_active = safe_calloc(sn_size, sizeof(BOOL));
  memset(seen, 0, sn_size * sizeof(BOOL));  /* reuse seen for goal symbols */

  {
    Plist p;
    for (p = goals; p; p = p->next) {
      int buf_len = 0;
      collect_formula_symbols((Formula) p->v, seen, sym_buf, &buf_len);
      for (j = 0; j < buf_len; j++) {
        active[sym_buf[j]] = TRUE;
        seen[sym_buf[j]] = FALSE;  /* clean up */
      }
    }
  }

  /* Phase 4: BFS loop with two thresholds.
     sel_depth[i]:   tight-selected at BFS depth d (1-based), 0=not tight.
     loose_depth[i]: wide-selected at BFS depth d (1-based), 0=not wide.
     An axiom can be tight (passes both), loose-only (passes wide but not
     tight), or unselected.  Both tight and loose axioms propagate their
     symbols to next_active (wide tolerance drives BFS expansion). */
  sel_depth = safe_calloc(n_axioms, sizeof(int));
  loose_depth = safe_calloc(n_axioms, sizeof(int));
  depth = 0;

  for (;;) {
    BOOL progress;
    BOOL *tmp;
    int k;
    long long occ_100, tight_rhs, wide_rhs;

    if (max_depth > 0 && depth >= max_depth)
      break;

    progress = FALSE;
    memcpy(next_active, active, sn_size * sizeof(BOOL));

    for (i = 0; i < n_axioms; i++) {
      if (sel_depth[i] || loose_depth[i])
        continue;  /* already selected at some level */
      for (j = 0; j < axiom_nsyms[i]; j++) {
        int s = axiom_syms[i][j];
        if (!active[s])
          continue;
        occ_100 = (long long)occ[s] * 100;
        tight_rhs = (long long)tolerance_pct * min_occ[i];
        if (occ_100 <= tight_rhs) {
          /* Passes tight threshold -> SOS */
          sel_depth[i] = depth + 1;
          for (k = 0; k < axiom_nsyms[i]; k++)
            next_active[axiom_syms[i][k]] = TRUE;
          progress = TRUE;
          break;
        }
        if (eff_tol2 > 0) {
          wide_rhs = (long long)eff_tol2 * min_occ[i];
          if (occ_100 <= wide_rhs) {
            /* Passes wide threshold only -> usable */
            loose_depth[i] = depth + 1;
            for (k = 0; k < axiom_nsyms[i]; k++)
              next_active[axiom_syms[i][k]] = TRUE;
            progress = TRUE;
            break;
          }
        }
      }
    }

    if (!progress)
      break;

    tmp = active;
    active = next_active;
    next_active = tmp;

    depth++;
  }

#ifdef DEBUG
  /* Diagnostic: per-depth counts to stderr */
  if (depth > 0) {
    int *dcnt_tight = safe_calloc(depth + 1, sizeof(int));
    int *dcnt_loose = safe_calloc(depth + 1, sizeof(int));
    int total_tight = 0, total_loose = 0;
    for (i = 0; i < n_axioms; i++) {
      if (sel_depth[i] > 0) {
        dcnt_tight[sel_depth[i]]++;
        total_tight++;
      }
      else if (loose_depth[i] > 0) {
        dcnt_loose[loose_depth[i]]++;
        total_loose++;
      }
    }
    fprintf(stderr, "%% SInE: %d tight + %d loose of %d (%d depths):",
            total_tight, total_loose, n_axioms, depth);
    for (i = 1; i <= depth; i++)
      fprintf(stderr, " d%d=%d+%d", i, dcnt_tight[i], dcnt_loose[i]);
    fprintf(stderr, "\n");
    safe_free(dcnt_tight);
    safe_free(dcnt_loose);
  }
#endif

  /* Phase 5: set sine_depth attribute on each selected Formula,
     then partition into three output lists.
     tight-selected -> SOS, loose-selected -> usable.
     When tolerance2==0 (single-threshold): unselected -> usable (soft filter).
     When tolerance2>0 (two-threshold):     unselected -> unselected list. */
  {
    Plist p;
    int idx, attr_id;
    attr_id = sine_depth_attr();
    for (p = axioms, idx = 0; p; p = p->next, idx++) {
      int d = sel_depth[idx] ? sel_depth[idx] : loose_depth[idx];
      if (d > 0) {
        Formula f = (Formula) p->v;
        f->attributes = set_int_attribute(f->attributes, attr_id, d);
      }
    }
  }

  sos_result = NULL;
  usable_result = NULL;
  unsel_result = NULL;
  {
    Plist p;
    int idx;
    for (p = axioms, idx = 0; p; idx++) {
      Plist nxt = p->next;
      p->next = NULL;
      if (sel_depth[idx]) {
        /* Tight-selected -> SOS */
        sos_result = plist_cat(sos_result, p);
      }
      else if (loose_depth[idx]) {
        /* Wide-selected only -> usable */
        usable_result = plist_cat(usable_result, p);
      }
      else if (eff_tol2 == 0) {
        /* Single-threshold soft filter: unselected -> usable */
        usable_result = plist_cat(usable_result, p);
      }
      else {
        /* Two-threshold: unselected -> zap candidate */
        unsel_result = plist_cat(unsel_result, p);
      }
      p = nxt;
    }
  }

  *p_sos = sos_result;
  *p_usable = usable_result;
  *p_unselected = unsel_result;

  /* Cleanup */
  for (i = 0; i < n_axioms; i++)
    safe_free(axiom_syms[i]);
  safe_free(axiom_syms);
  safe_free(axiom_nsyms);
  safe_free(occ);
  safe_free(seen);
  safe_free(sym_buf);
  safe_free(min_occ);
  safe_free(active);
  safe_free(next_active);
  safe_free(sel_depth);
  safe_free(loose_depth);
}  /* sine_filter */

/*************
 *
 *   sine_filter_scan()
 *
 *   SInE premise selection on raw scan data (no Formula/Term trees needed).
 *   Same BFS algorithm as sine_filter() but operates on scan_entry arrays.
 *
 *   Inputs:
 *     entries[]   - scanned formula entries with temp symbol IDs
 *     n_entries   - total count
 *     n_symbols   - total unique temp symbol IDs
 *     tolerance_pct, tolerance2_pct, max_depth - same as sine_filter()
 *
 *   Outputs (caller-allocated, n_entries ints each, zeroed on entry):
 *     sel_depth[i]   - tight-selected BFS depth (1-based), 0 = not tight
 *     loose_depth[i] - wide-selected BFS depth (1-based), 0 = not wide
 *
 *************/

void sine_filter_scan(struct scan_entry *entries, int n_entries,
                      int n_symbols,
                      int tolerance_pct, int tolerance2_pct,
                      int max_depth, int max_axioms,
                      int *sel_depth, int *loose_depth)
{
  int *occ;         /* occ[sym_id] = number of axioms containing symbol */
  int *min_occ;     /* min_occ[i] = min occ among axiom i's symbols */
  BOOL *active;     /* active[sym_id] = currently active symbol */
  BOOL *next_active;
  int eff_tol2;
  int i, j, depth;
  int n_selected;   /* running count of selected axioms (tight + loose) */

  if (n_symbols <= 0 || n_entries <= 0)
    return;

  eff_tol2 = tolerance2_pct;
  if (eff_tol2 > 0 && eff_tol2 < tolerance_pct)
    eff_tol2 = tolerance_pct;

  /* Compute occ[] -- goals and hypotheses don't contribute (they seed BFS) */
  occ = safe_calloc(n_symbols, sizeof(int));
  for (i = 0; i < n_entries; i++) {
    if (entries[i].role == SCAN_ROLE_GOAL ||
        entries[i].role == SCAN_ROLE_HYPOTHESIS)
      continue;
    for (j = 0; j < entries[i].nsyms; j++) {
      int sid = entries[i].syms[j];
      occ[sid]++;
    }
  }

  /* Compute min_occ[] for axiom-role entries */
  min_occ = safe_malloc(n_entries * sizeof(int));
  for (i = 0; i < n_entries; i++) {
    if (entries[i].role == SCAN_ROLE_GOAL ||
        entries[i].role == SCAN_ROLE_HYPOTHESIS) {
      min_occ[i] = 0;
      continue;
    }
    {
      int mo = INT_MAX;
      for (j = 0; j < entries[i].nsyms; j++) {
        int sid = entries[i].syms[j];
        int o = occ[sid];
        if (o < mo) mo = o;
      }
      min_occ[i] = (mo == INT_MAX) ? 0 : mo;
    }
  }

  /* Seed active symbols from goals, cnf negated_conjecture, and hypotheses */
  active = safe_calloc(n_symbols, sizeof(BOOL));
  next_active = safe_calloc(n_symbols, sizeof(BOOL));
  n_selected = 0;
  for (i = 0; i < n_entries; i++) {
    if (entries[i].role == SCAN_ROLE_GOAL ||
        entries[i].role == SCAN_ROLE_NEG_CONJ ||
        entries[i].role == SCAN_ROLE_HYPOTHESIS) {
      for (j = 0; j < entries[i].nsyms; j++) {
        int sid = entries[i].syms[j];
        active[sid] = TRUE;
      }
      /* Hypotheses are always selected (depth 1) */
      if (entries[i].role == SCAN_ROLE_HYPOTHESIS) {
        sel_depth[i] = 1;
        n_selected++;
      }
    }
  }

  /* BFS */
  depth = 0;
  for (;;) {
    BOOL progress = FALSE;
    BOOL *tmp;

    if (max_depth > 0 && depth >= max_depth)
      break;

    memcpy(next_active, active, n_symbols * sizeof(BOOL));

    for (i = 0; i < n_entries; i++) {
      long long occ_100, tight_rhs, wide_rhs;
      int k;

      if (entries[i].role == SCAN_ROLE_GOAL ||
          entries[i].role == SCAN_ROLE_HYPOTHESIS)
        continue;
      if (sel_depth[i] || loose_depth[i])
        continue;

      for (j = 0; j < entries[i].nsyms; j++) {
        int s = entries[i].syms[j];
        if (!active[s])
          continue;
        occ_100 = (long long)occ[s] * 100;
        tight_rhs = (long long)tolerance_pct * min_occ[i];
        if (occ_100 <= tight_rhs) {
          sel_depth[i] = depth + 1;
          n_selected++;
          for (k = 0; k < entries[i].nsyms; k++)
            next_active[entries[i].syms[k]] = TRUE;
          progress = TRUE;
          break;
        }
        if (eff_tol2 > 0) {
          wide_rhs = (long long)eff_tol2 * min_occ[i];
          if (occ_100 <= wide_rhs) {
            loose_depth[i] = depth + 1;
            n_selected++;
            for (k = 0; k < entries[i].nsyms; k++)
              next_active[entries[i].syms[k]] = TRUE;
            progress = TRUE;
            break;
          }
        }
      }
      /* Check max_axioms cap */
      if (max_axioms > 0 && n_selected >= max_axioms)
        break;
    }

    if (!progress)
      break;
    if (max_axioms > 0 && n_selected >= max_axioms)
      break;

    tmp = active;
    active = next_active;
    next_active = tmp;
    depth++;
  }

#ifdef DEBUG
  /* Diagnostic: per-depth counts to stderr */
  if (depth > 0) {
    int *dcnt_tight = safe_calloc(depth + 1, sizeof(int));
    int *dcnt_loose = safe_calloc(depth + 1, sizeof(int));
    int total_tight = 0, total_loose = 0;
    for (i = 0; i < n_entries; i++) {
      if (sel_depth[i] > 0) {
        dcnt_tight[sel_depth[i]]++;
        total_tight++;
      }
      else if (loose_depth[i] > 0) {
        dcnt_loose[loose_depth[i]]++;
        total_loose++;
      }
    }
    fprintf(stderr, "%% SInE (scan): %d tight + %d loose of %d (%d depths):",
            total_tight, total_loose, n_entries, depth);
    for (i = 1; i <= depth; i++)
      fprintf(stderr, " d%d=%d+%d", i, dcnt_tight[i], dcnt_loose[i]);
    fprintf(stderr, "\n");
    safe_free(dcnt_tight);
    safe_free(dcnt_loose);
  }
#endif

  safe_free(occ);
  safe_free(min_occ);
  safe_free(active);
  safe_free(next_active);
}  /* sine_filter_scan */
