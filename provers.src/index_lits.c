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

#include "index_lits.h"

/* Private definitions and types */

static Lindex  Unit_fpa_idx;          /* unit bsub, unit conflict */
static Lindex  Nonunit_fpa_idx;       /* back unit del */

static Lindex  Unit_discrim_idx;      /* unit fsub, unit del */
static Di_tree Nonunit_features_idx;  /* nonunit fsub, nonunit bsub */



/*************
 *
 *   write_discrim_entries() -- walk DISCRIM tree, write clause IDs
 *
 *   Uses the same n-counter as zap_discrim_tree in discrim.c.
 *   For each leaf entry (an atom Term), navigates atom->container
 *   to get the clause ID.
 *
 *************/

static
void write_discrim_entries(FILE *fp, Discrim root)
{
  struct frame { Discrim node; int n; };
  int cap = 256, top = 0;
  struct frame *stack = (struct frame *) safe_malloc(cap * sizeof(struct frame));

  stack[top].node = root;
  stack[top].n = 1;
  top++;

  while (top > 0) {
    Discrim cur;
    int cur_n;

    top--;
    cur = stack[top].node;
    cur_n = stack[top].n;

    if (cur_n == 0) {
      Plist p;
      for (p = cur->u.data; p != NULL; p = p->next) {
        Term atom = (Term) p->v;
        Topform c = (Topform) atom->container;
        fprintf(fp, "%llu\n", c->id);
      }
    }
    else {
      Discrim k;
      Discrim *kids = NULL;
      int n_kids = 0, i;

      for (k = cur->u.kids; k != NULL; k = k->next)
        n_kids++;
      if (n_kids > 0) {
        kids = (Discrim *) safe_malloc(n_kids * sizeof(Discrim));
        i = 0;
        for (k = cur->u.kids; k != NULL; k = k->next)
          kids[i++] = k;
        for (i = n_kids - 1; i >= 0; i--) {
          int arity;
          k = kids[i];
          if (k->type == AC_ARG_TYPE || k->type == AC_NV_ARG_TYPE)
            arity = 0;
          else if (DVAR(k))
            arity = 0;
          else
            arity = sn_to_arity(k->symbol);
          if (top >= cap) {
            cap *= 2;
            stack = (struct frame *) safe_realloc(stack,
                                                  cap * sizeof(struct frame));
          }
          stack[top].node = k;
          stack[top].n = cur_n + arity - 1;
          top++;
        }
        safe_free(kids);
      }
    }
  }
  safe_free(stack);
}

/*************
 *
 *   write_unit_discrim_index() -- serialize Unit_discrim_idx leaf ordering
 *
 *************/

/* PUBLIC */
void write_unit_discrim_index(const char *dir)
{
  char path[600];
  FILE *fp;

  if (Unit_discrim_idx == NULL)
    return;

  snprintf(path, sizeof(path), "%s/unit_discrim_index.txt", dir);
  fp = fopen(path, "w");
  if (!fp)
    return;

  fprintf(fp, "POS\n");
  if (Unit_discrim_idx->pos && Unit_discrim_idx->pos->discrim_tree)
    write_discrim_entries(fp, Unit_discrim_idx->pos->discrim_tree);
  fprintf(fp, "NEG\n");
  if (Unit_discrim_idx->neg && Unit_discrim_idx->neg->discrim_tree)
    write_discrim_entries(fp, Unit_discrim_idx->neg->discrim_tree);
  fclose(fp);
}  /* write_unit_discrim_index */

/*************
 *
 *   restore_unit_discrim_index() -- rebuild from serialized leaf ordering
 *
 *************/

/* PUBLIC */
void restore_unit_discrim_index(const char *dir)
{
  char path[600];
  FILE *fp;
  char line[128];
  int section = -1;  /* 0 = POS, 1 = NEG */
  int count = 0;

  snprintf(path, sizeof(path), "%s/unit_discrim_index.txt", dir);
  fp = fopen(path, "r");
  if (!fp)
    return;

  while (fgets(line, sizeof(line), fp)) {
    unsigned long long clause_id;
    if (strncmp(line, "POS", 3) == 0) {
      section = 0;
      continue;
    }
    if (strncmp(line, "NEG", 3) == 0) {
      section = 1;
      continue;
    }
    if (section < 0)
      continue;
    if (sscanf(line, "%llu", &clause_id) == 1) {
      Topform c = find_clause_by_id(clause_id);
      if (c != NULL && c->literals != NULL) {
        Term atom = c->literals->atom;
        if (section == 0)
          mindex_update(Unit_discrim_idx->pos, atom, INSERT);
        else
          mindex_update(Unit_discrim_idx->neg, atom, INSERT);
        count++;
      }
    }
  }
  fclose(fp);
  printf("%%   Restored unit discrim index: %d entries from %s\n", count,
         path);
}  /* restore_unit_discrim_index */


/*************
 *
 *   index_literals_fpa_only() -- index only into FPA indexes (skip DISCRIM)
 *
 *   Used during checkpoint resume: DISCRIM indexes are restored from
 *   serialized leaf ordering; FPA indexes are order-independent.
 *
 *************/

/* PUBLIC */
void index_literals_fpa_only(Topform c, Indexop op, Clock clock, BOOL no_fapl)
{
  BOOL unit = (number_of_literals(c->literals) == 1);
  clock_start(clock);
  if (!no_fapl || !positive_clause(c->literals))
    lindex_update(unit ? Unit_fpa_idx : Nonunit_fpa_idx, c, op);
  /* Skip Unit_discrim_idx (restored from file).
     But DO populate Nonunit_features_idx (subsumption filter). */
  if (!unit) {
    int *f = features(c->literals);
    int flen = feature_length();
    if (op == INSERT)
      di_tree_insert(f, flen, Nonunit_features_idx, c);
    else
      di_tree_delete(f, flen, Nonunit_features_idx, c);
  }
  clock_stop(clock);
}  /* index_literals_fpa_only */


/*************
 *
 *   init_lits_index()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_literals_index(int depth)
{
  Unit_fpa_idx     = lindex_init(FPA, ORDINARY_UNIF, depth,
				 FPA, ORDINARY_UNIF, depth);

  Nonunit_fpa_idx  = lindex_init(FPA, ORDINARY_UNIF, depth,
				 FPA, ORDINARY_UNIF, depth);

  Unit_discrim_idx = lindex_init(DISCRIM_BIND, ORDINARY_UNIF, depth,
				 DISCRIM_BIND, ORDINARY_UNIF, depth);

  Nonunit_features_idx = init_di_tree();
}  /* init_lits_index */

/*************
 *
 *   lits_destroy_index()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void destroy_literals_index(void)
{
  lindex_destroy(Unit_fpa_idx);       Unit_fpa_idx = NULL;
  lindex_destroy(Nonunit_fpa_idx);    Nonunit_fpa_idx = NULL;
  lindex_destroy(Unit_discrim_idx);   Unit_discrim_idx = NULL;
  zap_di_tree(Nonunit_features_idx,
	      feature_length());      Nonunit_features_idx = NULL;
}  /* lits_destroy_index */

/*************
 *
 *   index_literals()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void index_literals(Topform c, Indexop op, Clock clock, BOOL no_fapl)
{
  BOOL unit = (number_of_literals(c->literals) == 1);
  clock_start(clock);
  if (!no_fapl || !positive_clause(c->literals))
    lindex_update(unit ? Unit_fpa_idx : Nonunit_fpa_idx, c, op);

  if (unit)
    lindex_update(Unit_discrim_idx, c, op);
  else {
    int *f = features(c->literals);
    int flen = feature_length();
    if (op == INSERT)
      di_tree_insert(f, flen, Nonunit_features_idx, c);
    else
      di_tree_delete(f, flen, Nonunit_features_idx, c);
  }
  clock_stop(clock);
}  /* index_literals */

/*************
 *
 *   index_denial()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void index_denial(Topform c, Indexop op, Clock clock)
{
  BOOL unit = (number_of_literals(c->literals) == 1);
  clock_start(clock);
  lindex_update(unit ? Unit_fpa_idx : Nonunit_fpa_idx, c, op);
  clock_stop(clock);
}  /* index_denial */

/*************
 *
 *   unit_conflict()
 *
 *************/

/* DOCUMENTATION
Look for conflicting units.  Send any that are found to empty_proc().
*/

/* PUBLIC */
void unit_conflict(Topform c, void (*empty_proc) (Topform))
{
  unit_conflict_by_index(c, Unit_fpa_idx, empty_proc);
}  /* unit_conflict */

/*************
 *
 *   unit_deletion()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void unit_deletion(Topform c)
{
  unit_delete(c, Unit_discrim_idx);
}  /* unit_deletion */

/*************
 *
 *   back_unit_deletable()
 *
 *************/

/* DOCUMENTATION
Return the list of clauses that can be back unit deleted by
the given clause.
*/

/* PUBLIC */
Plist back_unit_deletable(Topform c)
{
  return back_unit_del_by_index(c, Nonunit_fpa_idx);
}  /* back_unit_deletable */

/*************
 *
 *   forward_subsumption()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Topform forward_subsumption(Topform d)
{
  Topform subsumer = forward_subsume(d, Unit_discrim_idx);
  if (!subsumer)
    subsumer = forward_feature_subsume(d, Nonunit_features_idx);
  return subsumer;
}  /* forward_subsumption */

/*************
 *
 *   forward_subsumption_filter()
 *
 *   Variant of forward_subsumption that skips candidates rejected by
 *   accept_cb.  Used to support set(ancestor_subsume): when the first
 *   subsumer is an alphabetic variant whose proof is longer than the
 *   new clause's, skip it and try the next candidate.  Matches Otter's
 *   forward_subsume which iterates past anc_subsume blocks.
 *
 *************/

/* PUBLIC */
Topform forward_subsumption_filter(Topform d,
                                   BOOL (*accept_cb)(Topform subsumer,
                                                     Topform new_clause,
                                                     void *arg),
                                   void *cb_arg)
{
  Topform subsumer = forward_subsume_filter(d, Unit_discrim_idx,
                                            accept_cb, cb_arg);
  if (!subsumer)
    subsumer = forward_feature_subsume(d, Nonunit_features_idx);
  return subsumer;
}  /* forward_subsumption_filter */

/*************
 *
 *   back_subsumption()
 *
 *************/

/* DOCUMENTATION
Return the list of clauses that can ar back subsumed by the given clause.
*/

/* PUBLIC */
Plist back_subsumption(Topform c)
{
  Plist p1 = back_subsume(c, Unit_fpa_idx);
#if 0
  Plist p2 = back_subsume(c, Nonunit_fpa_idx);
#else
  Plist p2 = back_feature_subsume(c, Nonunit_features_idx);
#endif

  Plist p3 = plist_cat(p1, p2);
  return p3;
}  /* back_subsumption */

/*************
 *
 *   lits_idx_report()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void lits_idx_report(void)
{
  printf("Pos unit lits index: ");
  p_fpa_density(Unit_fpa_idx->pos->fpa);
  printf("Neg unit lits index: ");
  p_fpa_density(Unit_fpa_idx->neg->fpa);
  printf("Pos nonunit lits index: ");
  p_fpa_density(Nonunit_fpa_idx->pos->fpa);
  printf("Neg nonunit lits index: ");
  p_fpa_density(Nonunit_fpa_idx->neg->fpa);
}  /* lits_idx_report */

/*************
 *
 *   write_fpa_lits_index() / restore_fpa_lits_index()
 *
 *   Serialize/deserialize the 4 FPA literal indexes for checkpoint.
 *
 *************/

/* PUBLIC */
void write_fpa_lits_index(const char *dir)
{
  char path[600];
  FILE *fp;

  snprintf(path, sizeof(path), "%s/fpa_lits_index.txt", dir);
  fp = fopen(path, "w");
  if (!fp) return;

  fprintf(fp, "SECTION unit_pos\n");
  fpa_write_index(fp, Unit_fpa_idx->pos->fpa);
  fprintf(fp, "SECTION unit_neg\n");
  fpa_write_index(fp, Unit_fpa_idx->neg->fpa);
  fprintf(fp, "SECTION nonunit_pos\n");
  fpa_write_index(fp, Nonunit_fpa_idx->pos->fpa);
  fprintf(fp, "SECTION nonunit_neg\n");
  fpa_write_index(fp, Nonunit_fpa_idx->neg->fpa);
  fprintf(fp, "END\n");

  fclose(fp);
}  /* write_fpa_lits_index */

/* PUBLIC */
BOOL restore_fpa_lits_index(const char *dir)
{
  char path[600], buf[64];
  FILE *fp;
  int restored = 0;

  snprintf(path, sizeof(path), "%s/fpa_lits_index.txt", dir);
  fp = fopen(path, "r");
  if (!fp) return FALSE;

  while (fscanf(fp, " %63s", buf) == 1) {
    if (strcmp(buf, "END") == 0) break;
    if (strcmp(buf, "SECTION") != 0) continue;
    if (fscanf(fp, " %63s", buf) != 1) break;

    if (strcmp(buf, "unit_pos") == 0) {
      if (fpa_restore_index(fp, Unit_fpa_idx->pos->fpa)) restored++;
    } else if (strcmp(buf, "unit_neg") == 0) {
      if (fpa_restore_index(fp, Unit_fpa_idx->neg->fpa)) restored++;
    } else if (strcmp(buf, "nonunit_pos") == 0) {
      if (fpa_restore_index(fp, Nonunit_fpa_idx->pos->fpa)) restored++;
    } else if (strcmp(buf, "nonunit_neg") == 0) {
      if (fpa_restore_index(fp, Nonunit_fpa_idx->neg->fpa)) restored++;
    }
  }

  fclose(fp);
  printf("%%   Restored FPA literals index: %d sections from %s\n",
         restored, path);
  return (restored == 4);
}  /* restore_fpa_lits_index */
