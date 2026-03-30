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

#include "demodulate.h"

/* Private definitions and types */

/* Maintain the indexes for forward and backward demodulation.
 */

static Mindex Demod_idx;
static Mindex Back_demod_idx;

/*************
 *
 *   init_demodulator_index()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_demodulator_index(Mindextype mtype, Uniftype utype, int fpa_depth)
{
  Demod_idx = mindex_init(mtype, utype, fpa_depth);
}  /* init_demodulator_index */

/*************
 *
 *   init_back_demod_index()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_back_demod_index(Mindextype mtype, Uniftype utype, int fpa_depth)
{
  Back_demod_idx = mindex_init(mtype, utype, fpa_depth);
}  /* init_back_demod_index */

/*************
 *
 *   index_demodulator()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void index_demodulator(Topform c, int type, Indexop operation, Clock clock)
{
  clock_start(clock);
  idx_demodulator(c, type, operation, Demod_idx);
  clock_stop(clock);
}  /* index_demodulator */

/*************
 *
 *   index_back_demod()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void index_back_demod(Topform c, Indexop operation, Clock clock, BOOL enabled)
{
  if (enabled) {
    clock_start(clock);
    index_clause_back_demod(c, Back_demod_idx, operation);
    clock_stop(clock);
  }
}  /* index_back_demod */

/*************
 *
 *   write_discrim_leaves() -- iterative DFS walk of DISCRIM tree
 *
 *   Uses the same n-counter logic as zap_discrim_tree in discrim.c:
 *   n tracks remaining symbols in the flattened term representation.
 *   When n==0, the node is a leaf with u.data (Plist of entries).
 *
 *************/

static
void write_discrim_leaves(FILE *fp, Discrim root)
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
      /* Leaf node: write entries in Plist order */
      Plist p;
      for (p = cur->u.data; p != NULL; p = p->next) {
        Term t = (Term) p->v;
        Topform c = (Topform) t->container;
        int side = (t == ARG(c->literals->atom, 0)) ? 0 : 1;
        fprintf(fp, "%llu %d\n", c->id, side);
      }
    }
    else {
      /* Internal node: push children in REVERSE order (so first child
         is processed first when popped from stack) */
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
 *   write_demod_index() -- serialize demod DISCRIM tree leaf ordering
 *
 *************/

/* PUBLIC */
void write_demod_index(const char *dir)
{
  char path[600];
  FILE *fp;
  Discrim root;

  if (Demod_idx == NULL || Demod_idx->discrim_tree == NULL)
    return;

  snprintf(path, sizeof(path), "%s/demod_index.txt", dir);
  fp = fopen(path, "w");
  if (!fp)
    return;

  root = Demod_idx->discrim_tree;
  write_discrim_leaves(fp, root);
  fclose(fp);
}  /* write_demod_index */

/*************
 *
 *   restore_demod_index() -- rebuild demod index in saved leaf-list order
 *
 *   Reads (clause_id, side) pairs from demod_index.txt and inserts the
 *   corresponding terms into the demod DISCRIM tree in exactly the
 *   saved order, reproducing the original leaf-list ordering.
 *
 *************/

/* PUBLIC */
void restore_demod_index(const char *dir, Clock clock)
{
  char path[600];
  FILE *fp;
  unsigned long long clause_id;
  int side;

  snprintf(path, sizeof(path), "%s/demod_index.txt", dir);
  fp = fopen(path, "r");
  if (!fp)
    return;  /* no saved index — fall back to default insertion order */

  {
    int count = 0;
    while (fscanf(fp, "%llu %d", &clause_id, &side) == 2) {
      Topform c = find_clause_by_id(clause_id);
      if (c != NULL && c->literals != NULL) {
        Term t = ARG(c->literals->atom, side);
        mindex_update(Demod_idx, t, INSERT);
        count++;
      }
    }
    printf("%%   Restored demod index: %d entries from %s\n", count,
           path);
  }
  fclose(fp);
}  /* restore_demod_index */

/*************
 *
 *   destroy_demodulation_index()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void destroy_demodulation_index(void)
{
  mindex_destroy(Demod_idx);
  Demod_idx = NULL;
}  /* destroy_demodulation_index */

/*************
 *
 *   destroy_back_demod_index()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void destroy_back_demod_index(void)
{
  mindex_destroy(Back_demod_idx);
  Back_demod_idx = NULL;
}  /* destroy_back_demod_index */

/*************
 *
 *   demodulate_clause()
 *
 *************/

/* DOCUMENTATION
Demodulate Topform c, using demodulators alreadly known to this package.
If any rewriting occurs, the justification is appended to
the clause's existing justification.
*/

/* PUBLIC */
void demodulate_clause(Topform c, int step_limit, int increase_limit,
		       BOOL print, BOOL lex_order_vars)
{
  static int limit_hits = 0;
  int starting_step_limit;

  step_limit = step_limit == -1 ? INT_MAX : step_limit;
  increase_limit = increase_limit == -1 ? INT_MAX : increase_limit;
  starting_step_limit = step_limit;

  fdemod_clause(c, Demod_idx, &step_limit, &increase_limit, lex_order_vars);

  if (step_limit == 0 || increase_limit == -1) {
    limit_hits++;
    char *mess = (step_limit == 0 ? "step" : "increase");

    if (print) {
      if (limit_hits == 1) {
	fprintf(stderr, "Demod_%s_limit (see stdout)\n", mess);
	printf("\nDemod_%s_limit: ", mess); f_clause(c);
	printf("\nDemod_%s_limit (steps=%d, size=%d).\n"
	       "The most recent kept clause is %llu.\n"
	       "From here on, a short message will be printed\n"
	       "for each 100 times the limit is hit.\n\n",
	       mess,
	       starting_step_limit - step_limit,
	       clause_symbol_count(c->literals),
	       clause_ids_assigned());
	fflush(stdout);
      }
      else if (limit_hits % 100 == 0) {
	printf("Demod_limit hit %d times.\n", limit_hits);
	fflush(stdout);
      }
    }
  }
}  /* demodulate_clause */

/*************
 *
 *   back_demodulatable()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist back_demodulatable(Topform demod, int type, BOOL lex_order_vars)
{
  return back_demod_indexed(demod, type, Back_demod_idx, lex_order_vars);
}  /* back_demodulatable */

/*************
 *
 *   back_demod_idx_report()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void back_demod_idx_report(void)
{
  printf("Back demod index: ");
  p_fpa_density(Back_demod_idx->fpa);
}  /* back_demod_idx_report */
