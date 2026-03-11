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

#ifndef LADR_DTREE_H
#define LADR_DTREE_H

/*
 * Decision tree inference engine.
 * Tree stored as static const array in dtree_data.h (generated).
 * Classification is a single while loop -- zero allocation.
 */

struct dtree_node {
  short feature_idx;   /* -1 = leaf */
  int   threshold;     /* split value (internal) or strategy_id (leaf) */
  int   child_left;    /* node index for <= branch */
  int   child_right;   /* node index for > branch */
};

/* Classify feature vector, returns strategy_id */
int dtree_classify(const int *fv);

/* Return full per-leaf strategy ranking for feature vector.
   Returns pointer to DTREE_NUM_STRATS shorts (sorted best-first),
   or NULL if tree has no ranking data. */
const short *dtree_rank(const int *fv);

/* Return number of strategies in leaf rankings */
int dtree_num_strats(void);

/* Return number of nodes in compiled tree */
int dtree_num_nodes(void);

#endif /* LADR_DTREE_H */
