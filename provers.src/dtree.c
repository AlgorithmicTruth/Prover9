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

#include "dtree.h"
#include "dtree_data.h"

int dtree_classify(const int *fv)
{
  int idx = 0;
  while (1) {
    const struct dtree_node *node = &Tree_nodes[idx];
    if (node->feature_idx < 0)
      return node->threshold;  /* leaf: strategy_id */
    if (fv[node->feature_idx] <= node->threshold)
      idx = node->child_left;
    else
      idx = node->child_right;
  }
}

const short *dtree_rank(const int *fv)
{
#ifdef DTREE_NUM_LEAVES
  int idx = 0;
  while (1) {
    const struct dtree_node *node = &Tree_nodes[idx];
    if (node->feature_idx < 0) {
      int li = Leaf_index[idx];
      if (li < 0) return NULL;  /* defensive */
      return Leaf_ranking[li];
    }
    if (fv[node->feature_idx] <= node->threshold)
      idx = node->child_left;
    else
      idx = node->child_right;
  }
#else
  (void) fv;
  return NULL;
#endif
}

int dtree_num_strats(void)
{
#ifdef DTREE_NUM_STRATS
  return DTREE_NUM_STRATS;
#else
  return 0;
#endif
}

int dtree_num_nodes(void)
{
  return DTREE_NUM_NODES;
}
