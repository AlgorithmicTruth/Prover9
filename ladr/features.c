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

#include "features.h"
#include "memory.h"

/* Private definitions and types */

static Ilist Feature_symbols;  /* list of featured symbols (symnums)*/

/* The following are work arrays, indexed by symnum, used for calculating
   the features of a clause.  They are allocated by init_features() and
   left in place throughout the process.
*/

static int Work_size;         /* size of following arrays */
static int *Pos_occurrences;
static int *Neg_occurrences;
static int *Pos_maxdepth;
static int *Neg_maxdepth;

static int  Feature_count;     /* length of feature vector */
static BOOL *Is_function_sym;  /* Is_function_sym[symnum] = TRUE for functions */
static int  *Feature_vec;      /* reusable feature vector, size Feature_count */

/*************
 *
 *   init_features()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_features(Ilist fsyms, Ilist rsyms)
{
  Ilist p;
  int n;

  Work_size = greatest_symnum() + 1;

  /* printf("init_features: size=%d\n", Work_size); */

  Feature_symbols = ilist_cat(ilist_copy(rsyms), ilist_copy(fsyms));
  Pos_occurrences = safe_calloc(Work_size, sizeof(int));
  Neg_occurrences = safe_calloc(Work_size, sizeof(int));
  Pos_maxdepth    = safe_calloc(Work_size, sizeof(int));
  Neg_maxdepth    = safe_calloc(Work_size, sizeof(int));

  /* Build Is_function_sym cache */
  Is_function_sym = calloc(Work_size, sizeof(BOOL));
  if (!Is_function_sym)
    fatal_error("init_features: calloc Is_function_sym failed");
  for (p = fsyms; p; p = p->next) {
    if (p->i >= 0 && p->i < Work_size)
      Is_function_sym[p->i] = TRUE;
  }

  /* Compute Feature_count and allocate Feature_vec */
  n = 2;  /* pos lits, neg lits */
  for (p = Feature_symbols; p; p = p->next) {
    n += 2;
    if (Is_function_sym[p->i])
      n += 2;
  }
  Feature_count = n;
  Feature_vec = calloc(Feature_count, sizeof(int));
  if (!Feature_vec)
    fatal_error("init_features: calloc Feature_vec failed");
}  /* init_features */

/*************
 *
 *   fill_in_arrays()
 *
 *************/

static
void fill_in_arrays(Term t, BOOL sign, int depth)
{
  if (!VARIABLE(t)) {
    int sn = SYMNUM(t);
    int i;
    if (sn >= Work_size) {
      /* Assume it's a symbol that was added after the start of
	 the search.  If we ignore symbols in features, we may get
	 less discrimination, but all answers should be returned.
       */
      ;  
    }
    else if (sign) {
      Pos_occurrences[sn]++;
      Pos_maxdepth[sn] = IMAX(depth, Pos_maxdepth[sn]);
    }
    else {
      Neg_occurrences[sn]++;
      Neg_maxdepth[sn] = IMAX(depth, Neg_maxdepth[sn]);
    }
    for (i = 0; i < ARITY(t); i++)
      fill_in_arrays(ARG(t,i), sign, depth+1);
  }
}  /* fill_in_arrays */

/*************
 *
 *   features()
 *
 *************/

/* DOCUMENTATION
Given a clause, build the feature vector.

Features:
  positive literals
  negative literals
  foreach relation symbol
     positive occurrences
     negative occurrences
  foreach function symbol
     positive occurrences
     negative occurrences
     positive maxdepth
     negative maxdepth
*/

/* PUBLIC */
int *features(Literals lits)
{
  Ilist p;
  Literals lit;
  int idx = 0;

  Feature_vec[idx++] = positive_literals(lits);
  Feature_vec[idx++] = negative_literals(lits);

  for (lit = lits; lit; lit = lit->next) {
    fill_in_arrays(lit->atom, lit->sign, 0);
  }

  for (p = Feature_symbols; p; p = p->next) {
    Feature_vec[idx++] = Pos_occurrences[p->i];
    Feature_vec[idx++] = Neg_occurrences[p->i];

    if (Is_function_sym[p->i]) {
      Feature_vec[idx++] = Pos_maxdepth[p->i];
      Feature_vec[idx++] = Neg_maxdepth[p->i];
    }

    Pos_occurrences[p->i] = 0;
    Neg_occurrences[p->i] = 0;
    Pos_maxdepth[p->i] = 0;
    Neg_maxdepth[p->i] = 0;
  }
  return Feature_vec;
}  /* features */

/*************
 *
 *   feature_length()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int feature_length(void)
{
  return Feature_count;
}  /* feature_length */

/*************
 *
 *   features_less_or_equal()
 *
 *************/

/* DOCUMENTATION
Return TRUE if Ilists c and d are thr same length and
each member of c is <= the corresponding member of d.
*/

/* PUBLIC */
BOOL features_less_or_equal(int *c, int *d, int len)
{
  int i;
  for (i = 0; i < len; i++) {
    if (c[i] > d[i])
      return FALSE;
  }
  return TRUE;
}  /* features_less_or_equal */

/*************
 *
 *   p_features()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void p_features(int *f)
{
  Ilist p;
  int idx = 0;
  printf("  pos_lits=%d, neg_lits=%d\n", f[0], f[1]);
  idx = 2;

  for (p = Feature_symbols; p; p = p->next) {
    printf("  symbol %s: ", sn_to_str(p->i));
    printf("pos_occ=%d, neg_occ=%d", f[idx], f[idx+1]);
    idx += 2;
    if (Is_function_sym[p->i]) {
      printf(", pos_max=%d, neg_max=%d", f[idx], f[idx+1]);
      idx += 2;
    }
    printf("\n");
  }
}  /* p_features */

