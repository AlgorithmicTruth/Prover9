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

#include "dioph.h"

#ifndef SOLO
#include "clock.h"  /* user_seconds(), for the AC walk budget */
#endif

/*************
 *
 *   gcd(x,y) - greatest common divisor
 *
 *************/

static
int gcd(int x, int y)
{
  int r;
  if (x < y) {r = x; x = y; y = r;}
  r = x % y;
  while (r != 0) {x = y; y = r; r = x % y;}
  return y;
}  /* gcd */

/*************
 *
 *   lcm(x,y) - least common multiple
 *
 *************/

static
int lcm(int x, int y)
{  
  return (x * y) / gcd(x,y);
}  /* lcm */

/*************
 *
 *   less_vec(a1, a2, length) - true iff each component of a1 is <=
 *   the corresponding component of a2
 *
 *************/

static
int less_vec(int *a1, int *a2, int length)
{
  int i;
  for (i = 0; i < length; i++) {
    if (a1[i] > a2[i])
      return 0;
  }
  return 1;
}  /* less_vec */

/*************
 *
 *    var_check_1(constraints, xy, start, stop)
 *
 *    true iff for i=start,...,stop, constraints[i] implies xy[i] <= 1;
 *    For checking basis solutions and combinations of basis solutions.
 *
 *    Otherwise, AC symbol would have to unify with another rigid symbol.
 *
 *************/

static
int var_check_1(int *constraints, int *xy, int start, int stop)
{
  int i;
  for (i = start; i <= stop; i++) {
    if (constraints[i] && xy[i] > 1)
      return 0;
  }
  return 1;
}  /* var_check_1 */

/*************
 *
 *    var_check_2(constraints, xy, start, stop)
 *
 *    TRUE iff for i,j=start,...,stop, 
 *        
 *        constraints[i] && xy[i]  && constraints[j] && xy[j]
 *          implies  constraints[i] = constraints[j] .
 *
 *    Otherwise, variable would have to unify with 2 different symbols.
 *
 *    For checking basis solutions only.
 *
 *************/

static
int var_check_2(int *constraints, int *xy, int start, int stop)
{
  int i, j;
    
  for (i = start; i <= stop; i++) {
    if (constraints[i] && xy[i]) {
      for (j = i+1; j <= stop; j++) {
	if (constraints[j] && xy[j]) {
	  if (constraints[j] != constraints[i])
	    return 0;
	}
      }
    }
  }
  return 1;
}  /* var_check_2 */

/*************
 *
 *    add_solution(xy, length, num_basis, basis)
 *    If no solution in basis is less than xy, then append xy to basis
 *    If there is not enough room, return 0.
 *
 *************/

static
int add_solution(int *xy, int length, int *num_basis, int (*basis)[MAX_COEF])
{
  int i;
  for (i = 0; i < *num_basis; i++)
    if (less_vec(basis[i], xy, length)) 
      return 1;
  if (*num_basis >= MAX_BASIS) {
    return 0;
  }
  for (i = 0; i < length; i++)
    basis[*num_basis][i] = xy[i];
  (*num_basis)++;
  return 1;
}  /* add_solution */

/*************
 *
 *    a_in_bounds(ab,xy,max_y,d,e,m,n,xypos,max_a,max_b,suma,constraints)
 *    Check if a[0],...,a[xypos] is ok:
 *      1. check Huet's (a) condition;
 *      2. check that xy vector is compatible with and constants/functions;
 *      3. set up the max_y vector;
 *      4. check Huet's (b) condition;
 *
 *************/

static
int a_in_bounds(int *ab, int *xy, int *max_y, int (*d)[MAX_COEF],
		int (*e)[MAX_COEF], int m, int n, int xypos, int max_a,
		int max_b, int suma, int *constraints)
{
  int i, j, f, bsum;
  if (xy[xypos] > max_b)  /* Huet's (a) condition */
    return 0;
  if (var_check_1(constraints, xy, 0, m-1) == 0 ||
      var_check_2(constraints, xy, 0, m-1) == 0)
    return 0;
  for (j = m; j < m+n; j++) /* build max_y vector */
    {
      max_y[j] = max_a;
      for (i = 0; i < m; i++)
	if (xy[i] >= d[i][j])
	  {
	    f = e[i][j] - 1;
	    if (f < max_y[j])
	      max_y[j] = f;
	  }
    }
  bsum = 0;
  for (j = m; j < m+n; j++)
    bsum = bsum + ab[j] * max_y[j];

  if (suma <= bsum) /* Huet's (b) condition */
    return 1;
  else
    return 0;
}  /* a_in_bounds */

/*************
 *
 *    b_in_bounds(xy,max_y,constraints,xypos,suma,sumb,m,n,d,e)
 *    Check if b[0],...,b[xypos] is ok:
 *      1. check Huet's (c) and (d) conditions;
 *      2. check that xy vector is compatible with and constants/functions;
 *
 *************/

static
int b_in_bounds(int *xy, int *max_y, int *constraints, int xypos,
		int suma, int sumb, int m, int n)
{
  /* Huet (d) and (c) conditions */
  if (sumb <= suma && xy[xypos] <= max_y[xypos]) 
    /* check constant/function symbol condition */ 
    if (var_check_1(constraints, xy, 0, m+n-1) &&
	var_check_2(constraints, xy, 0, m+n-1)) 
      return 1;
    else
      return 0;
  else
    return 0;
}  /* b_in_bounds */

/*************
 *
 *   int dio()
 *
 *************/

/* DOCUMENTATION
This routine generates the basis of solutions to the homogeneous linear 
diophantine equation given by ab, m, n.  It uses Huet's algorithm
(Information Processing Letters 7(3) 1978).
<P>
The equation has the form a1x1 + ... + amxm  =  b1y1 + ... + bnyn.
<UL>
<LI> ab[] - the vector of coefficients.  1..m is a1..am,  m+1..m+n is b1..bn.
<LI> m, n - the number of a and b coefficients.
<LI> constraints[] - rigid symbol (constant/function)restrictions.
<LI> basis[][] (output) - vector of minimal solutions.
<LI> num_basis (output) - number of minimal solutions.
</UL>
Return value:
<UL>
<LI>    0  - no solution within constraints
<LI>    1  - ok, solutions returned
<LI>   -1  - too many (> MAX_BASIS) base solutions exist
</UL>
*/

/* PUBLIC */
int dio(int ab[MAX_COEF],
	int m, int n,
	int constraints[MAX_COEF],
	int basis[MAX_BASIS][MAX_COEF],
	int *num_basis)
{
  /* max_a, max_b - the maximums of the a's and b's.
   * xy - the vector used to construct solutions.
   * xypos - the current position in the xy vector.
   * suma, sumb - accumulate the sums as the soutions are constructed.
   * max_y - used to hold maximums for the y values.
   * d, e - d[i,j] = lcm(ai,bj) / ai,  e[i,j] = lcm(ai,bj) / bj,  they
   *    are used to construct solutions and for bounds checking.
   */

  int xy[MAX_COEF], max_y[MAX_COEF];
  int d[MAX_COEF][MAX_COEF], e[MAX_COEF][MAX_COEF];
  int xypos, max_a, max_b, suma, sumb;
  int i, j, a, b, t, go_a, go_b, backup;

  if (m == 0 || n == 0) {
    *num_basis = 0;
    return 1;
  }

  max_a = 0;
  max_b = 0;
  for (i = 0; i < m; i++)
    for (j = m; j < m+n; j++) {
      a = ab[i];
      b = ab[j];
      t = lcm(a,b);
      d[i][j] = t / a;
      e[i][j] = t / b;
    }

  for (i = 0; i < m; i++)
    if (ab[i] > max_a)
      max_a = ab[i];

  for (i = m; i < m+n; i++)
    if (ab[i] > max_b)
      max_b = ab[i];

  for (i = 0; i < m+n; i++)
    xy[i] = 0;

  xypos = m - 1;
  go_a = 1;
  suma = 0;
  *num_basis = 0;

  while(go_a) {
    xy[xypos]++;
    suma = suma + ab[xypos];
    if (a_in_bounds(ab,xy,max_y,d,e,m,n,xypos,max_a,max_b,
		    suma,constraints)) {	
      sumb = 0;
      xypos = m + n - 1;
      go_b = 1;
      while (go_b) {
	xy[xypos]++;
	sumb = sumb + ab[xypos];
	if (b_in_bounds(xy,max_y,constraints,xypos,
			suma,sumb,m,n)) {
	  if (suma == sumb) {
	    if (add_solution(xy, m+n, num_basis, basis))
	      backup = 1;
	    else
	      return -1;
	  }
	  else
	    backup = 0;
	}
	else
	  backup = 1;
	if (backup) {
	  sumb = sumb - xy[xypos] * ab[xypos];
	  xy[xypos] = 0;
	  xypos--;
	  if (xypos < m)
	    go_b = 0;
	}
	else
	  xypos = m + n - 1;
      }
      xypos = m - 1;
    }
    else {
      suma = suma - xy[xypos] * ab[xypos];
      xy[xypos] = 0;
      xypos--;
      if (xypos < 0)
	go_a = 0;
    }
  }

  /* Add the special solutions Sij */
  for (i = 0; i < m+n; i++)
    xy[i] = 0;
    
  for (i = 0; i < m; i++)
    for (j = m; j < m+n; j++) {
      xy[i] = d[i][j];
      xy[j] = e[i][j];
      if (var_check_1(constraints,xy,0,m+n-1) &&
	  var_check_2(constraints,xy,0,m+n-1))
	if (!add_solution(xy, m+n, num_basis, basis))
	  return -1;
      xy[i] = 0;
      xy[j] = 0;
    }
  return 1;
}  /* dio */

/* Following macros are for following next_combo routines. */

#define ADD_TO_SUM(sum,basis,i,len) \
{int j,*p; for (j=0,p=basis[i];j<len;j++) sum[j] += p[j];}

#define SUBTRACT_FROM_SUM(sum,basis,i,len) \
{int j,*p; for (j=0,p=basis[i];j<len;j++) sum[j] -= p[j];}

/*************
 *
 *    AC walk budget
 *
 *    The next_combo_* walkers below enumerate subsets of the basis with
 *    no iteration limit of their own: MAX_COMBOS caps the number of
 *    ACCEPTED combinations per enumeration (next_combo_ss), not the
 *    number of subsets VISITED, and unify_ac() multiplies nested
 *    enumerations (each accepted combination spawns AC subproblems with
 *    their own enumerations), so a single backtrack-unification attempt
 *    can run essentially forever (a pathological wt-44 x wt-25
 *    AC-unification wedge case, 2026-07: 18+ CPU-hours inside one
 *    attempt).
 *
 *    The budget below is shared by all walk iterations in one attempt,
 *    across all nesting levels.  unify_bt_first() resets it for each new
 *    attempt; unify_bt_next() restarts the clock (but not the count) for
 *    each new crank.  When the budget is exhausted the walkers report
 *    "no more combinations", and exhaustion is sticky until the next
 *    reset, so the whole nested attempt collapses finitely.  Missing
 *    unifiers only makes AC unification incomplete, which it already is
 *    (MAX_COMBOS, superset restriction); soundness is unaffected.
 *
 *    Defaults are "no limit" so that library users and the SOLO test
 *    harness are unaffected; prover9 enables the budget via the parms
 *    ac_combo_budget and ac_unify_seconds.
 *
 *************/

static long Walk_budget       = -1;  /* iterations per attempt; -1 = no limit */
static int  Walk_seconds      = -1;  /* CPU seconds per crank;  -1 = no limit */
static long Walk_count        = 0;
static double Walk_start      = -1.0;  /* <0 = clock not yet read this crank */
static int  Walk_exhausted    = 0;
static long Walk_abandonments = 0;   /* total attempts abandoned */

/* DOCUMENTATION
Set the AC walk budget: combos is the maximum number of next_combo
iterations per backtrack-unification attempt, and seconds is the
maximum user CPU seconds per crank (call to unify_bt_first/next).
Either can be -1, meaning no limit.
*/

/* PUBLIC */
void set_ac_walk_budget(int combos, int seconds)
{
  Walk_budget = combos;
  Walk_seconds = seconds;
}  /* set_ac_walk_budget */

/* DOCUMENTATION
Current AC walk budget (see set_ac_walk_budget) -- lets a caller that
needs COMPLETE, un-abandoned AC unification (e.g. post-hoc proof
expansion) save the search's setting, lift the limits, and restore.
*/

/* PUBLIC */
void get_ac_walk_budget(int *combos, int *seconds)
{
  *combos = (int) Walk_budget;
  *seconds = Walk_seconds;
}  /* get_ac_walk_budget */

/* DOCUMENTATION
Start a fresh AC walk budget for a new backtrack-unification attempt.
*/

/* PUBLIC */
void reset_ac_walk_budget(void)
{
  Walk_count = 0;
  Walk_exhausted = 0;
  Walk_start = -1.0;
}  /* reset_ac_walk_budget */

/* DOCUMENTATION
Restart the AC walk clock (but not the iteration count) for another
crank of an existing attempt, so that time the caller spends between
unify_bt_next() calls is not charged to the attempt.
*/

/* PUBLIC */
void reclock_ac_walk_budget(void)
{
  Walk_start = -1.0;
}  /* reclock_ac_walk_budget */

/* DOCUMENTATION
Return the number of backtrack-unification attempts abandoned because
the AC walk budget was exhausted.
*/

/* PUBLIC */
long ac_walk_abandonments(void)
{
  return Walk_abandonments;
}  /* ac_walk_abandonments */

/*************
 *
 *    walk_budget_spent()
 *
 *    Charge one walker iteration against the budget.  Return 1 if the
 *    budget is exhausted (the walker should report no more combos).
 *    The CPU clock is read lazily, every 16384 iterations, so attempts
 *    that never walk that far never pay for a clock call.
 *
 *************/

static
int walk_budget_spent(void)
{
  if (Walk_exhausted)
    return 1;
  Walk_count++;
  if (Walk_budget >= 0 && Walk_count > Walk_budget)
    Walk_exhausted = 1;
#ifndef SOLO
  else if (Walk_seconds >= 0 && (Walk_count & 0x3FFF) == 0) {
    if (Walk_start < 0)
      Walk_start = user_seconds();
    else if (user_seconds() - Walk_start > Walk_seconds)
      Walk_exhausted = 1;
  }
#endif
  if (Walk_exhausted) {
    Walk_abandonments++;
    if (Walk_abandonments <= 20)
      printf("ac_walk_budget: abandoning AC unification attempt"
	     " (%ld iterations).%s\n", Walk_count,
	     Walk_abandonments == 20 ?
	     "  (Further messages suppressed; see stats.)" : "");
    return 1;
  }
  return 0;
}  /* walk_budget_spent */

/*************
 *
 *    next_combo_a
 *
 *************/

/* DOCUMENTATION
This routine gets the first or next appropriate subset of the
basis of solutions.  "Appropriate" means that each variable gets
instantiated to something, and there are no top-level rigid
symbol clashes.  I think of this as a potential unifier, because
he caller still has to worry about recursive unification of subterms.
<UL>
<LI> length -- total number of coefficients (m+n).
<LI> basis[][] -- basis of solutions.
<LI> num_basis -- number of basis solutions.
<LI> constraints[] -- rigid symbol constraints.
<LI> combo[] (input and output) -- current subset of the basis.
<LI> sum[]   (intput and output) -- sum corresponding to combo[].
<LI> start_flag -- 1 for first call, 0 for subsequent calls.
</UL>
We have several algorithms to do this.  This implements algorithm A.
(For most practical work, the differences in performance are small.)
*/

/* PUBLIC */
int next_combo_a(int length, int basis[MAX_BASIS][MAX_COEF],
		 int num_basis, int constraints[MAX_COEF],
		 int combo[MAX_BASIS], int sum[MAX_COEF],
		 int start_flag)
{
  int go, pos, i, success;

  if (start_flag) {
    for (i = 0; i < length; i++)
      sum[i] = 0;
    for (i = 0; i < num_basis; i++)
      combo[i] = 0;
  }

  success = 0;
  pos = num_basis-1;
  go = (pos >= 0);
  while (go && !success) {
    int backup = 1;
    if (walk_budget_spent())
      return 0;
    if (!combo[pos]) {
      combo[pos] = 1;  /* All following positions 0. */
      ADD_TO_SUM(sum, basis, pos, length);
      if (var_check_1(constraints, sum, 0, length-1)) {
	/* OK if no component is 0. */
	success = 1;
	for (i = 0; i < length && success; i++)
	  if (sum[i] == 0)
	    success = 0;
	backup = 0;
      }
    }
    if (backup) {
      combo[pos] = 0;
      SUBTRACT_FROM_SUM(sum, basis, pos, length);
      pos--;
      go = (pos >= 0);
    }
    else
      pos = num_basis-1;
  }
  return success;
}  /* next_combo_a */

/*************
 *
 *    next_combo_b
 *
 *    Find the first or next appropriate subset of the basis.
 *    combo is the current subset, and
 *    sum is the solution corresponding to combo.
 *
 *************/

/* DOCUMENTATION
This routine gets the first or next appropriate subset of the
basis of solutions.  This implements algorithm B.
See next_combo_a() for a description.
*/

/* PUBLIC */
int next_combo_b(int length, int basis[MAX_BASIS][MAX_COEF],
		 int num_basis, int constraints[MAX_COEF],
		 int combo[MAX_BASIS], int sum[MAX_COEF],
		 int start_flag)
{
  int go, pos, i, success;

  if (start_flag) {
    for (i = 0; i < length; i++)
      sum[i] = 0;
    for (i = 0; i < num_basis; i++)
      combo[i] = 0;
    pos = -1;
  }
  else {
    pos = num_basis-1;
    while (pos >= 0 && !combo[pos])
      pos--;
    combo[pos] = 0;
    SUBTRACT_FROM_SUM(sum, basis, pos, length);
  }

  success = 0; go = 1;

  while (go && !success) {
    if (walk_budget_spent())
      return 0;
    if (pos == num_basis-1) {
      success = 1;
      for (i = 0; i < length && success; i++)
	if (sum[i] == 0)
	  success = 0;

      if (!success) {
	while (pos >= 0 && !combo[pos])
	  pos--;
	if (pos < 0)
	  go = 0;
	else {
	  combo[pos] = 0;
	  SUBTRACT_FROM_SUM(sum, basis, pos, length);
	}
      }
    }
    else {
      pos++;
      combo[pos] = 1;
      ADD_TO_SUM(sum, basis, pos, length);
      if (!var_check_1(constraints, sum, 0, length-1)) {
	combo[pos] = 0;
	SUBTRACT_FROM_SUM(sum, basis, pos, length);
      }
    }
  }
  return success;
}  /* next_combo_b */

/*************
 *
 *    next_combo_c  -- Hullot's algorithm
 *
 *    Find the first or next appropriate subset of the basis.
 *
 *************/

#define DOWN    1
#define OVER    2
#define BACKUP  3
#define SUCCESS 4
#define FAILURE 5

/* DOCUMENTATION
This routine gets the first or next appropriate subset of the
basis of solutions.  This implements algorithm C.
See next_combo_a() for a description.
*/

/* PUBLIC */
int next_combo_c(int length, int basis[MAX_BASIS][MAX_COEF],
		 int num_basis, int constraints[MAX_COEF],
		 int combo[MAX_BASIS], int sum[MAX_COEF],
		 int start_flag)
{
  int pos, i, status, ok;

  if (start_flag) {
    for (i = 0; i < length; i++)
      sum[i] = 0;
    /* set combo[] to root pattern */
    for (i = 0; i < num_basis; i++) {
      combo[i] = 1;
      ADD_TO_SUM(sum, basis, i, length);
    }
    pos = -1;  /* pos, which is index into combo[], also = level-1 */
    /* Fail if a column of basis is all 0 (if not big enough). */
    for (i = 0, ok = 1; i < length && ok; i++)
      if (sum[i] == 0)
	ok = 0;
    status = (ok ? DOWN : FAILURE);
  }
  else {
    /* use combo[] from previous call */
    pos = num_basis-1;  /* leaf */
    status = BACKUP;
  }

  while (status != SUCCESS && status != FAILURE) {
    if (walk_budget_spent())
      return 0;
    if (status == DOWN) {
      /* go to left child */
      if (pos == -1 || combo[pos] == 0) {
	/* parent is a left child */
	pos++;
	combo[pos] = 0;
	SUBTRACT_FROM_SUM(sum, basis, pos, length);
      }
      else {
	pos++;
	for (i = pos+1; i < num_basis; i++) {
	  combo[i] = 1;
	  ADD_TO_SUM(sum, basis, i, length);
	}
      }
      /* if big enough */
      for (i = 0, ok = 1; i < length && ok; i++)
	if (sum[i] == 0)
	  ok = 0;
      if (ok)
	status = (pos == num_basis-1) ? SUCCESS : DOWN;
      else
	status = OVER;
    }
    else if (status == OVER) {
      /* go to (right) sibling */
      combo[pos] = 1;
      ADD_TO_SUM(sum, basis, pos, length);
      for (i = pos+1; i < num_basis; i++) {
	if (combo[i]) {
	  combo[i] = 0;
	  SUBTRACT_FROM_SUM(sum, basis, i, length);
	}
      }
      /* if small enough */
      if (var_check_1(constraints, sum, 0, length-1))
	status = (pos == num_basis-1) ? SUCCESS : DOWN;
      else
	status = BACKUP;
    }
    else if (status == BACKUP) {
      /* go to nearest ancestor that has a right sibling */
      while (pos >= 0 && combo[pos])
	pos--;
      status = (pos < 0 ? FAILURE : OVER);
    }
  }
  return status == SUCCESS ? 1 : 0;
}  /* next_combo_c */

/*************
 *
 *    superset_degree_bits / pack_combo_bits
 *
 *    Bitset replacement for the old int-array superset_degree(a,b,n):
 *    if a is not a superset of b (over the low n bits), return -1,
 *    else return |a-b|.  Same result, O(SS_WORDS) word ops instead of
 *    O(n) int compares -- n is bounded by MAX_BASIS (100), so this
 *    turns an O(B) inner test into an O(1) one (2 words).
 *
 *************/

#define SS_WORD_BITS (8 * (int) sizeof(unsigned long long))
#define SS_WORDS ((MAX_BASIS + SS_WORD_BITS - 1) / SS_WORD_BITS)

static
void pack_combo_bits(int *combo, int n, unsigned long long *bits)
{
  int i;
  for (i = 0; i < SS_WORDS; i++)
    bits[i] = 0;
  for (i = 0; i < n; i++)
    if (combo[i])
      bits[i / SS_WORD_BITS] |= (1ULL << (i % SS_WORD_BITS));
}  /* pack_combo_bits */

static
int superset_degree_bits(unsigned long long *abits, unsigned long long *bbits)
{
  int w, c;
  for (w = 0; w < SS_WORDS; w++)
    if (bbits[w] & ~abits[w])
      return -1;
  for (w = 0, c = 0; w < SS_WORDS; w++)
    c += __builtin_popcountll(abits[w] & ~bbits[w]);
  return c;
}  /* superset_degree_bits */

/*************
 *
 *    next_combo_ss
 *
 *************/

/* DOCUMENTATION
This routine gets the first or next appropriate subset of the
basis of solutions, subject to the "supserset restriction".
It appears to work like the other next_combo routines,
but it is not really incremental.  To implement the superset
restriction, we collect, in combos[] during the first call,
up to MAX_COMBOS subsets satisfying the restriction, then
give them out in the subsequent calls.  The first bunch of
parameters are the same as for the other next_combo routines.
<UL>
<LI> length -- total number of coefficients (m+n).
<LI> basis[][] -- basis of solutions.
<LI> num_basis -- number of basis solutions.
<LI> constraints[] -- rigid symbol constraints.
<LI> combo[] (input and output) -- current subset of the basis.
<LI> sum[]   (intput and output) -- sum corresponding to combo[].
<LI> start_flag -- 1 for first call, 0 for subsequent calls.
</UL>
The rest of the parameters are added for the supserset restriction.
<UL>
<LI> combos[][] (input and output) -- this is really just temp storage.
<LI> *np (input and output) -- temp storage (# of combos remaining).
<LI> ss_parm (input) -- supserset parameter [0...]
</UL>
*/

/* PUBLIC */
int next_combo_ss(int length, int basis[MAX_BASIS][MAX_COEF],
		  int num_basis, int constraints[MAX_COEF],
		  int combo[MAX_BASIS], int sum[MAX_COEF],
		  int start_flag,
		  int combos[MAX_COMBOS][MAX_BASIS],
		  int *np,
		  int ss_parm)
{
  int i, go, ok;

  if (start_flag) {
    /* Bitset cache of accepted combos, parallel to combos[][]: turns
       the O(*np) inner loop's per-comparison cost from O(num_basis)
       (superset_degree) into O(1) (superset_degree_bits).  Local, not
       static: next_combo_ss's setup phase is self-contained per call,
       so this stays reentrancy-safe. */
    unsigned long long combos_bits[MAX_COMBOS][SS_WORDS];
    unsigned long long combo_bits[SS_WORDS];

    *np = 0;
    go = next_combo_a(length,basis,num_basis,constraints,combo,sum,1);
    while (go) {
      pack_combo_bits(combo, num_basis, combo_bits);
      for (i=0, ok = 1; i < *np && ok; i++)
	/* 0 means basic superset test */
	/* n means allow supersets that have n more elements. */
	if (superset_degree_bits(combo_bits, combos_bits[i]) > ss_parm)
	  ok = 0;

      if (ok) {
	if (*np == MAX_COMBOS) {
	  printf("next_combo_ss: MAX_COMBOS.\n");
	  go = 0;
	}
	else {
	  for (i=0; i<num_basis; i++)
	    combos[*np][i] = combo[i];
	  for (i=0; i<SS_WORDS; i++)
	    combos_bits[*np][i] = combo_bits[i];
	  (*np)++;
	}
      }

      if (go)
	go = next_combo_a(length,basis,num_basis,constraints,combo,sum,0);
    }
  }
    
  if (*np > 0) {
    (*np)--;
    for (i=0; i<num_basis; i++)
      combo[i] = combos[*np][i];
    return 1;
  }
  else
    return 0;

}  /* next_combo_ss */

/*************
 *
 *    p_ac_basis()
 *
 *    Print the basis of solutions
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) a basis of solutions.
*/

/* PUBLIC */
void p_ac_basis(int basis[MAX_BASIS][MAX_COEF],
		int num_basis, int m, int n)
{
  int i, j;
  printf("\nBasis has %d solutions.\n",num_basis);
  for (i = 0; i < num_basis; i++) {
    for (j = 0; j < m+n; j++) printf("%3d",basis[i][j]);
    printf("\n");
  }
  printf("Basis has %d solutions.\n",num_basis);
}  /* p_ac_basis */

/*************
 *
 *    all_combos
 *
 *    For debugging only.  Find all the appropriate subsets and
 *    print a unifier for each.
 *
 *************/

#ifdef SOLO
static
int all_combos(int m, int n, int basis[MAX_BASIS][MAX_COEF], int num_basis,
	       int constraints[MAX_COEF], int (*proc) (/* ??? */))
{
  int combo[MAX_BASIS], sum[MAX_COEF];
  int count, j, ok;
    
  count = 0;
  ok = (*proc)(m+n, basis, num_basis, constraints, combo, sum, 1);
  while (ok) {
    count++;
#if 1
    for (j = 0; j < num_basis; j++)
      printf("%d ", combo[j]);
    printf("--------------\n");
#if 1
    {
      int i, k;
      for (i = 0; i < m+n; i++) {
	if (constraints[i])
	  printf(" %c = ", constraints[i]+'A'-1);
	else
	  printf("x%d -> ", i);
	for (j = 0; j < num_basis; j++)
	  if (combo[j])
	    for (k = 0; k < basis[j][i]; k++)
	      printf("z%d ", j);
	printf("\n");
      }
    }
#endif
#endif
    ok = (*proc)(m+n, basis, num_basis, constraints, combo, sum, 0);
  }
  return count;
}  /* all_combos */
#endif

#ifdef SOLO

/*************
 *
 *   main
 *
 *************/

int main(int argc, char **argv)
{
  int m, n, num_basis;
  int ab[MAX_COEF], constraints[MAX_COEF], basis[MAX_BASIS][MAX_COEF];
  int i;
  unsigned long t0, t1, t2, t3;
    
  printf("\nThe equation is A1X1 + ... + AmXm = B1Y1 + ... + BnYn.\n\n");
  printf("Enter m and n, the number of terms on each side: ");
  scanf("%d %d", &m, &n);
    
  if (m+n > MAX_COEF) {
    printf("maximum m+n is %d\n", MAX_COEF);
    exit(2);
  }
  printf("Enter the %d A coefficients and the %d B coefficients: ", m, n);
  for (i=0; i<m+n; i++) scanf("%d", &ab[i]);
    
  printf("Enter corresponding constraints for rigid symbols.\n");
  printf("0 means variable, use different positive integers for\n");
  printf("different nonvariable terms: ");
  for (i=0; i<m+n; i++) scanf("%d", &constraints[i]);
    
  printf("\na = "); for (i=0; i<m; i++) printf("%3d ", ab[i]);
  printf("  b = "); for (i=m; i<m+n; i++) printf("%3d ", ab[i]);
  printf("\n");
    
  printf("    "); for (i=0; i<m; i++) printf("%3d ", constraints[i]);
  printf("      "); for (i=m; i<m+n; i++) printf("%3d ", constraints[i]);
  printf("\n");
    
  num_basis = 0;
    
  t0 = clock();
  dio(ab, m, n, constraints, basis, &num_basis);
  t1 = clock();
  p_ac_basis(basis, num_basis, m, n);
  printf("dio time = %.2f\n", (t1-t0)/1000000.);
    
  if (num_basis > 0) {

    t2 = clock();
    i = all_combos(m, n, basis, num_basis, constraints, next_combo_a);
    t3 = clock();
    printf("\nNumber of unifiers is %d\n", i);
    printf("next_combo_a time = %.2f\n", (t3-t2)/1000000.);

#if 0
    t2 = clock();
    t2 = clock();
    i = all_combos(m, n, basis, num_basis, constraints, next_combo_b);
    t3 = clock();
    printf("\nNumber of unifiers is %d\n", i);
    printf("next_combo_b time = %.2f\n", (t3-t2)/1000000.);

    t2 = clock();
    i = all_combos(m, n, basis, num_basis, constraints, next_combo_c);
    t3 = clock();
    printf("\nNumber of unifiers is %d\n", i);
    printf("next_combo_c time = %.2f\n", (t3-t2)/1000000.);
#endif		
  }
  return 0;
}  /* main */

#endif
