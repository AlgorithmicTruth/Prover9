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

#include "just.h"

/* Private definitions and types */

/*
 * memory management
 */

#define PTRS_JUST PTRS(sizeof(struct just))
static unsigned Just_gets, Just_frees;

#define PTRS_PARAJUST PTRS(sizeof(struct parajust))
static unsigned Parajust_gets, Parajust_frees;

#define PTRS_INSTANCEJUST PTRS(sizeof(struct instancejust))
static unsigned Instancejust_gets, Instancejust_frees;

#define PTRS_IVYJUST PTRS(sizeof(struct ivyjust))
static unsigned Ivyjust_gets, Ivyjust_frees;

/*************
 *
 *   Just get_just()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Just get_just(void)
{
  Just p = get_cmem(PTRS_JUST);
  Just_gets++;
  return(p);
}  /* get_just */

/*************
 *
 *    free_just()
 *
 *************/

static
void free_just(Just p)
{
  free_mem(p, PTRS_JUST);
  Just_frees++;
}  /* free_just */

/*************
 *
 *   Parajust get_parajust()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Parajust get_parajust(void)
{
  Parajust p = get_cmem(PTRS_PARAJUST);
  Parajust_gets++;
  return(p);
}  /* get_parajust */

/*************
 *
 *    free_parajust()
 *
 *************/

static
void free_parajust(Parajust p)
{
  free_mem(p, PTRS_PARAJUST);
  Parajust_frees++;
}  /* free_parajust */

/*************
 *
 *   Instancejust get_instancejust()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Instancejust get_instancejust(void)
{
  Instancejust p = get_cmem(PTRS_INSTANCEJUST);
  Instancejust_gets++;
  return(p);
}  /* get_instancejust */

/*************
 *
 *    free_instancejust()
 *
 *************/

static
void free_instancejust(Instancejust p)
{
  free_mem(p, PTRS_INSTANCEJUST);
  Instancejust_frees++;
}  /* free_instancejust */

/*************
 *
 *   Ivyjust get_ivyjust()
 *
 *************/

static
Ivyjust get_ivyjust(void)
{
  Ivyjust p = get_mem(PTRS_IVYJUST);
  Ivyjust_gets++;
  return(p);
}  /* get_ivyjust */

/*************
 *
 *    free_ivyjust()
 *
 *************/

static
void free_ivyjust(Ivyjust p)
{
  free_mem(p, PTRS_IVYJUST);
  Ivyjust_frees++;
}  /* free_ivyjust */

/*************
 *
 *   fprint_just_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for data types
associated with the just package.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_just_mem(FILE *fp, BOOL heading)
{
  int n;
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");

  n = sizeof(struct just);
  fprintf(fp, "just (%4d)         %11u%11u%11u%9.1f K\n",
          n, Just_gets, Just_frees,
          Just_gets - Just_frees,
          ((Just_gets - Just_frees) * n) / 1024.);

  n = sizeof(struct parajust);
  fprintf(fp, "parajust (%4d)     %11u%11u%11u%9.1f K\n",
          n, Parajust_gets, Parajust_frees,
          Parajust_gets - Parajust_frees,
          ((Parajust_gets - Parajust_frees) * n) / 1024.);

  n = sizeof(struct instancejust);
  fprintf(fp, "instancejust (%4d) %11u%11u%11u%9.1f K\n",
          n, Instancejust_gets, Instancejust_frees,
          Instancejust_gets - Instancejust_frees,
          ((Instancejust_gets - Instancejust_frees) * n) / 1024.);

  n = sizeof(struct ivyjust);
  fprintf(fp, "ivyjust (%4d)      %11u%11u%11u%9.1f K\n",
          n, Ivyjust_gets, Ivyjust_frees,
          Ivyjust_gets - Ivyjust_frees,
          ((Ivyjust_gets - Ivyjust_frees) * n) / 1024.);

}  /* fprint_just_mem */

/*************
 *
 *   p_just_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) memory usage statistics for data types
associated with the just package.
*/

/* PUBLIC */
void p_just_mem()
{
  fprint_just_mem(stdout, TRUE);
}  /* p_just_mem */

/*
 *  end of memory management
 */

/*************
 *
 *   ivy_just()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Just ivy_just(Just_type type,
	      int parent1, Ilist pos1,
	      int parent2, Ilist pos2,
	      Plist pairs)
{
  Just j = get_just();
  j->type = IVY_JUST;
  j->u.ivy = get_ivyjust();
  j->u.ivy->type = type;
  j->u.ivy->parent1 = parent1;
  j->u.ivy->parent2 = parent2;
  j->u.ivy->pos1 = pos1;
  j->u.ivy->pos2 = pos2;
  j->u.ivy->pairs = pairs;
  return j;
}  /* ivy_just */

/*************
 *
 *   input_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for input.
*/

/* PUBLIC */
Just input_just(void)
{
  /* (INPUT_JUST) */
  Just j = get_just();
  j->type = INPUT_JUST;
  return j;
}  /* input_just */

/*************
 *
 *   goal_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for goal.
*/

/* PUBLIC */
Just goal_just(void)
{
  /* (GOAL_JUST) */
  Just j = get_just();
  j->type = GOAL_JUST;
  return j;
}  /* goal_just */

/*************
 *
 *   deny_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for deny.
*/

/* PUBLIC */
Just deny_just(Topform tf)
{
  /* (DENY_JUST) */
  Just j = get_just();
  j->type = DENY_JUST;
  j->u.id = tf->id;
  return j;
}  /* deny_just */

/*************
 *
 *   clausify_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for clausify.
*/

/* PUBLIC */
Just clausify_just(Topform tf)
{
  /* (CLAUSIFY_JUST) */
  Just j = get_just();
  j->type = CLAUSIFY_JUST;
  j->u.id = tf->id;
  return j;
}  /* clausify_just */

/*************
 *
 *   expand_def_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for expand_def.
*/

/* PUBLIC */
Just expand_def_just(Topform tf, Topform def)
{
  /* (expand_def_JUST) */
  Just j = get_just();
  j->type = EXPAND_DEF_JUST;
  j->u.lst = ilist_append(ilist_append(NULL, tf->id), def->id);
  return j;
}  /* expand_def_just */

/*************
 *
 *   copy_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for copy.
*/

/* PUBLIC */
Just copy_just(Topform c)
{
  /* (COPY_JUST parent_id) */
  Just j = get_just();
  j->type = COPY_JUST;
  j->u.id = c->id;
  return j;
}  /* copy_just */

/*************
 *
 *   propositional_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for propositional.
*/

/* PUBLIC */
Just propositional_just(Topform c)
{
  /* (PROPOSITIONAL_JUST parent_id) */
  Just j = get_just();
  j->type = PROPOSITIONAL_JUST;
  j->u.id = c->id;
  return j;
}  /* propositional_just */

/*************
 *
 *   new_symbol_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for new_symbol inference.
*/

/* PUBLIC */
Just new_symbol_just(Topform c)
{
  /* (NEW_SYMBOL_JUST parent_id) */
  Just j = get_just();
  j->type = NEW_SYMBOL_JUST;
  j->u.id = c->id;
  return j;
}  /* new_symbol_just */

/*************
 *
 *   back_demod_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for back_demod.
*/

/* PUBLIC */
Just back_demod_just(Topform c)
{
  /* (BACK_DEMOD_JUST parent_id) */
  Just j = get_just();
  j->type = BACK_DEMOD_JUST;
  j->u.id = c->id;
  return j;
}  /* back_demod_just */

/*************
 *
 *   back_unit_deletion_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for back_unit_deletion.
*/

/* PUBLIC */
Just back_unit_deletion_just(Topform c)
{
  /* (BACK_UNIT_DEL_JUST parent_id) */
  Just j = get_just();
  j->type = BACK_UNIT_DEL_JUST;
  j->u.id = c->id;
  return j;
}  /* back_unit_deletion_just */

/*************
 *
 *   binary_res_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for binary resolution.
(Binary res justifications may also be constructed in resolve(), along
with hyper and UR.)
*/

/* PUBLIC */
Just binary_res_just(Topform c1, int n1, Topform c2, int n2)
{
  /* (BINARY_RES_JUST (id1 lit1 id2 lit2) */
  Just j = get_just();
  j->type = BINARY_RES_JUST;
  j->u.lst = ilist_append(
                  ilist_append(
                       ilist_append(
                            ilist_append(NULL,c1->id),n1),c2->id),n2);

  return j;
}  /* binary_res_just */

/*************
 *
 *   binary_res_just_by_id()
 *
 *************/

/* DOCUMENTATION
Similar to binary_res_just, except that IDs are given instead of clauses.
*/

/* PUBLIC */
Just binary_res_just_by_id(int c1, int n1, int c2, int n2)
{
  /* (BINARY_RES_JUST (id1 lit1 id2 lit2) */
  Just j = get_just();
  j->type = BINARY_RES_JUST;
  j->u.lst = ilist_append(
                  ilist_append(
                       ilist_append(
                            ilist_append(NULL,c1),n1),c2),n2);

  return j;
}  /* binary_res_just_by_id */

/*************
 *
 *   factor_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for a factorization.
*/

/* PUBLIC */
Just factor_just(Topform c, int lit1, int lit2)
{
  /* (FACTOR_JUST (clause_id lit1 lit2)) */
  Just j = get_just();
  j->type = FACTOR_JUST;
  j->u.lst = ilist_append(ilist_append(ilist_append(NULL,c->id),lit1),lit2);
  return j;
}  /* factor_just */

/*************
 *
 *   xxres_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for resolution with x=x.
*/

/* PUBLIC */
Just xxres_just(Topform c, int lit)
{
  /* (XXRES_JUST (clause_id lit)) */
  Just j = get_just();
  j->type = XXRES_JUST;
  j->u.lst = ilist_append(ilist_append(NULL,c->id),lit);
  return j;
}  /* xxres_just */

/*************
 *
 *   resolve_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification for resolution rules.
This handles binary, hyper, ur, and maybe others.
*/

/* PUBLIC */
Just resolve_just(Ilist g, Just_type type)
{
  Just j = get_just();
  j->type = type;
  j->u.lst = g;
  return j;
}  /* resolve_just */

/*************
 *
 *   demod_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification for a demodulation.
*/

/* PUBLIC */
Just demod_just(I3list steps)
{
  Just j = get_just();
  j->type = DEMOD_JUST;
  j->u.demod = steps;
  return j;
}  /* demod_just */

/*************
 *
 *   para_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for a paramodulation
inference.  The position vectors are not copied.
*/

/* PUBLIC */
Just para_just(Just_type rule,
	       Topform from, Ilist from_vec,
	       Topform into, Ilist into_vec)
{
  Just j = get_just();
  j->type = rule;
  j->u.para = get_parajust();

  j->u.para->from_id = from->id;
  j->u.para->into_id = into->id;
  j->u.para->from_pos = from_vec;
  j->u.para->into_pos = into_vec;

  return j;
}  /* para_just */

/*************
 *
 *   instance_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for an instance
inference.  The list of pairs is not copied.
*/

/* PUBLIC */
Just instance_just(Topform parent, Plist pairs)
{
  Just j = get_just();
  j->type = INSTANCE_JUST;
  j->u.instance = get_instancejust();

  j->u.instance->parent_id = parent->id;
  j->u.instance->pairs = pairs;
  
  return j;
}  /* instance_just */

/*************
 *
 *   para_just_rev_copy()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for a paramodulation
inference.  The position vectors are copied and reversed.
*/

/* PUBLIC */
Just para_just_rev_copy(Just_type rule,
			Topform from, Ilist from_vec,
			Topform into, Ilist into_vec)
{
  return para_just(rule,
		   from, reverse_ilist(copy_ilist(from_vec)),
		   into, reverse_ilist(copy_ilist(into_vec)));
}  /* para_just_rev_copy */

/*************
 *
 *   unit_del_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification list for a factorization.
*/

/* PUBLIC */
Just unit_del_just(Topform deleter, int literal_num)
{
  /* UNIT_DEL (literal-num clause-id) */
  Just j = get_just();
  j->type = UNIT_DEL_JUST;
  j->u.lst = ilist_append(ilist_append(NULL, literal_num), deleter->id);
  return j;
}  /* cd_just */

/*************
 *
 *   flip_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification for equality flipping.
*/

/* PUBLIC */
Just flip_just(int n)
{
  Just j = get_just();
  j->type = FLIP_JUST;
  j->u.id = n;
  return j;
}  /* flip_just */

/*************
 *
 *   xx_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification for the XX rule,
which removes literals that are instances of x!=x.
*/

/* PUBLIC */
Just xx_just(int n)
{
  Just j = get_just();
  j->type = XX_JUST;
  j->u.id = n;
  return j;
}  /* xx_just */

/*************
 *
 *   merge_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification for the merging
a literal.  The n-th literal has been removed because it is
identical to another literal.
*/

/* PUBLIC */
Just merge_just(int n)
{
  Just j = get_just();
  j->type = MERGE_JUST;
  j->u.id = n;
  return j;
}  /* merge_just */

/*************
 *
 *   eval_just()
 *
 *************/

/* DOCUMENTATION
This routine builds and returns a justification for an eval rewrite.
The argument is the number of rewrites.
*/

/* PUBLIC */
Just eval_just(int n)
{
  Just j = get_just();
  j->type = EVAL_JUST;
  j->u.id = n;
  return j;
}  /* eval_just */

/*************
 *
 *   append_just()
 *
 *************/

/* DOCUMENTATION
This appends two justifications.  No copying occurs.
*/

/* PUBLIC */
Just append_just(Just j1, Just j2)
{
  if (j1 == NULL)
    return j2;
  else {
    Just p = j1;
    while (p->next != NULL)
      p = p->next;
    p->next = j2;
    return j1;
  }
}  /* append_just */

/*************
 *
 *   copy_justification()
 *
 *************/

/* DOCUMENTATION
Copy a justification.
*/

/* PUBLIC */
Just copy_justification(Just j)
{
  Just head = NULL;
  Just *tail = &head;
  while (j != NULL) {
    Just j2 = get_just();
    j2->type = j->type;
    j2->next = NULL;
    switch (j->type) {
    case INPUT_JUST:
    case GOAL_JUST:
      break;
    case DENY_JUST:
    case CLAUSIFY_JUST:
    case COPY_JUST:
    case PROPOSITIONAL_JUST:
    case NEW_SYMBOL_JUST:
    case BACK_DEMOD_JUST:
    case BACK_UNIT_DEL_JUST:
    case FLIP_JUST:
    case XX_JUST:
    case MERGE_JUST:
    case EVAL_JUST:
      j2->u.id = j->u.id;
      break;
    case EXPAND_DEF_JUST:
    case BINARY_RES_JUST:
    case HYPER_RES_JUST:
    case UR_RES_JUST:
    case UNIT_DEL_JUST:
    case FACTOR_JUST:
    case XXRES_JUST:
      j2->u.lst = copy_ilist(j->u.lst);
      break;
    case DEMOD_JUST:
      j2->u.demod = copy_i3list(j->u.demod);
      break;
    case PARA_JUST:
    case PARA_FX_JUST:
    case PARA_IX_JUST:
    case PARA_FX_IX_JUST:
      j2->u.para = get_parajust();
      j2->u.para->from_id = j->u.para->from_id;
      j2->u.para->into_id = j->u.para->into_id;
      j2->u.para->from_pos = copy_ilist(j->u.para->from_pos);
      j2->u.para->into_pos = copy_ilist(j->u.para->into_pos);
      break;
    case INSTANCE_JUST:
      j2->u.instance = get_instancejust();
      j2->u.instance->parent_id = j->u.instance->parent_id;
      j2->u.instance->pairs = copy_plist_of_terms(j->u.instance->pairs);
      break;
    case IVY_JUST:
      j2->u.ivy = get_ivyjust();
      j2->u.ivy->type = j->u.ivy->type;
      j2->u.ivy->parent1 = j->u.ivy->parent1;
      j2->u.ivy->parent2 = j->u.ivy->parent2;
      j2->u.ivy->pos1 = copy_ilist(j->u.ivy->pos1);
      j2->u.ivy->pos2 = copy_ilist(j->u.ivy->pos2);
      j2->u.ivy->pairs = copy_plist_of_terms(j->u.ivy->pairs);
      break;
    default: fatal_error("copy_justification: unknown type");
    }
    *tail = j2;
    tail = &j2->next;
    j = j->next;
  }
  return head;
}  /* copy_justification */

/*************
 *
 *   jstring() - strings for printing justifications
 *
 *************/

/* DOCUMENTATION
What is the string, e.g., "resolve" associated with a justification node?
*/

/* PUBLIC */
char *jstring(Just j)
{
  switch (j->type) {

    /* primary justifications */

  case INPUT_JUST:         return "assumption";
  case GOAL_JUST:          return "goal";
  case DENY_JUST:          return "deny";
  case CLAUSIFY_JUST:      return "clausify";
  case COPY_JUST:          return "copy";
  case PROPOSITIONAL_JUST: return "propositional";
  case NEW_SYMBOL_JUST:    return "new_symbol";
  case BACK_DEMOD_JUST:    return "back_rewrite";
  case BACK_UNIT_DEL_JUST: return "back_unit_del";
  case EXPAND_DEF_JUST:    return "expand_def";
  case BINARY_RES_JUST:    return "resolve";
  case HYPER_RES_JUST:     return "hyper";
  case UR_RES_JUST:        return "ur";
  case FACTOR_JUST:        return "factor";
  case XXRES_JUST:         return "xx_res";
  case PARA_JUST:          return "para";
  case PARA_FX_JUST:       return "para_fx";
  case PARA_IX_JUST:       return "para_ix";
  case PARA_FX_IX_JUST:    return "para_fx_ix";
  case INSTANCE_JUST:      return "instantiate";
  case IVY_JUST:           return "ivy";

    /* secondary justifications */

  case FLIP_JUST:          return "flip";
  case XX_JUST:            return "xx";
  case MERGE_JUST:         return "merge";
  case EVAL_JUST:          return "eval";
  case DEMOD_JUST:         return "rewrite";
  case UNIT_DEL_JUST:      return "unit_del";
  case UNKNOWN_JUST:       return "unknown";
  }
  return "unknown";
}  /* jstring */

/*************
 *
 *   jstring_to_jtype() - strings for printing justifications
 *
 *************/

static
int jstring_to_jtype(char *s)
{
  if (str_ident(s, "assumption"))
    return INPUT_JUST;
  else if (str_ident(s, "goal"))
    return GOAL_JUST;
  else if (str_ident(s, "deny"))
    return DENY_JUST;
  else if (str_ident(s, "clausify"))
    return CLAUSIFY_JUST;
  else if (str_ident(s, "copy"))
    return COPY_JUST;
  else if (str_ident(s, "propositional"))
    return PROPOSITIONAL_JUST;
  else if (str_ident(s, "new_symbol"))
    return NEW_SYMBOL_JUST;
  else if (str_ident(s, "back_rewrite"))
    return BACK_DEMOD_JUST;
  else if (str_ident(s, "back_unit_del"))
    return BACK_UNIT_DEL_JUST;
  else if (str_ident(s, "expand_def"))
    return EXPAND_DEF_JUST;
  else if (str_ident(s, "resolve"))
    return BINARY_RES_JUST;
  else if (str_ident(s, "hyper"))
    return HYPER_RES_JUST;
  else if (str_ident(s, "ur"))
    return UR_RES_JUST;
  else if (str_ident(s, "factor"))
    return FACTOR_JUST;
  else if (str_ident(s, "xx_res"))
    return XXRES_JUST;
  else if (str_ident(s, "para"))
    return PARA_JUST;
  else if (str_ident(s, "para_fx"))
    return PARA_FX_JUST;
  else if (str_ident(s, "para_ix"))
    return PARA_IX_JUST;
  else if (str_ident(s, "instantiate"))
    return INSTANCE_JUST;
  else if (str_ident(s, "para_fx_ix"))
    return PARA_FX_IX_JUST;
  else if (str_ident(s, "flip"))
    return FLIP_JUST;
  else if (str_ident(s, "xx"))
    return XX_JUST;
  else if (str_ident(s, "merge"))
    return MERGE_JUST;
  else if (str_ident(s, "eval"))
    return EVAL_JUST;
  else if (str_ident(s, "rewrite"))
    return DEMOD_JUST;
  else if (str_ident(s, "unit_del"))
    return UNIT_DEL_JUST;
  else if (str_ident(s, "ivy"))
    return IVY_JUST;
  else
    return UNKNOWN_JUST;
}  /* jstring_to_jtype */

/*************
 *
 *   itoc()
 *
 *************/

static
char itoc(int i)
{
  if (i <= 0)
    return '?';
  else if (i <= 26)
    return 'a' + i - 1;
  else if (i <= 52)
    return 'A' + i - 27;
  else
    return '?';
}  /* itoc */

/*************
 *
 *   ctoi()
 *
 *************/

static
int ctoi(char c)
{
  if (c >= 'a' && c <= 'z')
    return c - 'a' + 1;
  else if (c >= 'A' && c <= 'Z')
    return c - 'A' + 27;
  else
    return INT_MIN;
}  /* ctoi */

/*************
 *
 *   jmap1()
 *
 *************/

/* DOCUMENTATION
A jmap maps ints to pairs of ints.  This returns the first.
If i is not in the map, i is returned.
 */

/* PUBLIC */
int jmap1(I3list map, int i)
{
  int id = assoc2a(map, i);
  return (id == INT_MIN ? i : id);
}  /* jmap1 */

/*************
 *
 *   jmap2()
 *
 *************/

/* DOCUMENTATION
A jmap maps ints to pairs of ints.  This returns a string
representation of the second.  If i is not in the map, or
if the int value of is INT_MIN, "" is returned.

Starting with 0, the strings are "A" - "Z", "A26", "A27", ... .

The argument *a must point to available space for the result.
The result is returned.
 */

/* PUBLIC */
char *jmap2(I3list map, int i, char *a)
{
  int n = assoc2b(map, i);
  if (n == INT_MIN)
    a[0] = '\0';
  else if (n >= 0 && n <= 25) {   /* "A" -- "Z" */
    a[0] = 'A' + n;
    a[1] = '\0';
  }
  else {               /* "A26", ... */
    a[0] = 'A';
    sprintf(a+1, "%d", n);
  }
  return a;
}  /* jmap2 */

/*************
 *
 *   sb_append_id()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void sb_append_id(String_buf sb, int id, I3list map)
{
  char s[21];
  sb_append_int(sb, jmap1(map, id));
  sb_append(sb, jmap2(map, id, s));
}  /* sb_append_id */

/*************
 *
 *   sb_write_res_just() -- (1 a 2 b c 3 d e 4 f)
 *
 *   Assume input is well-formed, that is, length is 3n+1 for n>1.
 *
 *************/

static
void sb_write_res_just(String_buf sb, Just g, I3list map)
{
  Ilist q;
  Ilist p = g->u.lst;

  sb_append(sb, jstring(g));
  sb_append(sb, "(");
  sb_append_id(sb, p->i, map);

  for (q = p->next; q != NULL; q = q->next->next->next) {
    int nuc_lit = q->i;
    int sat_id  = q->next->i;
    int sat_lit = q->next->next->i;
    sb_append(sb, ",");
    sb_append_char(sb, itoc(nuc_lit));
    if (sat_id == 0)
      sb_append(sb, ",xx");
    else {
      sb_append(sb, ",");
      sb_append_id(sb, sat_id, map);
      sb_append(sb, ",");
      if (sat_lit > 0)
	sb_append_char(sb, itoc(sat_lit));
      else {
	sb_append_char(sb, itoc(-sat_lit));
	sb_append(sb, "(flip)");
      }
    }
  }
  sb_append(sb, ")");
}  /* sb_write_res_just */

/*************
 *
 *   sb_write_position() - like this (a,2,1,3)
 *
 *************/

static
void sb_write_position(String_buf sb, Ilist p)
{
  Ilist q;
  sb_append(sb, "(");
  sb_append_char(sb, itoc(p->i));
  for (q = p->next; q != NULL; q = q->next) {
    sb_append(sb, ",");
    sb_append_int(sb, q->i);
  }
  sb_append(sb, ")");
}  /* sb_write_position */

/*************
 *
 *   sb_write_ids() - separated by space
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void sb_write_ids(String_buf sb, Ilist p, I3list map)
{
  Ilist q;
  for (q = p; q; q = q->next) {
    sb_append_id(sb, q->i, map);
    if (q->next)
      sb_append(sb, " ");
  }
}  /* sb_write_ids */

/*************
 *
 *   set_para_subst_proof() / sb_append_para_subst()
 *
 *   When non-NULL, sb_write_just appends "{var <- term, ...}" after
 *   PARA steps to show the unifier.  The arrow direction matches the
 *   assignment semantics of para (each variable receives the term).
 *   Optional, off by default, activated by set(print_substitutions);
 *   independent of print_expanded_proof.
 *
 *************/

#include "xproofs.h"   /* proof_id_to_clause */
#include "literals.h"  /* ith_literal */

static Plist Para_subst_proof = NULL;
static Topform Para_subst_clause = NULL;

/* PUBLIC */
void set_para_subst_proof(Plist proof)
{
  Para_subst_proof = proof;
}  /* set_para_subst_proof */

/* PUBLIC -- set per-clause context for the rider.  Must be set before
   sb_write_just is called for the clause's justification, and cleared
   (NULL) after, so a sb_append_para_subst can find the result clause's
   literals to derive the canonical-rename map.  Called from
   sb_write_clause_jmap in ioutil.c. */
void set_para_subst_clause(Topform c)
{
  Para_subst_clause = c;
}  /* set_para_subst_clause */

/* Build a name like "x_7", "y_6", "v5_12" combining the standard letter
   for `local_varnum` (Prover9's x,y,z,u,w,v5,...) with the originating
   clause's id, joined by underscore so the name is an ordinary identifier
   (no quoting needed at print time). */
static
void clause_var_name(int local_varnum, int clause_id, char *buf, int bufsize)
{
  static const char letters[] = "xyzuw";
  if (local_varnum >= 0 && local_varnum < 5)
    snprintf(buf, bufsize, "%c_%d", letters[local_varnum], clause_id);
  else
    snprintf(buf, bufsize, "v%d_%d", local_varnum, clause_id);
}  /* clause_var_name */

/* Map a possibly-multiplier-shifted varnum back to (local, source_clause_id).
   Returns -1 in *id_out if the multiplier doesn't match either context
   (shouldn't happen in our setup but is a safety fallback). */
static
void resolve_var_source(int rendered_varnum,
                        int c1_mult, int from_id,
                        int c2_mult, int into_id,
                        int *local_out, int *id_out)
{
  int multiplier = rendered_varnum / MAX_VARS;
  *local_out = rendered_varnum % MAX_VARS;
  if (multiplier == c1_mult)
    *id_out = from_id;
  else if (multiplier == c2_mult)
    *id_out = into_id;
  else
    *id_out = -1;
}  /* resolve_var_source */

/* Map size for the internal-varnum -> canonical-varnum table.  Holds
   varnums for c1's multiplier-block and c2's multiplier-block; in our
   setup they're typically multipliers 0,1 (varnums 0..199 with
   MAX_VARS=100), but we size generously to handle higher multipliers
   from concurrent context use. */
#define INT_VARNUM_MAX (MAX_VARS * 8)

/* Deep-copy `t`, replacing each variable with one of:
   * the result clause's canonical letter, IF the variable's internal
     varnum is in the int_to_canon map -- this surfaces Larry's #answer-
     style end-to-end substitution (e.g. {z_3 <- y} where y is the
     result's y);
   * a clause-tagged constant (e.g. "x_7"), if the variable can be
     resolved to a source clause but doesn't appear in the result map;
   * a verbatim variable, as a fallback for unresolvable cases. */
static
Term copy_term_with_canonical(Term t,
                              int c1_mult, int from_id,
                              int c2_mult, int into_id,
                              int *int_to_canon)
{
  if (VARIABLE(t)) {
    int orig = VARNUM(t);
    int local, id;
    char buf[32];
    /* First: did this variable land in the result clause?  If so,
       render it as the result's canonical letter (x,y,z,u,w,v5,...)
       via the standard variable printer. */
    if (orig >= 0 && orig < INT_VARNUM_MAX && int_to_canon[orig] >= 0)
      return get_variable_term(int_to_canon[orig]);
    /* Otherwise fall back to clause-tagged constant. */
    resolve_var_source(orig, c1_mult, from_id, c2_mult, into_id,
                       &local, &id);
    if (id < 0)
      return get_variable_term(orig);  /* fallback: unknown context */
    clause_var_name(local, id, buf, sizeof(buf));
    return get_rigid_term(buf, 0);
  } else {
    Term out = get_rigid_term_dangerously(SYMNUM(t), ARITY(t));
    int i;
    for (i = 0; i < ARITY(t); i++)
      ARG(out, i) = copy_term_with_canonical(ARG(t, i),
                                             c1_mult, from_id,
                                             c2_mult, into_id,
                                             int_to_canon);
    return out;
  }
}  /* copy_term_with_canonical */

/* Walk two terms in parallel; where both are variables, record
   map[expected_varnum] = actual_varnum.  `actual` carries canonical
   (result-clause) varnums; `expected` carries internal (multiplier-
   shifted) varnums.  Returns FALSE if structure diverges (e.g.
   demodulation reshaped the result between paramod and final print);
   in that case map is partial and rendering falls back to clause-tags. */
static
BOOL collect_var_map(Term actual, Term expected, int *map)
{
  if (VARIABLE(actual) && VARIABLE(expected)) {
    int internal = VARNUM(expected);
    int canon = VARNUM(actual);
    if (internal >= 0 && internal < INT_VARNUM_MAX && map[internal] == -1)
      map[internal] = canon;
    return TRUE;
  }
  if (VARIABLE(actual) || VARIABLE(expected))
    return FALSE;
  if (SYMNUM(actual) != SYMNUM(expected) || ARITY(actual) != ARITY(expected))
    return FALSE;
  int i;
  for (i = 0; i < ARITY(actual); i++) {
    if (!collect_var_map(ARG(actual, i), ARG(expected, i), map))
      return FALSE;
  }
  return TRUE;
}  /* collect_var_map */

/* Build the expected pre-renumber paramod result for the targeted
   literal: apply c2 to into_atom and apply c1 to replacement, then
   substitute the (apply'd) replacement into the (apply'd) into_atom
   at into_pos_in_lit.  Caller must zap_term the returned term. */
static
Term build_expected_atom(Term into_atom, Ilist into_pos_in_lit,
                         Term replacement_term,
                         Context c1, Context c2)
{
  Term expected = apply(into_atom, c2);
  Term replacement_applied = apply(replacement_term, c1);

  if (into_pos_in_lit == NULL) {
    /* targeted the whole atom -- shouldn't happen for paramod (you'd
       be replacing the equation itself), but handle gracefully. */
    zap_term(expected);
    return replacement_applied;
  }

  /* Walk down to the parent of the target subterm. */
  Ilist p = into_pos_in_lit;
  Term cur = expected;
  while (p && p->next) {
    int idx = p->i - 1;
    if (idx < 0 || idx >= ARITY(cur)) {
      zap_term(replacement_applied);
      return expected;  /* invalid path; map will be partial */
    }
    cur = ARG(cur, idx);
    p = p->next;
  }
  /* p now points at the final position step; replace at this index. */
  int idx = p->i - 1;
  if (idx < 0 || idx >= ARITY(cur)) {
    zap_term(replacement_applied);
    return expected;
  }
  zap_term(ARG(cur, idx));
  ARG(cur, idx) = replacement_applied;
  return expected;
}  /* build_expected_atom */

/* Collect distinct varnums that appear in a term, into a small array
   `out`.  Returns count.  Variables seen are only recorded once. */
static
int collect_term_vars(Term t, int *out, int already, int max_out)
{
  if (VARIABLE(t)) {
    int n = VARNUM(t);
    int j;
    for (j = 0; j < already; j++)
      if (out[j] == n) return already;
    if (already < max_out) {
      out[already] = n;
      already++;
    }
    return already;
  }
  int i;
  for (i = 0; i < ARITY(t); i++)
    already = collect_term_vars(ARG(t, i), out, already, max_out);
  return already;
}  /* collect_term_vars */

static
int collect_clause_vars(Topform c, int *out, int max_out)
{
  int n = 0;
  Literals lit;
  if (c == NULL) return 0;
  for (lit = c->literals; lit != NULL; lit = lit->next) {
    if (lit->atom)
      n = collect_term_vars(lit->atom, out, n, max_out);
  }
  return n;
}  /* collect_clause_vars */

static
void sb_append_para_subst(String_buf sb, Parajust pj)
{
  if (Para_subst_proof == NULL || pj == NULL)
    return;

  Topform from_cl = proof_id_to_clause(Para_subst_proof, pj->from_id);
  Topform into_cl = proof_id_to_clause(Para_subst_proof, pj->into_id);
  if (from_cl == NULL || into_cl == NULL)
    return;
  if (pj->from_pos == NULL || pj->into_pos == NULL)
    return;

  Literals from_lit = ith_literal(from_cl->literals, pj->from_pos->i);
  Literals into_lit = ith_literal(into_cl->literals, pj->into_pos->i);
  if (from_lit == NULL || into_lit == NULL)
    return;

  Ilist from_pos_in_lit = pj->from_pos->next;
  Ilist into_pos_in_lit = pj->into_pos->next;

  Term source_term = term_at_pos(from_lit->atom, from_pos_in_lit);
  Term target_term = term_at_pos(into_lit->atom, into_pos_in_lit);
  if (source_term == NULL || target_term == NULL)
    return;

  /* Determine the FROM equation's "other side" (the replacement).
     from_pos_in_lit->i is 1 (LHS source -> RHS replaces) or 2 (vice
     versa).  Without that we can't build the expected pre-renumber
     atom, so we silently degrade to clause-tag-only rendering. */
  Term replacement_term = NULL;
  if (from_pos_in_lit && ARITY(from_lit->atom) == 2) {
    int side = from_pos_in_lit->i;
    if (side == 1)      replacement_term = ARG(from_lit->atom, 1);
    else if (side == 2) replacement_term = ARG(from_lit->atom, 0);
  }

  Context c1 = get_context();
  Context c2 = get_context();
  Trail tr = NULL;
  if (!unify(source_term, c1, target_term, c2, &tr)) {
    free_context(c1);
    free_context(c2);
    return;
  }

  /* Build internal-varnum -> result-canonical-varnum map by walking the
     expected pre-renumber atom in parallel with the actual result
     clause's atom for the same literal index.  When this succeeds, the
     rider can show "x_3 <- y" (input variable surviving as result's y).
     When it fails (e.g. demod reshaped the result), fall back to
     clause-tagged rendering. */
  int int_to_canon[INT_VARNUM_MAX];
  int k;
  for (k = 0; k < INT_VARNUM_MAX; k++) int_to_canon[k] = -1;

  if (Para_subst_clause != NULL && replacement_term != NULL) {
    Literals actual_lit = ith_literal(Para_subst_clause->literals,
                                      pj->into_pos->i);
    if (actual_lit && actual_lit->atom) {
      Term expected = build_expected_atom(into_lit->atom, into_pos_in_lit,
                                          replacement_term, c1, c2);
      BOOL ok = collect_var_map(actual_lit->atom, expected, int_to_canon);
      /* If direct walk diverges and the atom is a binary equation, try
         swapping the actual's args -- this handles the common flip(a)
         secondary justification without needing to inspect the just
         chain.  (Demodulation interleaved with paramod still falls
         through to clause-tag rendering; that's accepted degradation.) */
      if (!ok && ARITY(actual_lit->atom) == 2) {
        for (k = 0; k < INT_VARNUM_MAX; k++) int_to_canon[k] = -1;
        Term swapped = get_rigid_term_dangerously(SYMNUM(actual_lit->atom), 2);
        ARG(swapped, 0) = copy_term(ARG(actual_lit->atom, 1));
        ARG(swapped, 1) = copy_term(ARG(actual_lit->atom, 0));
        collect_var_map(swapped, expected, int_to_canon);
        zap_term(swapped);
      }
      zap_term(expected);
    }
  }

  /* Collect entries first so we can filter "obvious survivor" entries
     in a second pass (one input var alone mapping to its same-letter
     result var conveys nothing; aliasing -- multiple input vars to the
     same result var -- IS informative and must stay). */
  struct subst_entry {
    char lhs[32];
    char *rhs;        /* malloc'd, freed after emit */
    int local;        /* LHS local varnum */
    int rhs_canon;    /* RHS canonical varnum if RHS is a bare variable, else -1 */
  } entries[MAX_VARS * 2];
  int n_entries = 0;
  int count_by_canon[MAX_VARS];
  for (k = 0; k < MAX_VARS; k++) count_by_canon[k] = 0;

  int pass;
  for (pass = 0; pass < 2; pass++) {
    Topform cl     = (pass == 0 ? from_cl : into_cl);
    Context cx     = (pass == 0 ? c1 : c2);
    int     src_id = (pass == 0 ? pj->from_id : pj->into_id);

    int vars[MAX_VARS];
    int nv = collect_clause_vars(cl, vars, MAX_VARS);

    int vi;
    for (vi = 0; vi < nv; vi++) {
      int local = vars[vi];
      if (local < 0 || local >= MAX_VARS) continue;
      if (n_entries >= (int)(sizeof(entries) / sizeof(entries[0]))) break;

      Term as_var = get_variable_term(local);
      Term resolved = apply(as_var, cx);
      zap_term(as_var);

      Term rhs_term = copy_term_with_canonical(resolved,
                                               c1->multiplier, pj->from_id,
                                               c2->multiplier, pj->into_id,
                                               int_to_canon);

      /* Build RHS string (with paren-wrap for arity>=2). */
      String_buf rhs_sb = get_string_buf();
      BOOL wrap = (ARITY(rhs_term) >= 2);
      if (wrap) sb_append(rhs_sb, "(");
      sb_write_term(rhs_sb, rhs_term);
      if (wrap) sb_append(rhs_sb, ")");
      char *rhs_str = sb_to_malloc_string(rhs_sb);
      zap_string_buf(rhs_sb);

      char lhs_buf[32];
      clause_var_name(local, src_id, lhs_buf, sizeof(lhs_buf));

      /* Identity-string suppression: clause-tag fallback on both sides
         (walker bailed out due to demod). */
      if (rhs_str && strcmp(lhs_buf, rhs_str) == 0) {
        free(rhs_str);
        zap_term(rhs_term);
        zap_term(resolved);
        continue;
      }

      strncpy(entries[n_entries].lhs, lhs_buf, sizeof(entries[n_entries].lhs)-1);
      entries[n_entries].lhs[sizeof(entries[n_entries].lhs)-1] = 0;
      entries[n_entries].rhs = rhs_str;
      entries[n_entries].local = local;
      entries[n_entries].rhs_canon = (VARIABLE(rhs_term)
                                      ? VARNUM(rhs_term) : -1);
      if (entries[n_entries].rhs_canon >= 0 &&
          entries[n_entries].rhs_canon < MAX_VARS)
        count_by_canon[entries[n_entries].rhs_canon]++;
      n_entries++;

      zap_term(rhs_term);
      zap_term(resolved);
    }
  }

  /* Emit, suppressing entries that are "obvious survivors":
     RHS is a bare canonical variable, the LHS letter matches the RHS
     letter (local == rhs_canon), and no other entry shares that RHS
     varnum (no aliasing being flagged). */
  BOOL any = FALSE;
  int ei;
  for (ei = 0; ei < n_entries; ei++) {
    BOOL obvious = (entries[ei].rhs_canon >= 0 &&
                    entries[ei].rhs_canon < MAX_VARS &&
                    entries[ei].rhs_canon == entries[ei].local &&
                    count_by_canon[entries[ei].rhs_canon] == 1);
    if (!obvious) {
      if (!any) { sb_append(sb, " {"); any = TRUE; }
      else      { sb_append(sb, ", "); }
      sb_append(sb, entries[ei].lhs);
      sb_append(sb, " <- ");
      sb_append(sb, entries[ei].rhs);
    }
    free(entries[ei].rhs);
  }
  if (any)
    sb_append(sb, "}");

  undo_subst(tr);
  free_context(c1);
  free_context(c2);
}  /* sb_append_para_subst */

/*************
 *
 *   sb_write_just()
 *
 *************/

/* DOCUMENTATION
This routine writes (to a String_buf) a clause justification.
No whitespace is printed before or after.
*/

/* PUBLIC */
void sb_write_just(String_buf sb, Just just, I3list map)
{
  Just g = just;
  sb_append(sb, "[");
  while (g != NULL) {
    Just_type rule = g->type;
    if (rule == INPUT_JUST || rule == GOAL_JUST)
      sb_append(sb, jstring(g));
    else if (rule==BINARY_RES_JUST ||
	     rule==HYPER_RES_JUST ||
	     rule==UR_RES_JUST) {
      sb_write_res_just(sb, g, map);
    }
    else if (rule == DEMOD_JUST) {
      I3list p;
      sb_append(sb, jstring(g));
      sb_append(sb, "([");
      for (p = g->u.demod; p; p = p->next) {
	sb_append_int(sb, p->i);
	if (p->j > 0) {
	  sb_append(sb, "(");
	  sb_append_int(sb, p->j);
	  if (p->k == 2)
	    sb_append(sb, ",R");
	  sb_append(sb, ")");
	}

	sb_append(sb, p->next ? "," : "");
      }
      sb_append(sb, "])");
    }
    else if (rule == UNIT_DEL_JUST) {
      Ilist p = g->u.lst;
      int n = p->i;
      int id = p->next->i;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      if (n < 0) {
	sb_append_char(sb, itoc(-n));
	sb_append(sb, "(flip),");
      }
      else {
	sb_append_char(sb, itoc(n));
	sb_append(sb, ",");
      }
      sb_append_id(sb, id, map);
      sb_append(sb, ")");
    }
    else if (rule == FACTOR_JUST) {
      Ilist p = g->u.lst;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_id(sb, p->i, map);
      sb_append(sb, ",");
      sb_append_char(sb, itoc(p->next->i));
      sb_append(sb, ",");
      sb_append_char(sb, itoc(p->next->next->i));
      sb_append(sb, ")");
    }
    else if (rule == XXRES_JUST) {
      Ilist p = g->u.lst;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_id(sb, p->i, map);
      sb_append(sb, ",");
      sb_append_char(sb, itoc(p->next->i));
      sb_append(sb, ")");
    }
    else if (rule == EXPAND_DEF_JUST) {
      Ilist p = g->u.lst;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_id(sb, p->i, map);
      sb_append(sb, ",");
      sb_append_id(sb, p->next->i, map);
      sb_append(sb, ")");
    }
    else if (rule == BACK_DEMOD_JUST ||
	     rule == BACK_UNIT_DEL_JUST ||
	     rule == NEW_SYMBOL_JUST ||
	     rule == COPY_JUST ||
	     rule == DENY_JUST ||
	     rule == CLAUSIFY_JUST ||
	     rule == PROPOSITIONAL_JUST) {
      int id = g->u.id;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_id(sb, id, map);
      sb_append(sb, ")");
    }
    else if (rule == FLIP_JUST ||
	     rule == XX_JUST ||
	     rule == MERGE_JUST) {
      int id = g->u.id;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_char(sb, itoc(id));
      sb_append(sb, ")");
    }
    else if (rule == EVAL_JUST) {
      int id = g->u.id;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_int(sb, id);
      sb_append(sb, ")");
    }
    else if (rule == PARA_JUST || rule == PARA_FX_JUST ||
	     rule == PARA_IX_JUST || rule == PARA_FX_IX_JUST) {
      Parajust p = g->u.para;

      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_id(sb, p->from_id, map);
      sb_write_position(sb, p->from_pos);

      sb_append(sb, ",");
      sb_append_id(sb, p->into_id, map);
      sb_write_position(sb, p->into_pos);

      sb_append(sb, ")");

      /* When -expand is on, append the unifier so newcomers can see
         which variables got substituted across the clause. */
      sb_append_para_subst(sb, p);
    }
    else if (rule == INSTANCE_JUST) {
      Plist p;

      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_int(sb, g->u.instance->parent_id);
      sb_append(sb, ",[");

      for (p = g->u.instance->pairs; p; p = p->next) {
	sb_write_term(sb, p->v);
	if (p->next)
	  sb_append(sb, ",");
      }
      sb_append(sb, "])");
    }
    else if (rule == IVY_JUST) {
      sb_append(sb, jstring(g));
    }
    else {
      printf("\nunknown rule: %d\n", rule);
      fatal_error("sb_write_just: unknown rule");
    }
    g = g->next;
    if (g)
      sb_append(sb, ",");
  }
  sb_append(sb, "].");
}  /* sb_write_just */

/*************
 *
 *   sb_xml_write_just()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void sb_xml_write_just(String_buf sb, Just just, I3list map)
{
  Just g;

  /* Put the standard form into an attribute. */

  String_buf sb_standard = get_string_buf();
  sb_write_just(sb_standard, just, map);
  sb_append(sb, "    <justification jstring=\""); 
  sb_cat(sb, sb_standard);  /* this frees sb_standard */
  sb_append(sb, "\">\n");

  /* Put an abbreviated form (rule, parents) into an XML elements. */

  for (g = just; g; g = g->next) {

    Ilist parents = get_parents(g, FALSE);  /* for this node only */

    if (g == just)
      sb_append(sb, "      <j1 rule=\"");
    else
      sb_append(sb, "      <j2 rule=\"");
    sb_append(sb, jstring(g));
    sb_append(sb, "\"");

    if (parents) {
      sb_append(sb, " parents=\"");
      sb_write_ids(sb, parents, map);
      zap_ilist(parents);
      sb_append(sb, "\"");
    }

    sb_append(sb, "/>\n");  /* close the <j1 or <j2 */
  }
  sb_append(sb, "    </justification>\n");
}  /* sb_xml_write_just */

/*************
 *
 *   p_just()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void p_just(Just j)
{
  String_buf sb = get_string_buf();
  sb_write_just(sb, j, NULL);
  sb_append(sb, "\n");
  fprint_sb(stdout, sb);
  zap_string_buf(sb);
}  /* p_just */

/*************
 *
 *   zap_parajust()
 *
 *************/

static
void zap_parajust(Parajust p)
{
  zap_ilist(p->from_pos);
  zap_ilist(p->into_pos);
  free_parajust(p);
}  /* zap_parajust */

/*************
 *
 *   zap_instancejust()
 *
 *************/

static
void zap_instancejust(Instancejust p)
{
  zap_plist_of_terms(p->pairs);
  free_instancejust(p);
}  /* zap_instancejust */

/*************
 *
 *   zap_ivyjust()
 *
 *************/

static
void zap_ivyjust(Ivyjust p)
{
  zap_ilist(p->pos1);
  zap_ilist(p->pos2);
  zap_plist_of_terms(p->pairs);
  free_ivyjust(p);
}  /* zap_ivyjust */

/*************
 *
 *   zap_just()
 *
 *************/

/* DOCUMENTATION
This routine frees a justification list, including any sublists.
*/

/* PUBLIC */
void zap_just(Just just)
{
  while (just != NULL) {
    Just next = just->next;

    switch (just->type) {
    case INPUT_JUST:
    case GOAL_JUST:
    case DENY_JUST:
    case CLAUSIFY_JUST:
    case COPY_JUST:
    case PROPOSITIONAL_JUST:
    case NEW_SYMBOL_JUST:
    case BACK_DEMOD_JUST:
    case BACK_UNIT_DEL_JUST:
    case FLIP_JUST:
    case XX_JUST:
    case MERGE_JUST:
    case EVAL_JUST:
      break;  /* nothing to do */
    case EXPAND_DEF_JUST:
    case BINARY_RES_JUST:
    case HYPER_RES_JUST:
    case UR_RES_JUST:
    case UNIT_DEL_JUST:
    case FACTOR_JUST:
    case XXRES_JUST:
      zap_ilist(just->u.lst); break;
    case DEMOD_JUST:
      zap_i3list(just->u.demod); break;
    case PARA_JUST:
    case PARA_FX_JUST:
    case PARA_IX_JUST:
    case PARA_FX_IX_JUST:
      zap_parajust(just->u.para); break;
    case INSTANCE_JUST:
      zap_instancejust(just->u.instance); break;
    case IVY_JUST:
      zap_ivyjust(just->u.ivy); break;
    default: fatal_error("zap_just: unknown type");
    }
    free_just(just);
    just = next;
  }
}  /* zap_just */

/*************
 *
 *   get_parents()
 *
 *************/

/* DOCUMENTATION
This routine returns an Ilist of parent IDs.
If (all), get parents from the whole justification; otherwise
get parents from the first node only.
*/

/* PUBLIC */
Ilist get_parents(Just just, BOOL all)
{
  Ilist parents = NULL;
  Just g = just;

  while (g) {
    Just_type rule = g->type;
    if (rule==BINARY_RES_JUST || rule==HYPER_RES_JUST || rule==UR_RES_JUST) {
      /* [rule (nucid nuclit sat1id sat1lit nuclit2 sat2id sat2lit ...)] */
      Ilist p = g->u.lst;
      int nuc_id = p->i;
      parents = ilist_prepend(parents, nuc_id);
      p = p->next;
      while (p != NULL) {
	int sat_id = p->next->i;
	if (sat_id == 0)
	  ; /* resolution with x=x */
	else
	  parents = ilist_prepend(parents, sat_id);
	p = p->next->next->next;
      }
    }
    else if (rule == PARA_JUST || rule == PARA_FX_JUST ||
	     rule == PARA_IX_JUST || rule == PARA_FX_IX_JUST) {
      Parajust p   = g->u.para;
      parents = ilist_prepend(parents, p->from_id);
      parents = ilist_prepend(parents, p->into_id);
    }
    else if (rule == INSTANCE_JUST) {
      parents = ilist_prepend(parents, g->u.instance->parent_id);
    }
    else if (rule == EXPAND_DEF_JUST) {
      parents = ilist_prepend(parents, g->u.lst->i);
      parents = ilist_prepend(parents, g->u.lst->next->i);
    }
    else if (rule == FACTOR_JUST || rule == XXRES_JUST) {
      int parent_id = g->u.lst->i;
      parents = ilist_prepend(parents, parent_id);
    }
    else if (rule == UNIT_DEL_JUST) {
      int parent_id = g->u.lst->next->i;
      parents = ilist_prepend(parents, parent_id);
    }
    else if (rule == BACK_DEMOD_JUST ||
	     rule == COPY_JUST ||
	     rule == DENY_JUST ||
	     rule == CLAUSIFY_JUST ||
	     rule == PROPOSITIONAL_JUST ||
	     rule == NEW_SYMBOL_JUST ||
	     rule == BACK_UNIT_DEL_JUST) {
      int parent_id = g->u.id;
      parents = ilist_prepend(parents, parent_id);
    }
    else if (rule == DEMOD_JUST) {
      I3list p;
      /* list of triples: (i=ID, j=position, k=direction) */
      for (p = g->u.demod; p; p = p->next)
	parents = ilist_prepend(parents, p->i);
    }
    else if (rule == IVY_JUST) {
      if (g->u.ivy->type == FLIP_JUST ||
	  g->u.ivy->type == BINARY_RES_JUST ||
	  g->u.ivy->type == PARA_JUST ||
	  g->u.ivy->type == INSTANCE_JUST ||
	  g->u.ivy->type == PROPOSITIONAL_JUST)
	parents = ilist_prepend(parents, g->u.ivy->parent1);
      if (g->u.ivy->type == BINARY_RES_JUST ||
	  g->u.ivy->type == PARA_JUST)
	parents = ilist_prepend(parents, g->u.ivy->parent2);
    }
    else if (rule == FLIP_JUST ||
	     rule == XX_JUST ||
	     rule == MERGE_JUST ||
	     rule == EVAL_JUST ||
	     rule == GOAL_JUST ||
	     rule == INPUT_JUST)
      ;  /* do nothing */
    else
      fatal_error("get_parents, unknown rule.");

    g = (all ? g->next : NULL);
  }
  return reverse_ilist(parents);
}  /* get_parents */

/*************
 *
 *   first_negative_parent()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Topform first_negative_parent(Topform c)
{
  Ilist parents = get_parents(c->justification, TRUE);
  Ilist p;
  Topform first_neg = NULL;
  for (p = parents; p && first_neg == NULL; p = p->next) {
    Topform c = find_clause_by_id(p->i);
    if (negative_clause_possibly_compressed(c))
      first_neg = c;
  }
  zap_ilist(p);
  return first_neg;
}  /* first_negative_parent */

/*************
 *
 *   get_clanc()
 *
 *************/

static
Plist get_clanc(int id, Plist anc)
{
  Ilist worklist, parents, p, tmp;
  Topform c;
  int cur_id;

  worklist = ilist_prepend(NULL, id);

  while (worklist != NULL) {
    /* pop front of worklist */
    cur_id = worklist->i;
    tmp = worklist;
    worklist = worklist->next;
    tmp->next = NULL;
    zap_ilist(tmp);

    c = find_clause_by_id(cur_id);
    if (c == NULL) {
      /* Parent clause was deleted (back-subsumed, weight-limited, etc.).
         Skip this branch — ancestor set is incomplete but safe.
         ancestor_subsume will be conservative (fewer ancestors means
         fewer subsumption opportunities, never unsound). */
      continue;
    }

    if (!plist_member(anc, c)) {
      anc = insert_clause_into_plist(anc, c, TRUE);
      parents = get_parents(c->justification, TRUE);
      for (p = parents; p; p = p->next) {
        worklist = ilist_prepend(worklist, p->i);
      }
      zap_ilist(parents);
    }
  }
  return anc;
}  /* get_clanc */

/*************
 *
 *   get_clause_ancestors()
 *
 *************/

/* DOCUMENTATION
This routine returns the Plist of clauses that are ancestors of Topform c,
including clause c.  The result is sorted (increasing) by ID.
If any of the ancestors are compressed, they are uncompressed
(in place) and left uncompressed.
*/

/* PUBLIC */
Plist get_clause_ancestors(Topform c)
{
  if (c == NULL) return NULL;
  if (c->id != 0)
    return get_clanc(c->id, NULL);

  /* Root clause has no ID yet (called from anc_subsume during forward
     subsumption, before assign_clause_id).  Insert c itself, then walk
     its parents via the justification chain directly.  Without this,
     get_clanc(0) returns empty because find_clause_by_id(0) fails --
     making proof_length(c) = 0 and breaking the cost comparison in
     anc_subsume (every existing subsumer's proof_length >= 1, so
     cost_c <= cost_d evaluates FALSE and forward subsumption is
     blocked unconditionally under set(ancestor_subsume). */
  Plist anc = insert_clause_into_plist(NULL, c, TRUE);
  Ilist parents = get_parents(c->justification, TRUE);
  Ilist p;
  for (p = parents; p; p = p->next) {
    Plist sub, q;
    if (p->i == 0) continue;
    sub = get_clanc(p->i, NULL);
    for (q = sub; q; q = q->next) {
      if (!plist_member(anc, q->v))
        anc = insert_clause_into_plist(anc, q->v, TRUE);
    }
    zap_plist(sub);
  }
  zap_ilist(parents);
  return anc;
}  /* get_clause_ancestors */

/*************
 *
 *   proof_length()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int proof_length(Plist proof)
{
  return plist_count(proof);
}  /* proof_length */

/*************
 *
 *   proof_tree_weight()
 *
 *************/

/* DOCUMENTATION
Return the "proof weight" of clause c in Otter's sense: the number
of input-clause leaves in the proof TREE of c (not the DAG, so shared
ancestors are counted with multiplicity).  An input clause (one with
no parents) contributes 1; a derived clause contributes the sum of
the weights of its parents.  This measure differs from proof_length,
which counts distinct ancestors (DAG nodes).  Used by ancestor
subsumption as an alternate tie-breaking metric for alphabetic
variants (see Otter's prf_weight).  The traversal is iterative with
memoization keyed on clause ID so that DAGs with shared ancestors
are evaluated in linear time even though each share is counted with
multiplicity in the result.
*/

/* PUBLIC */
int proof_tree_weight(Topform c)
{
  /* Memoized DAG evaluation computing the tree-leaf count.
     We compute f(c) = 1 if c has no clause parents; else sum of f(p)
     over clause parents p.  Memoization is keyed on clause id.  We
     use a two-phase postorder: first push every node, then compute
     bottom-up.  Cycles (which should not occur in a well-formed
     proof DAG) are guarded by a "visiting" mark. */
  enum { MARK_VISITING = -1 };
  Plist worklist = NULL;     /* nodes to process (DFS stack, via plist_prepend) */
  I2list memo = NULL;        /* clause_id -> computed weight (or MARK_VISITING) */
  Plist ancestors;
  Plist a;

  if (c == NULL)
    return 0;

  /* Collect ancestors to bound the memo table and to pre-uncompress
     any compressed justifications (get_clause_ancestors does this). */
  ancestors = get_clause_ancestors(c);

  /* Seed the worklist with every ancestor; iterative postorder pass. */
  for (a = ancestors; a; a = a->next) {
    Topform ca = a->v;
    worklist = plist_prepend(worklist, ca);
  }

  while (worklist != NULL) {
    Topform cur = worklist->v;
    Ilist parents;
    BOOL all_done;
    int sum;

    if (assoc(memo, cur->id) != INT_MIN) {
      worklist = plist_pop(worklist);
      continue;
    }

    parents = get_parents(cur->justification, TRUE);
    if (parents == NULL) {
      /* Input clause: leaf contributes 1. */
      memo = alist_insert(memo, cur->id, 1);
      worklist = plist_pop(worklist);
      continue;
    }

    /* Check that all parents are memoized; if not, push them first. */
    all_done = TRUE;
    sum = 0;
    {
      Ilist p;
      for (p = parents; p; p = p->next) {
        int pv = assoc(memo, p->i);
        if (pv == INT_MIN) {
          Topform pc = find_clause_by_id(p->i);
          if (pc == NULL) {
            /* Parent vanished (e.g., purged by gc).  Treat as leaf
               with weight 1 -- conservative, keeps the metric finite. */
            sum += 1;
          } else {
            worklist = plist_prepend(worklist, pc);
            all_done = FALSE;
          }
        } else {
          sum += pv;
        }
      }
    }
    zap_ilist(parents);

    if (all_done) {
      memo = alist_insert(memo, cur->id, sum == 0 ? 1 : sum);
      worklist = plist_pop(worklist);
    }
    /* else: parents were pushed; revisit cur after they're done. */
  }

  {
    int result = assoc(memo, c->id);
    if (result == INT_MIN)
      result = 1;
    zap_i2list(memo);
    zap_plist(ancestors);
    return result;
  }
}  /* proof_tree_weight */

/*************
 *
 *   map_id()
 *
 *************/

static
int map_id(I2list a, int arg)
{
  int val = assoc(a, arg);
  return val == INT_MIN ? arg : val;
}  /* map_id */

/*************
 *
 *   map_just()
 *
 *************/

/* DOCUMENTATION
Update the clause IDs in a justification according to the map.
*/

/* PUBLIC */
void map_just(Just just, I2list map)
{
  Just j;

  for (j = just; j; j = j->next) {
    Just_type rule = j->type;
    if (rule==BINARY_RES_JUST || rule==HYPER_RES_JUST || rule==UR_RES_JUST) {
      /* [rule (nucid n sat1id n n sat2id n ...)] */
      Ilist p = j->u.lst;
      p->i = map_id(map, p->i);  /* nucleus */
      p = p->next;
      while (p != NULL) {
	int sat_id = p->next->i;
	if (sat_id == 0)
	  ;  /* resolution with x=x */
	else
	  p->next->i = map_id(map, p->next->i);  /* satellite */
	p = p->next->next->next;
      }
    }
    else if (rule == PARA_JUST || rule == PARA_FX_JUST ||
	     rule == PARA_IX_JUST || rule == PARA_FX_IX_JUST) {
      Parajust p   = j->u.para;
      p->from_id = map_id(map, p->from_id);
      p->into_id = map_id(map, p->into_id);
    }
    else if (rule == INSTANCE_JUST) {
      Instancejust p   = j->u.instance;
      p->parent_id = map_id(map, p->parent_id);
    }
    else if (rule == EXPAND_DEF_JUST) {
      Ilist p = j->u.lst;
      p->i = map_id(map, p->i);
      p->next->i = map_id(map, p->next->i);
    }
    else if (rule == FACTOR_JUST || rule == XXRES_JUST) {
      Ilist p = j->u.lst;
      p->i = map_id(map, p->i);
    }
    else if (rule == UNIT_DEL_JUST) {
      Ilist p = j->u.lst;
      p->next->i = map_id(map, p->next->i);
    }
    else if (rule == BACK_DEMOD_JUST ||
	     rule == COPY_JUST ||
	     rule == DENY_JUST ||
	     rule == CLAUSIFY_JUST ||
	     rule == PROPOSITIONAL_JUST ||
	     rule == NEW_SYMBOL_JUST ||
	     rule == BACK_UNIT_DEL_JUST) {
      j->u.id = map_id(map, j->u.id);
    }
    else if (rule == DEMOD_JUST) {
      I3list p;
      /* list of triples: <ID, position, direction> */
      for (p = j->u.demod; p; p = p->next)
	p->i = map_id(map, p->i);
    }
    else if (rule == IVY_JUST) {
      if (j->u.ivy->type == FLIP_JUST ||
	  j->u.ivy->type == BINARY_RES_JUST ||
	  j->u.ivy->type == PARA_JUST ||
	  j->u.ivy->type == INSTANCE_JUST ||
	  j->u.ivy->type == PROPOSITIONAL_JUST)
	j->u.ivy->parent1 = map_id(map, j->u.ivy->parent1);
      if (j->u.ivy->type == BINARY_RES_JUST ||
	  j->u.ivy->type == PARA_JUST)
	j->u.ivy->parent2 = map_id(map, j->u.ivy->parent2);
    }
    else if (rule == FLIP_JUST ||
	     rule == XX_JUST ||
	     rule == MERGE_JUST ||
	     rule == EVAL_JUST ||
	     rule == GOAL_JUST ||
	     rule == INPUT_JUST)
      ;  /* do nothing */
    else
      fatal_error("get_clanc, unknown rule.");
  }
}  /* map_just */

/*************
 *
 *   just_count()
 *
 *************/

/* DOCUMENTATION
Return the number of justification elements in a justtification.
*/

/* PUBLIC */
int just_count(Just j)
{
  int count = 0;
  while (j != NULL) {
    count++;
    j = j->next;
  }
  return count;
}  /* just_count */
/*************
 *
 *   mark_parents_as_used()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void mark_parents_as_used(Topform c)
{
  Ilist parents = get_parents(c->justification, TRUE);
  Ilist p;
  for (p = parents; p; p = p->next) {
    Topform parent = find_clause_by_id(p->i);
    parent->used = TRUE;
  }
  zap_ilist(parents);
}  /* mark_parents_as_used */

/*************
 *
 *   cl_level()
 *
 *************/

/*************
 *
 *   clause_level()
 *
 *************/

/* DOCUMENTATION
Return the level of a clause.  Input clauses have level=0, and
a derived clause has level 1 more than the max of the levels of its parents.
Iterative: collect all ancestors, then compute levels bottom-up (by ID order).
*/

/* PUBLIC */
int clause_level(Topform c)
{
  Plist ancestors, q;
  I2list levels;
  int level;

  /* get_clanc returns ancestors sorted by ID (ascending). */
  ancestors = get_clanc(c->id, NULL);

  /* Process in ID order: parents always have smaller IDs, so their
     levels are computed before they are needed. */
  levels = NULL;
  for (q = ancestors; q; q = q->next) {
    Topform a = q->v;
    Ilist parents = get_parents(a->justification, TRUE);
    Ilist p;
    int max = -1;
    for (p = parents; p; p = p->next) {
      int parent_level = assoc(levels, p->i);
      if (parent_level != INT_MIN)
        max = IMAX(max, parent_level);
    }
    levels = alist_insert(levels, a->id, max + 1);
    zap_ilist(parents);
  }

  level = assoc(levels, c->id);
  zap_i2list(levels);
  zap_plist(ancestors);
  return level;
}  /* clause_level */

/*************
 *
 *   lit_string_to_int()
 *
 *************/

static
int lit_string_to_int(char *s)
{
  int i;
  if (str_to_int(s, &i))
    return i;
  else if (strlen(s) > 1)
    return INT_MIN;
  else
    return ctoi(s[0]);
}  /* lit_string_to_int */

/*************
 *
 *   args_to_ilist()
 *
 *************/

static
Ilist args_to_ilist(Term t)
{
  Ilist p = NULL;
  int i;
  for (i = 0; i < ARITY(t); i++) {
    Term a = ARG(t,i);
    char *s = sn_to_str(SYMNUM(a));
    int x = lit_string_to_int(s);
    if (x > 0) {
      if (ARITY(a) == 1 && is_constant(ARG(a,0), "flip"))
	p = ilist_append(p, -x);
      else
	p = ilist_append(p, x);
    }
    else if (str_ident(s, "xx"))
      p = ilist_append(ilist_append(p, 0), 0);
    else
      fatal_error("args_to_ilist, bad arg");
  }
  return p;
}  /* args_to_ilist */

/*************
 *
 *   term_to_just()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Just term_to_just(Term lst)
{
  if (nil_term(lst))
    return NULL;
  else {
    Term t = ARG(lst,0);
    Just j = get_just();
    j->next = term_to_just(ARG(lst,1));  /* do the tail */
    
    j->type = jstring_to_jtype(sn_to_str(SYMNUM(t)));

    switch (j->type) {

      /* primary and secondary are mixed */

    case INPUT_JUST:
    case GOAL_JUST:
      return j;

    case COPY_JUST:
    case DENY_JUST:
    case CLAUSIFY_JUST:
    case PROPOSITIONAL_JUST:
    case NEW_SYMBOL_JUST:
    case BACK_DEMOD_JUST:
    case BACK_UNIT_DEL_JUST:
      {
	int id;
	if (term_to_int(ARG(t,0), &id))
	  j->u.id = id;
	else
	  fatal_error("term_to_just, bad just id");
	return j;
      }

    case FLIP_JUST:   /* secondary */
    case XX_JUST:     /* secondary */
    case EVAL_JUST:   /* secondary */
    case MERGE_JUST:  /* secondary */
      {
	j->u.id = lit_string_to_int(sn_to_str(SYMNUM(ARG(t,0))));
	return j;
      }

    case DEMOD_JUST:      /* secondary, rewrite([id(pos,side), ... ]) */
      {
	I3list p = NULL;
	Term lst = ARG(t,0);
	if (!proper_listterm(lst))
	  fatal_error("term_to_just: rewrites must be proper list");
	while(cons_term(lst)) {
	  Term a = ARG(lst,0);
	  int i, j;
	  int k = 0;
	  char *s = sn_to_str(SYMNUM(a));
	  if (ARITY(a) == 2 &&
	      str_to_int(s,&i) &
	      term_to_int(ARG(a,0),&j)) {
	    if (is_constant(ARG(a,1), "L"))
	      k = 1;
	    else if (is_constant(ARG(a,1), "R"))
	      k = 2;
	    else
	      fatal_error("term_to_just: bad justification term (demod 1)");
	    p = i3list_append(p, i, j, k);
	  }
	  else if (ARITY(a) == 1 &&
	      str_to_int(s,&i) &
	      term_to_int(ARG(a,0),&j)) {
	    p = i3list_append(p, i, j, 1);
	  }
	  else if (ARITY(a) == 0 &&
		   str_to_int(s,&i)) {
	    p = i3list_append(p, i, 0, 1);
	  }
	  else
	    fatal_error("term_to_just: bad justification term (demod 2)");
	  lst = ARG(lst,1);
	}
	j->u.demod = p;
	return j;
      }

    case EXPAND_DEF_JUST:
    case BINARY_RES_JUST:
    case HYPER_RES_JUST:
    case UR_RES_JUST:
    case FACTOR_JUST:
    case XXRES_JUST:
    case UNIT_DEL_JUST:   /* secondary */
      j->u.lst = args_to_ilist(t);
      return j;

    case PARA_JUST:
    case PARA_FX_JUST:
    case PARA_IX_JUST:
    case PARA_FX_IX_JUST:
      {
	int id;
	Term from = ARG(t,0);
	Term into = ARG(t,1);
	Parajust p = get_parajust();
	j->u.para = p;

	if (str_to_int(sn_to_str(SYMNUM(from)), &id))
	  p->from_id = id;
	else
	  fatal_error("term_to_just, bad from_id");

	p->from_pos = args_to_ilist(from);

	if (str_to_int(sn_to_str(SYMNUM(into)), &id))
	  p->into_id = id;
	else
	  fatal_error("term_to_just, bad into_id");

	p->into_pos = args_to_ilist(into);

	return j;
      }
    case INSTANCE_JUST:
      {
	int id;
	Term parent = ARG(t,0);
	Term pairs = ARG(t,1);
	Instancejust ij = get_instancejust();
	j->u.instance = ij;
	if (str_to_int(sn_to_str(SYMNUM(parent)), &id))
	  ij->parent_id = id;
	else
	  fatal_error("term_to_just, bad parent_id");

	ij->pairs = NULL;
	while (cons_term(pairs)) {
	  ij->pairs = plist_append(ij->pairs, copy_term(ARG(pairs,0)));
	  pairs = ARG(pairs,1);
	}
	return j;
      }
    
    case IVY_JUST:
      fatal_error("term_to_just, IVY_JUST not handled");
      return NULL;

    case UNKNOWN_JUST:
    default:
      printf("unknown: %d, %s\n", j->type, jstring(j));
      fatal_error("term_to_just, unknown justification");
      return NULL;
    }
  }
}  /* term_to_just */

/*************
 *
 *   primary_just_type()
 *
 *************/

/* DOCUMENTATION
Does a clause have justtification "input"?
*/

/* PUBLIC */
BOOL primary_just_type(Topform c, Just_type t)
{
  return c->justification && c->justification->type == t;
}  /* primary_just_type */

/*************
 *
 *   has_input_just()
 *
 *************/

/* DOCUMENTATION
Does a clause have justtification "input"?
*/

/* PUBLIC */
BOOL has_input_just(Topform c)
{
  return primary_just_type(c, INPUT_JUST);
}  /* has_input_just */

/*************
 *
 *   has_copy_just()
 *
 *************/

/* DOCUMENTATION
Does a clause have justification "copy"?
*/

/* PUBLIC */
BOOL has_copy_just(Topform c)
{
  return primary_just_type(c, COPY_JUST);
}  /* has_copy_just */

/*************
 *
 *   has_copy_flip_just()
 *
 *************/

/* DOCUMENTATION
Does a clause have justification "copy, flip", and nothing else?
*/

/* PUBLIC */
BOOL has_copy_flip_just(Topform c)
{
  return (c->justification &&
	  c->justification->type == COPY_JUST &&
	  c->justification->next &&
	  c->justification->next->type == FLIP_JUST &&
	  c->justification->next->next == NULL);
}  /* has_copy_flip_just */

/*************
 *
 *   has_deny_just()
 *
 *************/

/* DOCUMENTATION
Does a clause have justification "deny"?
*/

/* PUBLIC */
BOOL has_deny_just(Topform c)
{
  return primary_just_type(c, DENY_JUST);
}  /* has_deny_just */

/*************
 *
 *   has_goal_just()
 *
 *************/

/* DOCUMENTATION
Does a clause have justification "goal"?
*/

/* PUBLIC */
BOOL has_goal_just(Topform c)
{
  return primary_just_type(c, GOAL_JUST);
}  /* has_goal_just */

/* ************************************************************************
   BV(2007-aug-20):  new functions to support tagged proofs (prooftrans)
   ***********************************************************************/

/*************
 *
 *   sb_tagged_write_res_just() -- (1 a 2 b c 3 d e 4 f)
 *
 *   Assume input is well-formed, that is, length is 3n+1 for n>1.
 *
 *************/

static
void sb_tagged_write_res_just(String_buf sb, Just g, I3list map)
{
  Ilist q;
  Ilist p = g->u.lst;

#if 1
   /* BV(2007-jul-10) */
  sb_append(sb, jstring(g));
  sb_append(sb, "\np ");
  sb_append_id(sb, p->i, map);
  for (q = p->next; q != NULL; q = q->next->next->next) {
    int sat_id  = q->next->i;
    sb_append(sb, "\np ");
    if (sat_id == 0)
      sb_append(sb, ",xx");
    else
      sb_append_id(sb, sat_id, map);
    }
  return;
#endif

}  /* sb_tagged_write_res_just */

/*************
 *
 *   sb_tagged_write_just()
 *
 *************/

/* DOCUMENTATION
This routine writes (to a String_buf) a clause justification.
No whitespace is printed before or after.
*/

/* PUBLIC */
void sb_tagged_write_just(String_buf sb, Just just, I3list map)
{
  Just g = just;
  /* sb_append(sb, "["); */
  while (g != NULL) {
    Just_type rule = g->type;
    sb_append(sb, "i ");
    if (rule == INPUT_JUST || rule == GOAL_JUST)
      sb_append(sb, jstring(g));
    else if (rule==BINARY_RES_JUST ||
	     rule==HYPER_RES_JUST ||
	     rule==UR_RES_JUST) {
      sb_tagged_write_res_just(sb, g, map);
    }
    else if (rule == DEMOD_JUST) {
      I3list p;
      sb_append(sb, jstring(g));
      for (p = g->u.demod; p; p = p->next) {
        sb_append(sb, "\np ");
	sb_append_int(sb, p->i);
      }
    }
    else if (rule == UNIT_DEL_JUST) {
      Ilist p = g->u.lst;
      int n = p->i;
      int id = p->next->i;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      if (n < 0) {
	sb_append_char(sb, itoc(-n));
	sb_append(sb, "(flip),");
      }
      else {
	sb_append_char(sb, itoc(n));
	sb_append(sb, ",");
      }
      sb_append_id(sb, id, map);
      sb_append(sb, ")");
    }
    else if (rule == FACTOR_JUST) {
      Ilist p = g->u.lst;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_id(sb, p->i, map);
      sb_append(sb, ",");
      sb_append_char(sb, itoc(p->next->i));
      sb_append(sb, ",");
      sb_append_char(sb, itoc(p->next->next->i));
      sb_append(sb, ")");
    }
    else if (rule == XXRES_JUST) {
      Ilist p = g->u.lst;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_id(sb, p->i, map);
      sb_append(sb, ",");
      sb_append_char(sb, itoc(p->next->i));
      sb_append(sb, ")");
    }
    else if (rule == EXPAND_DEF_JUST) {
      Ilist p = g->u.lst;
      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_id(sb, p->i, map);
      sb_append(sb, ",");
      sb_append_id(sb, p->next->i, map);
      sb_append(sb, ")");
    }
    else if (rule == BACK_DEMOD_JUST ||
	     rule == BACK_UNIT_DEL_JUST ||
	     rule == NEW_SYMBOL_JUST ||
	     rule == COPY_JUST ||
	     rule == DENY_JUST ||
	     rule == CLAUSIFY_JUST ||
	     rule == PROPOSITIONAL_JUST) {
      int id = g->u.id;
      sb_append(sb, jstring(g));
      sb_append(sb, "\np ");
      sb_append_id(sb, id, map);
    }
    else if (rule == FLIP_JUST ||
	     rule == XX_JUST ||
	     rule == EVAL_JUST ||
	     rule == MERGE_JUST) {
      /* int id = g->u.id; */

#if 1
      /* BV(2007-jul-10) */
      sb_append(sb, "(flip)");
      /* break; */
#endif

    }
    else if (rule == PARA_JUST || rule == PARA_FX_JUST ||
	     rule == PARA_IX_JUST || rule == PARA_FX_IX_JUST) {
      Parajust p = g->u.para;

#if 1
      /* BV(2007-jul-10) */
      sb_append(sb, "para");
      sb_append(sb, "\np ");
      sb_append_id(sb, p->from_id, map);
      sb_append(sb, "\np ");
      sb_append_id(sb, p->into_id, map);
      /* break; */
#endif

    }
    else if (rule == INSTANCE_JUST) {
      Plist p;

      sb_append(sb, jstring(g));
      sb_append(sb, "(");
      sb_append_int(sb, g->u.instance->parent_id);
      sb_append(sb, ",[");

      for (p = g->u.instance->pairs; p; p = p->next) {
	sb_write_term(sb, p->v);
	if (p->next)
	  sb_append(sb, ",");
      }
      sb_append(sb, "])");
    }
    else if (rule == IVY_JUST) {
      sb_append(sb, jstring(g));
    }
    else {
      printf("\nunknown rule: %d\n", rule);
      fatal_error("sb_write_just: unknown rule");
    }
    g = g->next;
    /* if (g) */
    /*   sb_append(sb, ","); */
    sb_append(sb, "\n");
  }
  /* sb_append(sb, "]."); */
}  /* sb_tagged_write_just */

/*************
 *
 *   tptp_rule_name()
 *
 *   Map Prover9 justification type to TSTP inference rule name.
 *
 *************/

/* PUBLIC */
const char *tptp_rule_name(Just_type type)
{
  switch (type) {
  case DENY_JUST:          return "assume_negation";
  case CLAUSIFY_JUST:      return "clausify";
  case COPY_JUST:          return "copy";
  case BINARY_RES_JUST:    return "resolve";
  case HYPER_RES_JUST:     return "hyper";
  case UR_RES_JUST:        return "ur";
  case FACTOR_JUST:        return "factor";
  case XXRES_JUST:         return "xxres";
  case PARA_JUST:
  case PARA_FX_JUST:
  case PARA_IX_JUST:
  case PARA_FX_IX_JUST:    return "paramod";
  case BACK_DEMOD_JUST:    return "back_demod";
  case BACK_UNIT_DEL_JUST: return "back_unit_del";
  case NEW_SYMBOL_JUST:    return "new_symbol";
  case EXPAND_DEF_JUST:    return "expand_def";
  case PROPOSITIONAL_JUST: return "propositional";
  case INSTANCE_JUST:      return "instantiate";
  case DEMOD_JUST:         return "rewrite";
  case UNIT_DEL_JUST:      return "unit_del";
  case FLIP_JUST:          return "flip";
  case MERGE_JUST:         return "merge";
  case EVAL_JUST:          return "eval";
  default:                 return "unknown";
  }
}  /* tptp_rule_name */

