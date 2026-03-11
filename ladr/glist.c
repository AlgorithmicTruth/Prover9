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

#include "glist.h"
#include "memory.h"

/*
 * memory management
 */

#define PTRS_ILIST PTRS(sizeof(struct ilist))
static unsigned Ilist_gets, Ilist_frees;

#define PTRS_PLIST PTRS(sizeof(struct plist))
static unsigned Plist_gets, Plist_frees;

#define PTRS_I2LIST PTRS(sizeof(struct i2list))
static unsigned I2list_gets, I2list_frees;

#define PTRS_I3LIST PTRS(sizeof(struct i3list))
static unsigned I3list_gets, I3list_frees;

/*************
 *
 *   Ilist get_ilist()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist get_ilist(void)
{
  Ilist p = get_mem(PTRS_ILIST);
  p->next = NULL;
  Ilist_gets++;
  return(p);
}  /* get_ilist */

/*************
 *
 *    free_ilist()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void free_ilist(Ilist p)
{
  free_mem(p, PTRS_ILIST);
  Ilist_frees++;
}  /* free_ilist */

/*************
 *
 *   Plist get_plist()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist get_plist(void)
{
  Plist p = get_mem(PTRS_PLIST);
  p->next = NULL;
  Plist_gets++;
  return(p);
}  /* get_plist */

/*************
 *
 *    free_plist()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void free_plist(Plist p)
{
  free_mem(p, PTRS_PLIST);
  Plist_frees++;
}  /* free_plist */

/*************
 *
 *   I2list get_i2list()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
I2list get_i2list(void)
{
  I2list p = get_mem(PTRS_I2LIST);
  p->next = NULL;
  I2list_gets++;
  return(p);
}  /* get_i2list */

/*************
 *
 *    free_i2list()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void free_i2list(I2list p)
{
  free_mem(p, PTRS_I2LIST);
  I2list_frees++;
}  /* free_i2list */

/*************
 *
 *   I3list get_i3list()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
I3list get_i3list(void)
{
  I3list p = get_mem(PTRS_I3LIST);
  p->next = NULL;
  I3list_gets++;
  return(p);
}  /* get_i3list */

/*************
 *
 *    free_i3list()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void free_i3list(I3list p)
{
  free_mem(p, PTRS_I3LIST);
  I3list_frees++;
}  /* free_i3list */

/*************
 *
 *   fprint_glist_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for data types
associated with the glist package.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_glist_mem(FILE *fp, BOOL heading)
{
  int n;
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");

  n = sizeof(struct ilist);
  fprintf(fp, "ilist (%4d)        %11u%11u%11u%9.1f K\n",
          n, Ilist_gets, Ilist_frees,
          Ilist_gets - Ilist_frees,
          ((Ilist_gets - Ilist_frees) * n) / 1024.);

  n = sizeof(struct plist);
  fprintf(fp, "plist (%4d)        %11u%11u%11u%9.1f K\n",
          n, Plist_gets, Plist_frees,
          Plist_gets - Plist_frees,
          ((Plist_gets - Plist_frees) * n) / 1024.);

  n = sizeof(struct i2list);
  fprintf(fp, "i2list (%4d)       %11u%11u%11u%9.1f K\n",
          n, I2list_gets, I2list_frees,
          I2list_gets - I2list_frees,
          ((I2list_gets - I2list_frees) * n) / 1024.);

}  /* fprint_glist_mem */

/*************
 *
 *   p_glist_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to stdout) memory usage statistics for data types
associated with the glist package.
*/

/* PUBLIC */
void p_glist_mem()
{
  fprint_glist_mem(stdout, TRUE);
}  /* p_glist_mem */

/*
 *  end of memory management
 */

/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/

/*************
 *
 *   plist_cat()
 *
 *************/

/* DOCUMENTATION
Concatenate two Plists and return the result.  The result is constructed
from the arguments, so do not refer to either of the arguments after the call.
<P>
That is, both args are destroyed.
*/

/* PUBLIC */
Plist plist_cat(Plist p1, Plist p2)
{
  if (p1 == NULL)
    return p2;
  else if (p2 == NULL)
    return p1;
  else {
    Plist p = p1;
    while (p->next != NULL)
      p = p->next;
    p->next = p2;
    return p1;
  }
}  /* plist_cat */

/*************
 *
 *   plist_cat2()
 *
 *************/

/* DOCUMENTATION
Concatenate two Plists and return the result.
In this version, the second plist is copied and
placed at the end of p1.
<P>
That is, the first arg is destroyed, and the second
is preserved.
*/

/* PUBLIC */
Plist plist_cat2(Plist p1, Plist p2)
{
  return plist_cat(p1, copy_plist(p2));
}  /* plist_cat2 */

/*************
 *
 *   plist_pop()
 *
 *************/

/* DOCUMENTATION
This routine takes a nonempty Plist, removes and frees the first node
(ignoring the contents), and returns the remainder of the list.
*/

/* PUBLIC */
Plist plist_pop(Plist p)
{
  Plist q = p;
  p = p->next;
  free_plist(q);
  return p;
}  /* plist_pop */

/*************
 *
 *   plist_count()
 *
 *************/

/* DOCUMENTATION
This routine returns the length of a Plist.
*/

/* PUBLIC */
int plist_count(Plist p)
{
  int n;
  for (n = 0; p; p = p->next, n++);
  return(n);
}  /* plist_count */

/*************
 *
 *   rev_app_plist(p1, p2)
 *
 *************/

static
Plist rev_app_plist(Plist p1, Plist p2)
{
  while (p1 != NULL) {
    Plist p3 = p1->next;
    p1->next = p2;
    p2 = p1;
    p1 = p3;
  }
  return p2;
}  /* rev_app_plist */

/*************
 *
 *     reverse_plist(p1)
 *
 *************/

/* DOCUMENTATION
This routine reverses a Plist.  The list is reversed in-place,
so you should not refer to the argument after calling this routine.
A good way to use it is like this:
<PRE>
p = reverse_plist(p);
</PRE>
*/

/* PUBLIC */
Plist reverse_plist(Plist p)
{
  return rev_app_plist(p, NULL);
}  /* reverse_plist */

/*************
 *
 *   copy_plist(p)
 *
 *************/

/* DOCUMENTATION
This routine copies a Plist (the whole list) and returns the copy.
*/

/* PUBLIC */
Plist copy_plist(Plist p)
{
  Plist start, p1, p2;

  start = NULL;
  p2 = NULL;
  for ( ; p; p = p->next) {
    p1 = get_plist();
    p1->v = p->v;
    p1->next = NULL;
    if (p2)
      p2->next = p1;
    else
      start = p1;
    p2 = p1;
  }
  return(start);
}  /* copy_plist */

/*************
 *
 *   zap_plist(p)
 *
 *************/

/* DOCUMENTATION
This routine frees a Plist (the whole list).  The things to which
the members point are not freed.
*/

/* PUBLIC */
void zap_plist(Plist p)
{
  Plist curr, prev;

  curr = p;
  while (curr != NULL) {
    prev = curr;
    curr = curr->next;
    free_plist(prev);
  }
}  /* zap_plist */

/*************
 *
 *   plist_append()
 *
 *************/

/* DOCUMENTATION
This routine appends a pointer to a Plist.  The updated Plist
is returned.
*/

/* PUBLIC */
Plist plist_append(Plist lst, void *v)
{
  Plist g = get_plist();
  g->v = v;
  g->next = NULL;
  if (lst == NULL)
    return g;
  else {
    Plist p = lst;
    while (p->next != NULL)
      p = p->next;
    p->next = g;
    return lst;
  }
}  /* plist_append */

/*************
 *
 *   plist_prepend()
 *
 *************/

/* DOCUMENTATION
This routine inserts a pointer as the first member of a Plist.
The updated Plist is returned.
*/

/* PUBLIC */
Plist plist_prepend(Plist lst, void *v)
{
  Plist g = get_plist();
  g->v = v;
  g->next = lst;
  return g;
}  /* plist_prepend */

/*************
 *
 *   plist_member()
 *
 *************/

/* DOCUMENTATION
This function checks if a pointer is a member of a Plist.
*/

/* PUBLIC */
BOOL plist_member(Plist lst, void *v)
{
  while (lst != NULL) {
    if (lst->v == v)
      return TRUE;
    lst = lst->next;
  }
  return FALSE;
}  /* plist_member */

/*************
 *
 *   plist_subtract()
 *
 *************/

/* DOCUMENTATION
Return the members of p1 that are not in p2.
<P>
The arguments are not changed.
*/

/* PUBLIC */
Plist plist_subtract(Plist p1, Plist p2)
{
  /* Build result in reverse, then reverse to preserve order. */
  Plist r = NULL;
  while (p1 != NULL) {
    if (!plist_member(p2, p1->v))
      r = plist_prepend(r, p1->v);
    p1 = p1->next;
  }
  return reverse_plist(r);
}  /* plist_subtract */

/*************
 *
 *   plist_subset()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL plist_subset(Plist a, Plist b)
{
  while (a != NULL) {
    if (!plist_member(b, a->v))
      return FALSE;
    a = a->next;
  }
  return TRUE;
}  /* plist_subset */

/*************
 *
 *   plist_remove()
 *
 *************/

/* DOCUMENTATION
Remove the first occurrence of a pointer from a Plist.
*/

/* PUBLIC */
Plist plist_remove(Plist p, void *v)
{
  Plist *pp = &p;
  while (*pp != NULL) {
    if ((*pp)->v == v) {
      Plist x = *pp;
      *pp = x->next;
      free_plist(x);
      return p;
    }
    pp = &(*pp)->next;
  }
  fatal_error("plist_remove: pointer not found");
  return p;  /* not reached */
}  /* plist_remove */

/*************
 *
 *   plist_remove_string()
 *
 *************/

/* DOCUMENTATION
Remove the first occurrence of a pointer from a Plist.
*/

/* PUBLIC */
Plist plist_remove_string(Plist p, char *s)
{
  Plist *pp = &p;
  while (*pp != NULL) {
    if (str_ident((*pp)->v, s)) {
      Plist x = *pp;
      *pp = x->next;
      free_plist(x);
      return p;
    }
    pp = &(*pp)->next;
  }
  fatal_error("plist_remove_string: pointer not found");
  return p;  /* not reached */
}  /* plist_remove_string */

/*************
 *
 *   sort_plist()
 *
 *************/

/* DOCUMENTATION
 */

/* PUBLIC */
Plist sort_plist(Plist objects,	Ordertype (*comp_proc) (void *, void *))
{
  int n = plist_count(objects);
  void **a = safe_malloc(n * sizeof(void *));
  int i;
  Plist p;
  for (p = objects, i = 0; p; p = p->next, i++)
    a[i] = p->v;
  merge_sort(a, n, comp_proc);
  for (p = objects, i = 0; p; p = p->next, i++)
    p->v = a[i];
  safe_free(a);
  return objects;
}  /* sort_plist */

/*************
 *
 *   plist_remove_last()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist plist_remove_last(Plist p)
{
  if (p == NULL)
    return NULL;
  if (p->next == NULL) {
    free_plist(p);
    return NULL;
  }
  Plist q = p;
  while (q->next->next != NULL)
    q = q->next;
  free_plist(q->next);
  q->next = NULL;
  return p;
}  /* plist_remove_last */

/*************
 *
 *   position_of_string_in_plist()
 *
 *************/

/* DOCUMENTATION
Count from 1; return -1 if the string is not in the Plist.
*/

/* PUBLIC */
int position_of_string_in_plist(char *s, Plist p)
{
  int pos = 1;
  while (p != NULL) {
    if (str_ident(s, p->v))
      return pos;
    p = p->next;
    pos++;
  }
  return -1;
}  /* position_of_string_in_plist */

/*************
 *
 *   string_member_plist()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL string_member_plist(char *s, Plist p)
{
  return position_of_string_in_plist(s, p) >= 0;
}  /* string_member_plist */

/*************
 *
 *   longest_string_in_plist()
 *
 *************/

/* DOCUMENTATION
Return -1 if the Plist is empty.
*/

/* PUBLIC */
int longest_string_in_plist(Plist p)
{
  int best = -1;
  while (p != NULL) {
    int n = strlen(p->v);
    if (n > best)
      best = n;
    p = p->next;
  }
  return best;
}  /* longest_string_in_plist */

/*************
 *
 *   ith_in_plist()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void *ith_in_plist(Plist p, int i)
{
  while (p != NULL && i > 1) {
    p = p->next;
    i--;
  }
  if (p == NULL || i <= 0)
    return NULL;
  return p->v;
}  /* ith_in_plist */

/*************
 *
 *   plist_last()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void *plist_last(Plist p)
{
  if (p == NULL)
    return NULL;
  while (p->next != NULL)
    p = p->next;
  return p->v;
}  /* plist_last */

/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/

/*************
 *
 *   ilist_cat()
 *
 *************/

/* DOCUMENTATION
Concatenate two Ilists and return the result.  The result is constructed
from the arguments, so do not refer to either of the arguments after the call.
<P>
That is, both arguments are "used up".
*/

/* PUBLIC */
Ilist ilist_cat(Ilist p1, Ilist p2)
{
  if (p1 == NULL)
    return p2;
  else if (p2 == NULL)
    return p1;
  else {
    Ilist p = p1;
    while (p->next != NULL)
      p = p->next;
    p->next = p2;
    return p1;
  }
}  /* ilist_cat */

/*************
 *
 *   ilist_cat2()
 *
 *************/

/* DOCUMENTATION
Concatenate two Ilists and return the result.
In this version, the second ilist is copied and
placed at the end of p1.  That is, p1 is "used up",
but p2 is not.
*/

/* PUBLIC */
Ilist ilist_cat2(Ilist p1, Ilist p2)
{
  return ilist_cat(p1, copy_ilist(p2));
}  /* ilist_cat2 */

/*************
 *
 *   ilist_pop()
 *
 *************/

/* DOCUMENTATION
This routine takes a nonempty Ilist, removes and frees the first node
(ignoring the contents), and returns the remainder of the list.
*/

/* PUBLIC */
Ilist ilist_pop(Ilist p)
{
  Ilist q = p;
  p = p->next;
  free_ilist(q);
  return p;
}  /* ilist_pop */

/*************
 *
 *   ilist_count()
 *
 *************/

/* DOCUMENTATION
This routine returns the length of a Ilist.
*/

/* PUBLIC */
int ilist_count(Ilist p)
{
  int n;
  for (n = 0; p; p = p->next, n++);
  return(n);
}  /* ilist_count */

/*************
 *
 *   rev_app_ilist(p1, p2)
 *
 *************/

static
Ilist rev_app_ilist(Ilist p1, Ilist p2)
{
  while (p1 != NULL) {
    Ilist p3 = p1->next;
    p1->next = p2;
    p2 = p1;
    p1 = p3;
  }
  return p2;
}  /* rev_app_ilist */

/*************
 *
 *     reverse_ilist(p1)
 *
 *************/

/* DOCUMENTATION
This routine reverses a Ilist.  The list is reversed in-place,
so you should not refer to the argument after calling this routine.
A good way to use it is like this:
<PRE>
p = reverse_ilist(p);
</PRE>
*/

/* PUBLIC */
Ilist reverse_ilist(Ilist p)
{
  return rev_app_ilist(p, NULL);
}  /* reverse_ilist */

/*************
 *
 *   copy_ilist(p)
 *
 *************/

/* DOCUMENTATION
This routine copies a Ilist (the whole list) and returns the copy.
*/

/* PUBLIC */
Ilist copy_ilist(Ilist p)
{
  Ilist start, p1, p2;

  start = NULL;
  p2 = NULL;
  for ( ; p; p = p->next) {
    p1 = get_ilist();
    p1->i = p->i;
    p1->next = NULL;
    if (p2)
      p2->next = p1;
    else
      start = p1;
    p2 = p1;
  }
  return(start);
}  /* copy_ilist */

/*************
 *
 *   zap_ilist(p)
 *
 *************/

/* DOCUMENTATION
This routine frees a Ilist (the whole list).
*/

/* PUBLIC */
void zap_ilist(Ilist p)
{
  Ilist curr, prev;

  curr = p;
  while (curr != NULL) {
    prev = curr;
    curr = curr->next;
    free_ilist(prev);
  }
}  /* zap_ilist */

/*************
 *
 *   ilist_append()
 *
 *************/

/* DOCUMENTATION
This routine appends an integer to a Ilist.  The updated Ilist
is returned.
*/

/* PUBLIC */
Ilist ilist_append(Ilist lst, int i)
{
  Ilist g = get_ilist();
  g->i = i;
  g->next = NULL;
  if (lst == NULL)
    return g;
  else {
    Ilist p = lst;
    while (p->next != NULL)
      p = p->next;
    p->next = g;
    return lst;
  }
}  /* ilist_append */

/*************
 *
 *   ilist_prepend()
 *
 *************/

/* DOCUMENTATION
This routine inserts an integer as the first member of a Ilist.
The updated Ilist is returned.
*/

/* PUBLIC */
Ilist ilist_prepend(Ilist lst, int i)
{
  Ilist g = get_ilist();
  g->i = i;
  g->next = lst;
  return g;
}  /* ilist_prepend */

/*************
 *
 *   ilist_last()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist ilist_last(Ilist lst)
{
  if (lst == NULL)
    return NULL;
  while (lst->next != NULL)
    lst = lst->next;
  return lst;
}  /* ilist_last */

/*************
 *
 *   ilist_member()
 *
 *************/

/* DOCUMENTATION
This function checks if an integer is a member of a Ilist.
(If a node in the Ilist contains a pointer instead of an integer,
the result is undefined.)
*/

/* PUBLIC */
BOOL ilist_member(Ilist lst, int i)
{
  while (lst != NULL) {
    if (lst->i == i)
      return TRUE;
    lst = lst->next;
  }
  return FALSE;
}  /* ilist_member */

/*************
 *
 *   ilist_subtract()
 *
 *************/

/* DOCUMENTATION
Return the members of p1 that are not in p2.
<P>
The arguments are not changed.
*/

/* PUBLIC */
Ilist ilist_subtract(Ilist p1, Ilist p2)
{
  Ilist r = NULL;
  while (p1 != NULL) {
    if (!ilist_member(p2, p1->i))
      r = ilist_prepend(r, p1->i);
    p1 = p1->next;
  }
  return reverse_ilist(r);
}  /* ilist_subtract */

/*************
 *
 *   ilist_removeall()
 *
 *************/

/* DOCUMENTATION
Remove all occurrences of i.
<P>
The argument is "used up".
*/

/* PUBLIC */
Ilist ilist_removeall(Ilist p, int i)
{
  Ilist *pp = &p;
  while (*pp != NULL) {
    if ((*pp)->i == i) {
      Ilist x = *pp;
      *pp = x->next;
      free_ilist(x);
    }
    else
      pp = &(*pp)->next;
  }
  return p;
}  /* ilist_removeall */

/*************
 *
 *   ilist_intersect()
 *
 *************/

/* DOCUMENTATION
Construct the intersection (as a new Ilist).
<P>
The arguments are not changed.
*/

/* PUBLIC */
Ilist ilist_intersect(Ilist a, Ilist b)
{
  Ilist r = NULL;
  while (a != NULL) {
    if (ilist_member(b, a->i))
      r = ilist_prepend(r, a->i);
    a = a->next;
  }
  return reverse_ilist(r);
}  /* ilist_intersect */

/*************
 *
 *   ilist_union()
 *
 *************/

/* DOCUMENTATION
Construct the union (as a new Ilist).
<p>
The arguments need not be sets, the result is a set.
<p>
The arguments are not changed.
*/

/* PUBLIC */
Ilist ilist_union(Ilist a, Ilist b)
{
  /* Start with a deduplicated copy of b. */
  Ilist result = ilist_set(b);
  /* Prepend elements of a not already in result, in reverse order. */
  Ilist extras = NULL;
  while (a != NULL) {
    if (!ilist_member(result, a->i))
      extras = ilist_prepend(extras, a->i);
    a = a->next;
  }
  /* extras is in reverse order; prepending reversed restores original order. */
  while (extras != NULL) {
    Ilist tmp = extras->next;
    extras->next = result;
    result = extras;
    extras = tmp;
  }
  return result;
}  /* ilist_union */

/*************
 *
 *   ilist_set()
 *
 *************/

/* DOCUMENTATION
Take a list of integers and remove duplicates.
This creates a new list and leave the old list as it was.
Don't make any assumptions about the order of the result.
*/

/* PUBLIC */
Ilist ilist_set(Ilist m)
{
  /* Build deduplicated copy. Walk in reverse to preserve original order. */
  Ilist rev = NULL;
  Ilist p;
  for (p = m; p != NULL; p = p->next)
    rev = ilist_prepend(rev, p->i);
  /* rev is m reversed. Now build result from rev, skipping dups. */
  Ilist result = NULL;
  while (rev != NULL) {
    Ilist tmp = rev->next;
    if (!ilist_member(result, rev->i)) {
      rev->next = result;
      result = rev;
    }
    else
      free_ilist(rev);
    rev = tmp;
  }
  return result;
}  /* ilist_set */

/*************
 *
 *   ilist_rem_dups()
 *
 *************/

/* DOCUMENTATION
Take a list of integers and remove duplicates.
<P>
This version "uses up" the argument.
*/

/* PUBLIC */
Ilist ilist_rem_dups(Ilist m)
{
  /* Reverse first so we keep earliest occurrence when scanning from tail. */
  Ilist rev = NULL;
  while (m != NULL) {
    Ilist tmp = m->next;
    m->next = rev;
    rev = m;
    m = tmp;
  }
  /* Build result from rev, skipping dups. */
  Ilist result = NULL;
  while (rev != NULL) {
    Ilist tmp = rev->next;
    if (!ilist_member(result, rev->i)) {
      rev->next = result;
      result = rev;
    }
    else
      free_ilist(rev);
    rev = tmp;
  }
  return result;
}  /* ilist_rem_dups */

/*************
 *
 *   ilist_is_set()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL ilist_is_set(Ilist a)
{
  while (a != NULL) {
    if (ilist_member(a->next, a->i))
      return FALSE;
    a = a->next;
  }
  return TRUE;
}  /* ilist_is_set */

/*************
 *
 *   ilist_subset()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL ilist_subset(Ilist a, Ilist b)
{
  while (a != NULL) {
    if (!ilist_member(b, a->i))
      return FALSE;
    a = a->next;
  }
  return TRUE;
}  /* ilist_subset */

/*************
 *
 *   fprint_ilist()
 *
 *************/

/* DOCUMENTATION
The list of integers is printed to FILE *fp like this: (4 5 1 3),
without a newline.
*/

/* PUBLIC */
void fprint_ilist(FILE *fp, Ilist p)
{
  fprintf(fp, "(");
  for (; p != NULL; p = p->next) {
    fprintf(fp, "%d", p->i);
    fprintf(fp, "%s", p->next ? " " : "");
  }
  fprintf(fp, ")");
  fflush(fp);
}  /* fprint_ilist */

/*************
 *
 *   p_ilist()
 *
 *************/

/* DOCUMENTATION
The list of integers is printed to stdout like this: (4 5 1 3),
with a '\n' at the end.
*/

/* PUBLIC */
void p_ilist(Ilist p)
{
  fprint_ilist(stdout, p);
  printf("\n");
  fflush(stdout);
}  /* p_ilist */

/*************
 *
 *   ilist_copy()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist ilist_copy(Ilist p)
{
  Ilist start = NULL, tail = NULL;
  while (p != NULL) {
    Ilist n = get_ilist();
    n->i = p->i;
    n->next = NULL;
    if (tail)
      tail->next = n;
    else
      start = n;
    tail = n;
    p = p->next;
  }
  return start;
}  /* ilist_copy */

/*************
 *
 *   ilist_remove_last()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist ilist_remove_last(Ilist p)
{
  if (p == NULL)
    return NULL;
  if (p->next == NULL) {
    free_ilist(p);
    return NULL;
  }
  Ilist q = p;
  while (q->next->next != NULL)
    q = q->next;
  free_ilist(q->next);
  q->next = NULL;
  return p;
}  /* ilist_remove_last */

/*************
 *
 *   ilist_occurrences()
 *
 *************/

/* DOCUMENTATION
How many times does an integer occur in an ilist?
*/

/* PUBLIC */
int ilist_occurrences(Ilist p, int i)
{
  int count = 0;
  while (p != NULL) {
    if (p->i == i)
      count++;
    p = p->next;
  }
  return count;
}  /* ilist_occurrences */

/*************
 *
 *   ilist_insert_up()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist ilist_insert_up(Ilist p, int i)
{
  Ilist *pp = &p;
  while (*pp != NULL && (*pp)->i < i)
    pp = &(*pp)->next;
  Ilist g = get_ilist();
  g->i = i;
  g->next = *pp;
  *pp = g;
  return p;
}  /* ilist_insert_up */

/*************
 *
 *   position_in_ilist()
 *
 *************/

/* DOCUMENTATION
Count from 1; return -1 if the int is not in the Ilist.
*/

/* PUBLIC */
int position_in_ilist(int i, Ilist p)
{
  int pos = 1;
  while (p != NULL) {
    if (p->i == i)
      return pos;
    p = p->next;
    pos++;
  }
  return -1;
}  /* position_in_ilist */

/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/

/*************
 *
 *   zap_i2list(p)
 *
 *************/

/* DOCUMENTATION
This routine frees an I2list (the whole list).
*/

/* PUBLIC */
void zap_i2list(I2list p)
{
  I2list curr, prev;

  curr = p;
  while (curr != NULL) {
    prev = curr;
    curr = curr->next;
    free_i2list(prev);
  }
}  /* zap_i2list */

/*************
 *
 *   i2list_append()
 *
 *************/

/* DOCUMENTATION
This routine appends an integer to a I2list.  The updated I2list
is returned.
*/

/* PUBLIC */
I2list i2list_append(I2list lst, int i, int j)
{
  I2list g = get_i2list();
  g->i = i;
  g->j = j;
  g->next = NULL;
  if (lst == NULL)
    return g;
  else {
    I2list p = lst;
    while (p->next != NULL)
      p = p->next;
    p->next = g;
    return lst;
  }
}  /* i2list_append */

/*************
 *
 *   i2list_prepend()
 *
 *************/

/* DOCUMENTATION
This routine inserts an integer triple as the first member of a I2list.
The updated I2list is returned.
*/

/* PUBLIC */
I2list i2list_prepend(I2list lst, int i, int j)
{
  I2list g = get_i2list();
  g->i = i;
  g->j = j;
  g->next = lst;
  return g;
}  /* i2list_prepend */

/*************
 *
 *   i2list_removeall()
 *
 *************/

/* DOCUMENTATION
Remove all occurrences of i.
<P>
The argument is "used up".
*/

/* PUBLIC */
I2list i2list_removeall(I2list p, int i)
{
  I2list *pp = &p;
  while (*pp != NULL) {
    if ((*pp)->i == i) {
      I2list x = *pp;
      *pp = x->next;
      free_i2list(x);
    }
    else
      pp = &(*pp)->next;
  }
  return p;
}  /* i2list_removeall */

/*************
 *
 *   i2list_member()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
I2list i2list_member(I2list lst, int i)
{
  while (lst != NULL) {
    if (lst->i == i)
      return lst;
    lst = lst->next;
  }
  return NULL;
}  /* i2list_member */

/*************
 *
 *   p_i2list()
 *
 *************/

/* DOCUMENTATION
The list of integers is printed to stdout like this: (4 5 1 3),
with a '\n' at the end.
*/

/* PUBLIC */
void p_i2list(I2list p)
{
  printf("(");
  for (; p != NULL; p = p->next) {
    printf("%d/%d", p->i, p->j);
    printf("%s", p->next ? " " : "");
  }
  printf(")\n");
  fflush(stdout);
}  /* p_i2list */

/*************
 *
 *   i2list_count()
 *
 *************/

/* DOCUMENTATION
This routine returns the length of a I2list.
*/

/* PUBLIC */
int i2list_count(I2list p)
{
  int n;
  for (n = 0; p; p = p->next, n++);
  return(n);
}  /* i2list_count */

/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/

/*************
 *
 *   i3list_member()
 *
 *************/

/* DOCUMENTATION
This function checks if a triple of integers is a member of a I3list.
*/

/* PUBLIC */
BOOL i3list_member(I3list lst, int i, int j, int k)
{
  while (lst != NULL) {
    if (lst->i == i && lst->j == j && lst->k == k)
      return TRUE;
    lst = lst->next;
  }
  return FALSE;
}  /* i3list_member */

/*************
 *
 *   i3list_append()
 *
 *************/

/* DOCUMENTATION
This routine appends an integer to a I3list.  The updated I3list
is returned.
*/

/* PUBLIC */
I3list i3list_append(I3list lst, int i, int j, int k)
{
  I3list g = get_i3list();
  g->i = i;
  g->j = j;
  g->k = k;
  g->next = NULL;
  if (lst == NULL)
    return g;
  else {
    I3list p = lst;
    while (p->next != NULL)
      p = p->next;
    p->next = g;
    return lst;
  }
}  /* i3list_append */

/*************
 *
 *   i3list_prepend()
 *
 *************/

/* DOCUMENTATION
This routine inserts an integer triple as the first member of a I3list.
The updated I3list is returned.
*/

/* PUBLIC */
I3list i3list_prepend(I3list lst, int i, int j, int k)
{
  I3list g = get_i3list();
  g->i = i;
  g->j = j;
  g->k = k;
  g->next = lst;
  return g;
}  /* i3list_prepend */

/*************
 *
 *   zap_i3list(p)
 *
 *************/

/* DOCUMENTATION
This routine frees a I3list (the whole list).
*/

/* PUBLIC */
void zap_i3list(I3list p)
{
  I3list curr, prev;

  curr = p;
  while (curr != NULL) {
    prev = curr;
    curr = curr->next;
    free_i3list(prev);
  }
}  /* zap_i3list */

/*************
 *
 *   rev_app_i3list(p1, p2)
 *
 *************/

static
I3list rev_app_i3list(I3list p1, I3list p2)
{
  while (p1 != NULL) {
    I3list p3 = p1->next;
    p1->next = p2;
    p2 = p1;
    p1 = p3;
  }
  return p2;
}  /* rev_app_i3list */

/*************
 *
 *     reverse_i3list(p1)
 *
 *************/

/* DOCUMENTATION
This routine reverses a I3list.  The 3list is reversed in-place,
so you should not refer to the argument after calling this routine.
A good way to use it is like this:
<PRE>
p = reverse_i3list(p);
</PRE>
*/

/* PUBLIC */
I3list reverse_i3list(I3list p)
{
  return rev_app_i3list(p, NULL);
}  /* reverse_i3list */

/*************
 *
 *   copy_i3list(p)
 *
 *************/

/* DOCUMENTATION
This routine copies a I3list (the whole 3list) and returns the copy.
*/

/* PUBLIC */
I3list copy_i3list(I3list p)
{
  I3list start, p1, p2;

  start = NULL;
  p2 = NULL;
  for ( ; p; p = p->next) {
    p1 = get_i3list();
    p1->i = p->i;
    p1->j = p->j;
    p1->k = p->k;
    p1->next = NULL;
    if (p2)
      p2->next = p1;
    else
      start = p1;
    p2 = p1;
  }
  return(start);
}  /* copy_i3list */

/*************
 *
 *   i3list_count()
 *
 *************/

/* DOCUMENTATION
This routine returns the length of a I3list.
*/

/* PUBLIC */
int i3list_count(I3list p)
{
  int n;
  for (n = 0; p; p = p->next, n++);
  return(n);
}  /* i3list_count */

/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/

/*************
 *
 *   alist_insert()
 *
 *************/

/* DOCUMENTATION
Alists (association list) for integers.
Insert key/value pairs.  With assoc(key), retreive value.
If a key has more than one value, the most recent is returned.
It an key is not in the alist, INT_MIN is returned.
An alist can be freed with zap_i2list(alist).
This is not efficient, because no hashing is done; lookups are linear.
*/

/* PUBLIC */
I2list alist_insert(I2list p, int key, int val)
{
  return i2list_prepend(p, key, val);
}  /* alist_insert */

/*************
 *
 *   assoc()
 *
 *************/

/* DOCUMENTATION
See alist_insert.
*/

/* PUBLIC */
int assoc(I2list p, int key)
{
  while (p != NULL) {
    if (p->i == key)
      return p->j;
    p = p->next;
  }
  return INT_MIN;
}  /* assoc */

/*************
 *
 *   alist2_insert()
 *
 *************/

/* DOCUMENTATION
Alist2 (association list) for pairs of integers.
Insert key/<value-a,value-b> pairs.
With assoc2a(key), retreive value-a.
With assoc2b(key), retreive value-b.
If a key has more than one value pair, the most recent is returned.
It a key is not in the alist2, INT_MIN is returned.
An alist2 can be freed with zap_i3list(alist2).
*/

/* PUBLIC */
I3list alist2_insert(I3list p, int key, int a, int b)
{
  return i3list_prepend(p, key, a, b);
}  /* alist2_insert */

/*************
 *
 *   assoc2a()
 *
 *************/

/* DOCUMENTATION
See alist2_insert.
*/

/* PUBLIC */
int assoc2a(I3list p, int key)
{
  while (p != NULL) {
    if (p->i == key)
      return p->j;
    p = p->next;
  }
  return INT_MIN;
}  /* assoc2a */

/*************
 *
 *   assoc2b()
 *
 *************/

/* DOCUMENTATION
See alist2_insert.
*/

/* PUBLIC */
int assoc2b(I3list p, int key)
{
  while (p != NULL) {
    if (p->i == key)
      return p->k;
    p = p->next;
  }
  return INT_MIN;
}  /* assoc2b */

/*************
 *
 *   alist2_remove()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
I3list alist2_remove(I3list p, int key)
{
  I3list *pp = &p;
  while (*pp != NULL) {
    if ((*pp)->i == key) {
      I3list x = *pp;
      *pp = x->next;
      free_i3list(x);
    }
    else
      pp = &(*pp)->next;
  }
  return p;
}  /* alist2_remove */

/*****************************************************************************/
/*****************************************************************************/
/*****************************************************************************/

/*
  Multiset of integers is implemented with I2list, that is,
  list of pairs of integers: <value, number-of-occurrences>.
 */

/*************
 *
 *   i2list_multimember()
 *
 *************/

/* DOCUMENTATION
Is <i,n> a multimember of multiset b?
*/

/* PUBLIC */
BOOL i2list_multimember(I2list b, int i, int n)
{
  while (b != NULL) {
    if (i == b->i)
      return n <= b->j;
    b = b->next;
  }
  return FALSE;
}  /* i2list_multimember */

/*************
 *
 *   i2list_multisubset()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL i2list_multisubset(I2list a, I2list b)
{
  while (a != NULL) {
    if (!i2list_multimember(b, a->i, a->j))
      return FALSE;
    a = a->next;
  }
  return TRUE;
}  /* i2list_multisubset */

/*************
 *
 *   multiset_add_n()
 *
 *************/

/* DOCUMENTATION
Add n occurrences of i to multiset a.
*/

/* PUBLIC */
I2list multiset_add_n(I2list a, int i, int n)
{
  I2list *p = &a;
  while (*p != NULL) {
    if ((*p)->i == i) {
      (*p)->j += n;
      return a;
    }
    p = &(*p)->next;
  }
  /* Not found — append new node at the end. */
  *p = get_i2list();
  (*p)->i = i;
  (*p)->j = n;
  return a;
}  /* multiset_add_n */

/*************
 *
 *   multiset_add()
 *
 *************/

/* DOCUMENTATION
Add 1 occurrence of i to multiset a.
*/

/* PUBLIC */
I2list multiset_add(I2list a, int i)
{
  return multiset_add_n(a, i, 1);
}  /* multiset_add */

/*************
 *
 *   multiset_union()
 *
 *************/

/* DOCUMENTATION
The result is constructed from the arguments,
so do not refer to either of the arguments after the call.
That is, both arguments are "used up".
*/

/* PUBLIC */
I2list multiset_union(I2list a, I2list b)
{
  I2list p;
  for (p = b; p; p = p->next)
    a = multiset_add_n(a, p->i, p->j);
  zap_i2list(b);
  return a;
}  /* multiset_union */

/*************
 *
 *   multiset_to_set()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist multiset_to_set(I2list m)
{
  Ilist start = NULL, tail = NULL;
  while (m != NULL) {
    Ilist p = get_ilist();
    p->i = m->i;
    p->next = NULL;
    if (tail)
      tail->next = p;
    else
      start = p;
    tail = p;
    m = m->next;
  }
  return start;
}  /* multiset_to_set */

/*************
 *
 *   multiset_occurrences()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int multiset_occurrences(I2list m, int i)
{
  I2list a = i2list_member(m, i);
  return (a == NULL ? 0 : a->j);
}  /* multiset_occurrences */

/*************
 *
 *   counts_to_multiset()
 *
 *************/

/* PUBLIC */
I2list counts_to_multiset(int *counts, int n)
{
  I2list result = NULL;
  int i;
  for (i = n - 1; i >= 0; i--) {
    if (counts[i] > 0) {
      I2list node = get_i2list();
      node->i = i;
      node->j = counts[i];
      node->next = result;
      result = node;
    }
  }
  return result;
}  /* counts_to_multiset */

/*************
 *
 *   counts_to_set()
 *
 *************/

/* PUBLIC */
Ilist counts_to_set(int *counts, int n)
{
  Ilist result = NULL;
  int i;
  for (i = n - 1; i >= 0; i--) {
    if (counts[i] > 0) {
      Ilist node = get_ilist();
      node->i = i;
      node->next = result;
      result = node;
    }
  }
  return result;
}  /* counts_to_set */

