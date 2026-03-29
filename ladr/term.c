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

#include "term.h"
#include "memory.h"

/*
  Sharing Variables.  In the original design, no term sharing occurred.
  This allows compact data structures and simpler algorithms for
  processiong terms.  Then we tried sharing variables only (using the
  same data structures).

  In most cases of practical work, nearly all of the leaves in the
  clause spaces are variables (as opposed to constants).  Assuming most
  function applications are binary, this means that variables take up
  about half of the term storage.  We can save all of this by sharing
  variables.

  All terms have a containment field, which points to the containing
  clause.  (If we wished to have terms point to immediate superterms, we
  could do that instead.)  We need containment, because indexing returns
  terms, and we have to get from those terms to the containing clauses.
  BUT, we don't index variables, so we can do without containment
  pointers in variables.

  Making the change to shared variables was easy.  We introduced
  an array of term pointers, static Term Shared_variables[MAX_VNUM], and
  changed get_variable_term to return one of those instead of
  a fresh one.  Also, we eliminated the routine set_variable, which
  changes the variable number of a variable term.  If you want to
  do that now (with shared or with nonshared variables), just free
  the old one and get a new one.

  Things to be careful about:

  (1) Don't change variable numbers of variable terms.  Just use
  get_variable_term and free_term.
  (2) Don't use the container field of variables.

  January 29, 2003.
*/

/* Private definitions and types */

/* _AnyConst matching (Veroff/Justermans, 2016) */
BOOL AnyConstsEnabled = TRUE;

static BOOL AnyConstsInited = FALSE;
static int AnyConsts[MAX_ANYCONSTS];

static Term Shared_variables[MAX_VNUM];

/*
 * memory management
 */

#define PTRS_TERM PTRS(sizeof(struct term))
static unsigned Term_gets, Term_frees;

static unsigned Arg_mem;  /* memory (pointers) for arrays of args */

/*************
 *
 *   Term get_term(arity)
 *
 *************/

static
Term get_term(int arity)
{
  /* This is a little tricky.  The pointers to the subterms are
     in an array (p->args) that is just after (contiguous with)
     the term.

     private_symbol is not initialized.
     args array is not initialized.
   */
  Term p = get_mem(PTRS_TERM + arity);  /* non-initialized memory */
  p->arity = arity;
  if (arity == 0)
    p->args = NULL;
  else {
    void **v = (void **) p;
    p->args = (Term *) (v + PTRS_TERM);  /* just after the (struct term) */
  }
  p->private_flags = 0;
  p->container = NULL;
  p->u.vp = NULL;
  Term_gets++;
  Arg_mem += arity;
  return(p);
}  /* get_term */

/*************
 *
 *    free_term()
 *
 *************/

/* DOCUMENTATION
This routine frees a term node only.  To recursively
free all of the subterms as well, call zap_term(t) instead.
*/

/* PUBLIC */
void free_term(Term p)
{
  if (VARIABLE(p))
    return;  /* variables are never freed, because they are shared */
  Arg_mem -= p->arity;
  free_mem(p, PTRS_TERM + p->arity);
  Term_frees++;
}  /* free_term */

/*************
 *
 *   fprint_term_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) memory usage statistics for Terms.
The Boolean argument heading tells whether to print a heading on the table.
*/

/* PUBLIC */
void fprint_term_mem(FILE *fp, BOOL heading)
{
  int n;
  
  if (heading)
    fprintf(fp, "  type (bytes each)        gets      frees     in use      bytes\n");
  
  n = sizeof(struct term);
  fprintf(fp, "term (%4d)         %11u%11u%11u%9.1f K\n",
	  n, Term_gets, Term_frees, Term_gets - Term_frees,
	  ((Term_gets - Term_frees) * n) / 1024.);
  
  fprintf(fp, "      term arg arrays:                               %9.1f K\n",
	  Arg_mem * BYTES_POINTER / 1024.); 

  /* end of printing for each type */
  
}  /* fprint_term_mem */

/*************
 *
 *   p_term_mem()
 *
 *************/

/* DOCUMENTATION
This routine prints memory usage statistics for Terms to stdout.
*/

/* PUBLIC */
void p_term_mem(void)
{
  fprint_term_mem(stdout, 1);
}  /* p__mem */

/*
 *  end of memory management
 */

/*************
 *
 *   get_variable_term()
 *
 *************/

/* DOCUMENTATION
This routine returns a term of type VARIABLE.
The index of the variable is set to var_num, which  should
be an integer >= 0.
*/

/* PUBLIC */
Term get_variable_term(int var_num)
{
  if (var_num < 0 || var_num >= MAX_VAR)
    fatal_error("get_variable_term: var_num out of range");

  if (var_num >= MAX_VNUM || Shared_variables[var_num] == NULL) {
    Term t = safe_malloc(sizeof(struct term));
    t->private_symbol = var_num;
    t->arity = 0;
    t->private_flags = 0;
    t->container = NULL;
    t->u.id = 0;
    if (var_num >= MAX_VNUM)
      return t;  /* will not be shared */
    else
      Shared_variables[var_num] = t;
  }
  return Shared_variables[var_num];
}  /* get_variable_term */

/*************
 *
 *   get_variable_term_if_exists()
 *
 *   Return the shared variable term for var_num, or NULL if not yet created.
 *   Does NOT allocate.
 *
 *************/

/* PUBLIC */
Term get_variable_term_if_exists(int var_num)
{
  if (var_num < 0 || var_num >= MAX_VNUM)
    return NULL;
  return Shared_variables[var_num];
}  /* get_variable_term_if_exists */

/*************
 *
 *   get_rigid_term_like()
 *
 *************/

/* DOCUMENTATION
This routine allocates and returns a term node with the same
symbol and arity as the given Term t.
*/

/* PUBLIC */
Term get_rigid_term_like(Term t)
{
  Term t1 = get_term(ARITY(t));
  t1->private_symbol = t->private_symbol;
  return t1;
}  /* get_rigid_term_like */

/*************
 *
 *   get_rigid_term()
 *
 *************/

/* DOCUMENTATION
This routine allocates and returns a term node with the given
symbol and arity.  If you already have a similar term node, say t,
(containing the symbol and arity you need) call get_rigid_term_like(t)
instead.
*/

/* PUBLIC */
Term get_rigid_term(char *sym, int arity)
{
  Term t1;
  int sn;
  if (arity > MAX_ARITY) {
    printf("\nArity %d requested for symbol \"%s\"\n", arity, sym);
    fprintf(stderr, "\nArity %d requested for symbol \"%s\".\n", arity, sym);
    fatal_error("get_rigid_term, arity too big");
  }
  t1 = get_term(arity);
  sn = str_to_sn(sym, arity);
  if (sn >= MAX_SYM)
    fatal_error("get_rigid_term, too many symbols");
  t1->private_symbol = -sn;
  return t1;
}  /* get_rigid_term */

/*************
 *
 *   get_rigid_term_dangerously()
 *
 *************/

/* DOCUMENTATION
This routine can be used to allocate a term node if all you have is
the symbol ID and arity.  <I>If the arity is not correct
for the symbol ID, terrible things will happen!</I> 
<P>
If you have a similar term, use get_rigid_term_like() instead.
If you can afford the time to access the symbol table,
use sn_to_str() and get_rigid_term() instead.
*/

/* PUBLIC */
Term get_rigid_term_dangerously(int symnum, int arity)
{
  Term t1 = get_term(arity);
  t1->private_symbol = -symnum;
  return t1;
}  /* get_rigid_term_dangerously */

/*************
 *
 *    zap_term(term)
 *
 *    Free a term and all of its subterms.
 *
 *************/

/* DOCUMENTATION
This routine frees a term t and all of its subterms.  You should not
refer to t after calling zap_term(t).
*/

/* PUBLIC */
void zap_term(Term t)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    int i;
    for (i = ARITY(s) - 1; i >= 0; i--)
      stack[top++] = ARG(s,i);
    free_term(s);
  }
}  /* zap_term */

/*************
 *
 *    int term_ident(term1, term2) -- Compare two terms.
 *
 *    If identical return 1); else return 0.  The bits
 *    field is not checked.
 *
 *************/

/* DOCUMENTATION
This function checks if two terms are identical.  Only the 
structure and symbols are checked---any extra fields such as
bits or u are NOT checked.
*/

/* PUBLIC */
BOOL term_ident(Term t1, Term t2)
{
  struct { Term a; Term b; } stack[1000];
  int top = 0;
  stack[top].a = t1; stack[top].b = t2; top++;
  while (top > 0) {
    top--;
    Term a = stack[top].a;
    Term b = stack[top].b;
    if (a->private_symbol != b->private_symbol)
      return 0;
    int i;
    for (i = ARITY(a)-1; i >= 0; i--) {
      stack[top].a = ARG(a,i); stack[top].b = ARG(b,i); top++;
    }
  }
  return 1;
}  /* term_ident */

/*************
 *
 *    Term copy_term(term) -- Return a copy of the term.
 *
 *    The bits field is not copied.
 *
 *************/

/* DOCUMENTATION
This routine copies a term.  Only the symbols and structure
are copied---any extra fields such as bits or u are
NOT copied.
*/

/* PUBLIC */
Term copy_term(Term t)
{
  if (t == NULL)
    return NULL;
  if (VARIABLE(t))
    return get_variable_term(VARNUM(t));

  /* Iterative deep copy using explicit stack.
     Each frame: source term, dest term, next child index to process. */
  struct { Term src; Term dst; int child; } stack[1000];
  int top = 0;

  Term root = get_rigid_term_like(t);
  stack[top].src = t; stack[top].dst = root; stack[top].child = 0; top++;

  while (top > 0) {
    int idx = top - 1;
    Term src = stack[idx].src;
    Term dst = stack[idx].dst;
    int c = stack[idx].child;

    if (c >= ARITY(src)) {
      top--;  /* done with this node */
    }
    else {
      stack[idx].child = c + 1;
      Term child_src = ARG(src, c);
      if (VARIABLE(child_src)) {
        ARG(dst, c) = get_variable_term(VARNUM(child_src));
      }
      else {
        Term child_dst = get_rigid_term_like(child_src);
        ARG(dst, c) = child_dst;
        if (ARITY(child_src) > 0) {
          stack[top].src = child_src;
          stack[top].dst = child_dst;
          stack[top].child = 0;
          top++;
        }
      }
    }
  }
  return root;
}  /* copy_term */

/*************
 *
 *    int ground_term(t) -- is a term ground?
 *
 *************/

/* DOCUMENTATION
This function checks if a term is ground, that is, has no variables.
*/

/* PUBLIC */
BOOL ground_term(Term t)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (VARIABLE(s)) return FALSE;
    int i;
    for (i = ARITY(s) - 1; i >= 0; i--)
      stack[top++] = ARG(s,i);
  }
  return TRUE;
}  /* ground_term */

/*************
 *
 *   biggest_variable()
 *
 *************/

/* DOCUMENTATION
This routine returns the greatest variable index of any variable int
the given term t.  If t is ground, -1 is returned.
*/

/* PUBLIC */
int biggest_variable(Term t)
{
  Term stack[1000];
  int top = 0;
  int max = -1;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (VARIABLE(s)) {
      int v = VARNUM(s);
      if (v > max) max = v;
    }
    else {
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return max;
}  /* biggest_variable */

/*************
 *
 *   term_depth()
 *
 *************/

/* DOCUMENTATION
Return the depth of a term.  Variables and constants have depth 0.
*/

/* PUBLIC */
int term_depth(Term t)
{
  /* Iterative depth computation using explicit stack with depth tracking. */
  struct { Term t; int depth; } stack[1000];
  int top = 0;
  int max_depth = 0;
  stack[top].t = t; stack[top].depth = 0; top++;
  while (top > 0) {
    top--;
    Term s = stack[top].t;
    int d = stack[top].depth;
    if (VARIABLE(s) || CONSTANT(s)) {
      if (d > max_depth) max_depth = d;
    }
    else {
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--) {
        stack[top].t = ARG(s,i); stack[top].depth = d+1; top++;
      }
    }
  }
  return max_depth;
}  /* term_depth */

/*************
 *
 *    symbol_count
 *
 *************/

/* DOCUMENTATION
This routine returns the total number of symbols (i.e., the number of
nodes) in the given term t.
*/

/* PUBLIC */
int symbol_count(Term t)
{
  Term stack[1000];
  int top = 0;
  int count = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    count++;
    int i;
    for (i = ARITY(s) - 1; i >= 0; i--)
      stack[top++] = ARG(s,i);
  }
  return count;
}  /* symbol_count  */

/*************
 *
 *     int occurs_in(t1, t2) -- Does t1 occur in t2 (including t1==t2)?
 *
 *     term_ident is used to check identity.
 *
 *************/

/* DOCUMENTATION
This function checks if Term t2 is identical to a subterm of Term t1,
including the case term_ident(t1,t2).  All identity checks are done
with term_ident(), so extra fields such as bits or u are not
checked.
*/

/* PUBLIC */
BOOL occurs_in(Term t1, Term t2)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t2;
  while (top > 0) {
    Term s = stack[--top];
    if (term_ident(t1, s))
      return TRUE;
    int i;
    for (i = ARITY(s) - 1; i >= 0; i--)
      stack[top++] = ARG(s,i);
  }
  return FALSE;
}  /* occurs_in */

/*************
 *
 *  fprint_term(fp, t)
 *
 *************/

/* DOCUMENTATION
This routine prints (to FILE *fp) a term.  A newline is NOT printed.
*/

/* PUBLIC */
void fprint_term(FILE *fp, Term t)
{
  if (t == NULL) {
    fprintf(fp, "fprint_term: NULL term\n");
    return;
  }
  /* Iterative term printing using explicit stack.
     Each frame: term, next child to print, arity. */
  struct { Term t; int child; } stack[1000];
  int top = 0;
  stack[top].t = t; stack[top].child = -1; top++;

  while (top > 0) {
    int idx = top - 1;
    Term s = stack[idx].t;
    int c = stack[idx].child;

    if (c == -1) {
      /* First visit: print symbol and opening paren */
      if (VARIABLE(s)) {
        fprintf(fp, "v%d", VARNUM(s));
        top--;
      }
      else {
        fprint_sym(fp, SYMNUM(s));
        if (COMPLEX(s)) {
          fprintf(fp, "(");
          stack[idx].child = 0;
        }
        else {
          top--;
        }
      }
    }
    else if (c < ARITY(s)) {
      if (c > 0) fprintf(fp, ",");
      stack[idx].child = c + 1;
      /* Push child */
      stack[top].t = ARG(s, c); stack[top].child = -1; top++;
    }
    else {
      /* All children done */
      fprintf(fp, ")");
      top--;
    }
  }
  fflush(fp);
}  /* fprint_term */

/*************
 *
 *  sprint_term(sb, t)
 *
 *************/

/* DOCUMENTATION
This (recursive) routine appends the string representation of a term to
a String_buf.  A newline is not included.
*/

/* PUBLIC */
void sprint_term(String_buf sb, Term t)
{
  if (t == NULL) {
    printf("sprint_term: NULL term\n");
    return;
  }
  struct { Term t; int child; } stack[1000];
  int top = 0;
  stack[top].t = t; stack[top].child = -1; top++;

  while (top > 0) {
    int idx = top - 1;
    Term s = stack[idx].t;
    int c = stack[idx].child;

    if (c == -1) {
      if (VARIABLE(s)) {
        char buf[MAX_NAME];
        sprintf(buf, "v%d", VARNUM(s));
        sb_append(sb, buf);
        top--;
      }
      else {
        sprint_sym(sb, SYMNUM(s));
        if (COMPLEX(s)) {
          sb_append(sb, "(");
          stack[idx].child = 0;
        }
        else {
          top--;
        }
      }
    }
    else if (c < ARITY(s)) {
      if (c > 0) sb_append(sb, ",");
      stack[idx].child = c + 1;
      stack[top].t = ARG(s, c); stack[top].child = -1; top++;
    }
    else {
      sb_append(sb, ")");
      top--;
    }
  }
}  /* sprint_term */

/*************
 *
 *   term_to_string()
 *
 *************/

/* DOCUMENTATION
Convert a term to a string in standard prefix form.
The string is malloced, so call free on it when done with it.
*/

/* PUBLIC */
char *term_to_string(Term t)
{
  char *s;
  String_buf sb = get_string_buf();
  sprint_term(sb, t);
  s = sb_to_malloc_string(sb);
  zap_string_buf(sb);
  return s;
}  /* term_to_string */

/*************
 *
 *  p_term(t)
 *
 *************/

/* DOCUMENTATION
This routine prints a term, followed by '\n' and fflush, to stdout.
If you don't want the newline, use fprint_term() instead.
If you want the term put into a string, use sprint_term() instead.
*/

/* PUBLIC */
void p_term(Term t)
{
  fprint_term(stdout, t);
  printf("\n");
  fflush(stdout);
}  /* p_term */

/*************
 *
 *  all_args_vars(t)
 *
 *************/

/* DOCUMENTATION
This Boolean routine checks if all argumets of Term t are VARIABLEs.
(It is true also if t is a VARIABLE.)
*/

/* PUBLIC */
BOOL all_args_vars(Term t)
{
  if (VARIABLE(t))
    return TRUE;
  else {
    int i;
    for (i = 0; i < ARITY(t); i++)
      if (!VARIABLE(ARG(t,i)))
	return FALSE;
    return TRUE;
  }
}  /* all_args_vars */

/*************
 *
 *    build_binary_term()
 *
 *************/

/* DOCUMENTATION
Build and return a binary term with SYMNUM sn, first term a1, and
second term a2.
<P>
WARNING: if sn is not a binary symbol, bad things will happen!
*/

/* PUBLIC */
Term build_binary_term(int sn, Term a1, Term a2)
{
    Term t = get_rigid_term_dangerously(sn, 2);
    ARG(t,0) = a1;
    ARG(t,1) = a2;
    return(t);
}  /* build_binary_term */

/*************
 *
 *    build_binary_term_safe()
 *
 *************/

/* DOCUMENTATION
Build and return a binary term with root str, first term a1, and
second term a2.
<p>
If you know the symnum, and you're certain it has arity 2, you
can use the faster routine build_binary_term() instead;
*/

/* PUBLIC */
Term build_binary_term_safe(char *str, Term a1, Term a2)
{
  return build_binary_term(str_to_sn(str, 2), a1, a2);
}  /* build_binary_term_safe */

/*************
 *
 *    build_unary_term()
 *
 *************/

/* DOCUMENTATION
Build and return a unary term with SYMNUM sn and argument term a.
<P>
WARNING: if sn is not a unary symbol, bad things will happen!
*/

/* PUBLIC */
Term build_unary_term(int sn, Term a)
{
    Term t = get_rigid_term_dangerously(sn, 1);
    ARG(t,0) = a;
    return(t);
}  /* build_unary_term */

/*************
 *
 *    build_unary_term_safe()
 *
 *************/

/* DOCUMENTATION
Build and return a unary term with root str, argument a.
<p>
If you know the symnum, and you're certain it has arity 1, you
can use the faster routine build_unary_term() instead;
*/

/* PUBLIC */
Term build_unary_term_safe(char *str, Term a)
{
  return build_unary_term(str_to_sn(str, 1), a);
}  /* build_unary_term_safe */

/*************
 *
 *   subst_term()
 *
 *************/

/* DOCUMENTATION
In term t, replace all occurrences of Term target with <I>copies of</I>
Term replacement.  Free all of the replaced terms;
*/

/* PUBLIC */
Term subst_term(Term t, Term target, Term replacement)
{
  /* Iterative in-place substitution using parent stack. */
  struct { Term t; int child; } stack[1000];
  int top = 0;

  /* Check root */
  if (term_ident(t, target)) {
    zap_term(t);
    return copy_term(replacement);
  }
  stack[top].t = t; stack[top].child = 0; top++;
  while (top > 0) {
    int idx = top - 1;
    Term s = stack[idx].t;
    int c = stack[idx].child;
    if (c >= ARITY(s)) {
      top--;
    }
    else {
      stack[idx].child = c + 1;
      if (term_ident(ARG(s,c), target)) {
        zap_term(ARG(s,c));
        ARG(s,c) = copy_term(replacement);
      }
      else if (ARITY(ARG(s,c)) > 0) {
        stack[top].t = ARG(s,c); stack[top].child = 0; top++;
      }
    }
  }
  return t;
}  /* subst_term */

/*************
 *
 *   subst_var_term()
 *
 *************/

/* DOCUMENTATION
In Term t, replace all CONSTANT terms containing SYMNUM symnum
with a variable containing VARNUM varnum.  Free the replaced constants
and return the result.
*/

/* PUBLIC */
Term subst_var_term(Term t, int symnum, int varnum)
{
  if (CONSTANT(t) && SYMNUM(t) == symnum) {
    Term v = get_variable_term(varnum);
    zap_term(t);
    return v;
  }
  /* Iterative: walk and replace matching constants in place. */
  struct { Term t; int child; } stack[1000];
  int top = 0;
  stack[top].t = t; stack[top].child = 0; top++;
  while (top > 0) {
    int idx = top - 1;
    Term s = stack[idx].t;
    int c = stack[idx].child;
    if (c >= ARITY(s)) {
      top--;
    }
    else {
      stack[idx].child = c + 1;
      Term child = ARG(s,c);
      if (CONSTANT(child) && SYMNUM(child) == symnum) {
        ARG(s,c) = get_variable_term(varnum);
        zap_term(child);
      }
      else if (!VARIABLE(child) && ARITY(child) > 0) {
        stack[top].t = child; stack[top].child = 0; top++;
      }
    }
  }
  return t;
}  /* subst_var_term */

/*************
 *
 *   greatest_variable()
 *
 *************/

/* DOCUMENTATION
This routine returns the greatest variable index in a term.
If the term is ground, -1 is returned.
*/

/* PUBLIC */
int greatest_variable(Term t)
{
  Term stack[1000];
  int top = 0;
  int max = -1;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (VARIABLE(s)) {
      int v = VARNUM(s);
      if (v > max) max = v;
    }
    else {
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return max;
}  /* greatest_variable */

/*************
 *
 *   greatest_symnum_in_term()
 *
 *************/

/* DOCUMENTATION
This function returns the greatest SYMNUM (of a CONSTANT or COMPLEX term)
in the given Term t.
If the term is a VARIABLE, return -1.
*/

/* PUBLIC */
int greatest_symnum_in_term(Term t)
{
  Term stack[1000];
  int top = 0;
  int max = -1;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (!VARIABLE(s)) {
      int sn = SYMNUM(s);
      if (sn > max) max = sn;
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return max;
}  /* greatest_symnum_in_term */

/*************
 *
 *   upward_term_links()
 *
 *************/

/* DOCUMENTATION
In the given Term t, make the "container" field of t and each subterm,
except variables, point to (void *) p.
*/

/* PUBLIC */
void upward_term_links(Term t, void *p)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (!VARIABLE(s)) {
      s->container = p;
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
}  /* upward_term_links */

/*************
 *
 *   check_upward_term_links()
 *
 *************/

/* DOCUMENTATION
In the given Term t, check that the "container" field of t and each subterm,
except variables, point to (void *) p.
*/

/* PUBLIC */
BOOL check_upward_term_links(Term t, void *p)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (!VARIABLE(s)) {
      if (s->container != p) return FALSE;
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return TRUE;
}  /* check_upward_term_links */

/*************
 *
 *   occurrences()
 *
 *************/

/* DOCUMENTATION
This function returns the number of occurrences of Term target in Term t.
The checks are made with term_ident().
*/

/* PUBLIC */
int occurrences(Term t, Term target)
{
  Term stack[1000];
  int top = 0;
  int n = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (term_ident(s, target))
      n++;
    else {
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return n;
}  /* occurrences */

/*************
 *
 *   trm_set_vars_recurse()
 *
 *   There might be another (static) copy of this routine in clause.c.
 *
 *************/

static
Term trm_set_vars_recurse(Term t, char **varnames, int max_vars)
{
  /* Handle root being a constant that becomes a variable.
     Skip symbols marked as quoted (from TPTP quoted atoms or
     distinct objects — these are constants regardless of case). */
  if (CONSTANT(t)) {
    char *name = sn_to_str(SYMNUM(t));
    if (variable_name(name) && !is_quoted(SYMNUM(t))) {
      int i = 0;
      while (i < max_vars && varnames[i] != NULL && varnames[i] != name)
	i++;
      if (i == max_vars)
	fatal_error("trm_set_vars_recurse: max_vars");
      if (varnames[i] == NULL)
        varnames[i] = name;
      free_term(t);
      return get_variable_term(i);
    }
    return t;
  }

  /* Iterative traversal for complex terms */
  struct { Term t; int child; } stack[1000];
  int top = 0;
  stack[top].t = t; stack[top].child = 0; top++;
  while (top > 0) {
    int idx = top - 1;
    Term s = stack[idx].t;
    int c = stack[idx].child;
    if (c >= ARITY(s)) {
      top--;
    }
    else {
      stack[idx].child = c + 1;
      Term child = ARG(s,c);
      if (CONSTANT(child)) {
        char *name = sn_to_str(SYMNUM(child));
        if (variable_name(name) && !is_quoted(SYMNUM(child))) {
          int i = 0;
          while (i < max_vars && varnames[i] != NULL && varnames[i] != name)
            i++;
          if (i == max_vars)
            fatal_error("trm_set_vars_recurse: max_vars");
          if (varnames[i] == NULL)
            varnames[i] = name;
          free_term(child);
          ARG(s,c) = get_variable_term(i);
        }
      }
      else if (!VARIABLE(child) && ARITY(child) > 0) {
        stack[top].t = child; stack[top].child = 0; top++;
      }
    }
  }
  return t;
}  /* trm_set_vars_recurse */

/*************
 *
 *   term_set_variables()
 *
 *************/

/* DOCUMENTATION
This routine traverses a term and changes the constants
that should be variables, into variables.  On input, the term
should have no variables.  The new variables are numbered
0, 1, 2 ... according the the first occurrence, reading from the
left.
<P>
A fatal error occurs if there are more than max_vars variables.
<P>
<I>If you are dealing with clauses, use clause_set_variables()
instead.</I>
*/

/* PUBLIC */
void term_set_variables(Term t, int max_vars)
{
  char *a[MAX_VARS], **vmap;
  int i;

  if (max_vars > MAX_VARS)
    vmap = safe_malloc((max_vars * sizeof(char *)));
  else
    vmap = a;

  for (i = 0; i < max_vars; i++)
    vmap[i] = NULL;

  for (i = 0; i < ARITY(t); i++) 
    ARG(t,i) = trm_set_vars_recurse(ARG(t,i), vmap, max_vars);

  if (max_vars > MAX_VARS)
    safe_free(vmap);
}  /* term_set_variables */

/*************
 *
 *   nat_to_term()
 *
 *************/

/* DOCUMENTATION
This routine takes a nonnegative integer and returns
a constant Term with the string representation of the
integer as the constant symbol.
*/

/* PUBLIC */
Term nat_to_term(int n)
{
  char s[25];
  if (n < 0)
    fatal_error("nat_to_term: negative term");
  return get_rigid_term(int_to_str(n, s, 25), 0);
}  /* nat_to_term */

/*************
 *
 *   int_to_term()
 *
 *************/

/* DOCUMENTATION
This routine takes an integer and returns the Term
representation.
*/

/* PUBLIC */
Term int_to_term(int i)
{
  char s[25];
  Term t;
  t = get_rigid_term(int_to_str(abs(i), s, 25), 0);
  if (i < 0)
    t = build_unary_term_safe("-", t);
  return t;
}  /* int_to_term */

/*************
 *
 *   bool_to_term()
 *
 *************/

/* DOCUMENTATION
This routine takes an Bool and returns the Term
representation.
*/

/* PUBLIC */
Term bool_to_term(BOOL val)
{
  return get_rigid_term( val ? true_sym() : false_sym() , 0);
}  /* bool_to_term */

/*************
 *
 *   double_to_term()
 *
 *************/

/* DOCUMENTATION
This routine takes a double and returns
a constant Term with the string representation of the
double as the constant symbol.
*/

/* PUBLIC */
Term double_to_term(double d)
{
  char s[25];
  return get_rigid_term(double_to_str(d, s, 25), 0);
}  /* double_to_term */

/*************
 *
 *   natural_constant_term(t)
 *
 *************/

/* DOCUMENTATION
This routine takes a term, and if the term represents
an nonnegative integer, that integer is returned;
otherwise, -1 is returned.
*/

/* PUBLIC */
int natural_constant_term(Term t)
{
  if (!CONSTANT(t))
    return -1;
  else
    return natural_string(sn_to_str(SYMNUM(t)));
}  /* natural_constant_term */

/*************
 *
 *   arg_position()
 *
 *************/

/* DOCUMENTATION
If the given terms are in a parent-child relatioship,
return the argument position (index) of the child.
Otherwise, return -1.
*/

/* PUBLIC */
int arg_position(Term parent, Term child)
{
  int i;
  for (i = 0; i < ARITY(parent); i++) {
    if (ARG(parent,i) == child)
      return i;
  }
  return -1;
}  /* arg_position */

/*************
 *
 *   is_term()
 *
 *************/

/* DOCUMENTATION
Does term t have the the given symbol and arity?
*/

/* PUBLIC */
BOOL is_term(Term t, char *str, int arity)
{
  return t != NULL && is_symbol(SYMNUM(t), str, arity);
}  /* is_term */

/*************
 *
 *   is_constant()
 *
 *************/

/* DOCUMENTATION
Is term t a specific constant?
*/

/* PUBLIC */
BOOL is_constant(Term t, char *str)
{
  return is_term(t, str, 0);
}  /* is_constant */

/*************
 *
 *   term_symbol()
 *
 *************/

/* DOCUMENTATION
Return the print string associated with the given nonvariable term.
If the term is a variable, return NULL.
*/

/* PUBLIC */
char *term_symbol(Term t)
{
  return VARIABLE(t) ? NULL : sn_to_str(SYMNUM(t));
}  /* term_symbol */

/*************
 *
 *   term_to_int()
 *
 *************/

/* DOCUMENTATION
Given a term, see if it represents an integer.
If so, set *result to the integer and return TRUE.
If not, return FALSE.
<P>
The term representation of a negative integer is
the function symbol "-" applied to a nonnegative integer.
*/

/* PUBLIC */
BOOL term_to_int(Term t, int *result)
{
  if (CONSTANT(t)) {
    return str_to_int(sn_to_str(SYMNUM(t)), result); 
  }
  else if (is_term(t, "-", 1)) {
    if (!CONSTANT(ARG(t,0)))
      return FALSE;
    else {
      if (str_to_int(sn_to_str(SYMNUM(ARG(t,0))), result)) {
	*result = -(*result);
	return TRUE;
      }
      else return FALSE;
    }
  }
  else
    return FALSE;
}  /* term_to_int */

/*************
 *
 *   term_to_double()
 *
 *************/

/* DOCUMENTATION
Given a term, see if it represents a double.
If so, set *result to the double and return TRUE.
If not, return FALSE.
*/

/* PUBLIC */
BOOL term_to_double(Term t, double *result)
{
  if (CONSTANT(t))
    return str_to_double(sn_to_str(SYMNUM(t)), result); 
  else
    return FALSE;
}  /* term_to_double */

/*************
 *
 *   term_to_number()
 *
 *************/

/* DOCUMENTATION
Given a term, see if it represents an integer or a double.
If so, set *result (a double) to the number and return TRUE.
If not, return FALSE.
*/

/* PUBLIC */
BOOL term_to_number(Term t, double *result)
{
  int i;
  if (term_to_int(t, &i)) {
    *result = (double) i;
    return TRUE;
  }
  else if (term_to_double(t, result))
    return TRUE;
  else
    return FALSE;
}  /* term_to_number */

/*************
 *
 *   true_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL true_term(Term t)
{
  return is_term(t, true_sym(), 0);
}  /* true_term */

/*************
 *
 *   false_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL false_term(Term t)
{
  return is_term(t, false_sym(), 0);
}  /* false_term */

/*************
 *
 *   term_to_bool()
 *
 *************/

/* DOCUMENTATION
Given a term, see if it represents an Boolean value.
If so, set *result to the value and return TRUE.
If not, return FALSE.
*/

/* PUBLIC */
BOOL term_to_bool(Term t, BOOL *result)
{
  if (true_term(t)) {
    *result = TRUE;
    return TRUE;
  }
  else if (false_term(t)) {
    *result = FALSE;
    return TRUE;
  }
  else
    return FALSE;
}  /* term_to_bool */

/*************
 *
 *   symbols_in_term()
 *
 *************/

/* DOCUMENTATION
This routine collects the multiset of nonvariable symbols in a term.
An Ilist of symbol IDs (symnums) is returned
*/

/* PUBLIC */
I2list symbols_in_term(Term t, I2list g)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (!VARIABLE(s)) {
      g = multiset_add(g, SYMNUM(s));
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return g;
}  /* symbols_in_term */

/*************
 *
 *   fsym_set_in_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist fsym_set_in_term(Term t)
{
  I2list a = symbols_in_term(t, NULL);
  Ilist b = multiset_to_set(a);
  zap_i2list(a);
  return b;
}  /* fsym_set_in_term */

/*************
 *
 *   renum_vars_recurse()
 *
 *************/

/* DOCUMENTATION
This routine renumbers the variables of a term.  It is assumed
that vmap has been filled with -1 on the initial call and that
the size of vmap is at least max_vars.
<P>
This returns a Term instead of being void, in case the
given term is itself a variable.  (Recall that variables
may be shared, so we can't just change a variable's index.
*/

/* PUBLIC */
Term renum_vars_recurse(Term t, int vmap[], int max_vars)
{
  /* Handle root variable case */
  if (VARIABLE(t)) {
    int i = 0;
    while (i < max_vars && vmap[i] != -1 && vmap[i] != VARNUM(t))
      i++;
    if (i == max_vars)
      fatal_error("renum_vars_recurse: too many variables");
    if (vmap[i] == -1)
      vmap[i] = VARNUM(t);
    free_term(t);
    return get_variable_term(i);
  }

  /* Iterative traversal for non-variable terms */
  struct { Term t; int child; } stack[1000];
  int top = 0;
  stack[top].t = t; stack[top].child = 0; top++;
  while (top > 0) {
    int idx = top - 1;
    Term s = stack[idx].t;
    int c = stack[idx].child;
    if (c >= ARITY(s)) {
      top--;
    }
    else {
      stack[idx].child = c + 1;
      Term child = ARG(s,c);
      if (VARIABLE(child)) {
        int i = 0;
        while (i < max_vars && vmap[i] != -1 && vmap[i] != VARNUM(child))
          i++;
        if (i == max_vars)
          fatal_error("renum_vars_recurse: too many variables");
        if (vmap[i] == -1)
          vmap[i] = VARNUM(child);
        free_term(child);
        ARG(s,c) = get_variable_term(i);
      }
      else if (ARITY(child) > 0) {
        stack[top].t = child; stack[top].child = 0; top++;
      }
    }
  }
  return t;
}  /* renum_vars_recurse */

/*************
 *
 *   set_vars_recurse()
 *
 *************/

/* DOCUMENTATION
This routine sets the variables of a term.  It is assumed
that vnames has been filled with NULL on the initial call and that
the size of vnames is at least max_vars.
<P>
This returns a Term instead of being void, in case the
given term is itself becomes a variable.
*/

/* PUBLIC */
Term set_vars_recurse(Term t, char *vnames[], int max_vars)
{
  /* Handle root constant becoming a variable.
     Skip symbols marked as quoted (TPTP quoted/distinct objects). */
  if (CONSTANT(t)) {
    char *name = sn_to_str(SYMNUM(t));
    if (variable_name(name) && !is_quoted(SYMNUM(t))) {
      int i = 0;
      while (i < max_vars && vnames[i] != NULL && vnames[i] != name)
	i++;
      if (i == max_vars)
	fatal_error("set_vars_recurse: max_vars");
      if (vnames[i] == NULL)
        vnames[i] = name;
      free_term(t);
      return get_variable_term(i);
    }
    return t;
  }

  /* Iterative traversal */
  struct { Term t; int child; } stack[1000];
  int top = 0;
  stack[top].t = t; stack[top].child = 0; top++;
  while (top > 0) {
    int idx = top - 1;
    Term s = stack[idx].t;
    int c = stack[idx].child;
    if (c >= ARITY(s)) {
      top--;
    }
    else {
      stack[idx].child = c + 1;
      Term child = ARG(s,c);
      if (CONSTANT(child)) {
        char *name = sn_to_str(SYMNUM(child));
        if (variable_name(name) && !is_quoted(SYMNUM(child))) {
          int i = 0;
          while (i < max_vars && vnames[i] != NULL && vnames[i] != name)
            i++;
          if (i == max_vars)
            fatal_error("set_vars_recurse: max_vars");
          if (vnames[i] == NULL)
            vnames[i] = name;
          free_term(child);
          ARG(s,c) = get_variable_term(i);
        }
      }
      else if (!VARIABLE(child) && ARITY(child) > 0) {
        stack[top].t = child; stack[top].child = 0; top++;
      }
    }
  }
  return t;
}  /* set_vars_recurse */

/*************
 *
 *   multiset_of_vars()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
I2list multiset_of_vars(Term t, I2list vars)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (VARIABLE(s))
      vars = multiset_add(vars, VARNUM(s));
    else {
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return vars;
}  /* multiset_of_vars */

/*************
 *
 *   multiset_vars()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
I2list multiset_vars(Term t)
{
  return multiset_of_vars(t, NULL);
}  /* multiset_vars */

/*************
 *
 *   set_of_vars()
 *
 *************/

/* DOCUMENTATION
See set_of_variables(t).
*/

/* PUBLIC */
Plist set_of_vars(Term t, Plist vars)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (VARIABLE(s)) {
      if (!plist_member(vars, s))
        vars = plist_prepend(vars, s);
    }
    else {
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return vars;
}  /* set_of_vars */

/*************
 *
 *   set_of_variables()
 *
 *************/

/* DOCUMENTATION
Given a Term, return the set of variables.
*/

/* PUBLIC */
Plist set_of_variables(Term t)
{
  return set_of_vars(t, NULL);
}  /* set_of_variables */

/*************
 *
 *   number_of_vars_in_term()
 *
 *************/

/* DOCUMENTATION
Given a Term, return the set of variables.
*/

/* PUBLIC */
int number_of_vars_in_term(Term t)
{
  Plist p = set_of_vars(t, NULL);
  int n = plist_count(p);
  zap_plist(p);
  return n;
}  /* number_of_vars_in_term */

/*************
 *
 *   set_of_ivars()
 *
 *************/

/* DOCUMENTATION
See set_of_ivariables(t).
*/

/* PUBLIC */
Ilist set_of_ivars(Term t, Ilist ivars)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (VARIABLE(s)) {
      if (!ilist_member(ivars, VARNUM(s)))
        ivars = ilist_prepend(ivars, VARNUM(s));
    }
    else {
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return ivars;
}  /* set_of_ivars */

/*************
 *
 *   set_of_ivariables()
 *
 *************/

/* DOCUMENTATION
Given a Term, return the set of integers corresponding to its variables.
*/

/* PUBLIC */
Ilist set_of_ivariables(Term t)
{
  return set_of_ivars(t, NULL);
}  /* set_of_ivariables */

/*************
 *
 *   variables_subset()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL variables_subset(Term t1, Term t2)
{
  Plist t1_vars = set_of_variables(t1);
  Plist t2_vars = set_of_variables(t2);
  BOOL ok = plist_subset(t1_vars, t2_vars);
  zap_plist(t1_vars);
  zap_plist(t2_vars);
  return ok;
}  /* variables_subset */

/*************
 *
 *   variables_multisubset()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL variables_multisubset(Term a, Term b)
{
#if 1
  I2list a_vars = multiset_vars(a);
  I2list b_vars = multiset_vars(b);
  BOOL ok = i2list_multisubset(a_vars, b_vars);
  zap_i2list(a_vars);
  zap_i2list(b_vars);
  return ok;
#else  /* old version */
  Plist a_vars = set_of_variables(a);
  Plist p;
  BOOL ok = TRUE;

  for (p = a_vars; p && ok; p = p->next)
    ok = occurrences(b, p->v) >= occurrences(a, p->v);

  zap_plist(a_vars);
  return ok;
#endif
}  /* variables_multisubset */

/*************
 *
 *   term_at_pos()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Term term_at_pos(Term t, Ilist pos)
{
  while (pos != NULL) {
    if (pos->i > ARITY(t))
      return NULL;
    t = ARG(t, pos->i - 1);
    pos = pos->next;
  }
  return t;
}  /* term_at_pos */

/*************
 *
 *   pos_of_subterm()
 *
 *************/

static
Ilist pos_of_subterm(Term t, Term subterm)
{
  if (VARIABLE(t))
    return NULL;
  if (t == subterm)
    return ilist_prepend(NULL, INT_MAX);  /* terminator */

  /* Iterative DFS. When found, build position by walking back up the stack.
     At each level j, stack[j].child holds the NEXT child to try, which is
     c+1 after we selected child c. This equals the original code's loop
     variable i after increment, which is the value prepended to the path. */
  struct { Term t; int child; } stack[1000];
  int top = 0;
  stack[top].t = t; stack[top].child = 0; top++;

  while (top > 0) {
    int idx = top - 1;
    Term s = stack[idx].t;
    int c = stack[idx].child;
    if (c >= ARITY(s)) {
      top--;
    }
    else {
      stack[idx].child = c + 1;
      Term child = ARG(s, c);
      if (!VARIABLE(child)) {
        if (child == subterm) {
          /* Build position from bottom of stack to top, then leaf. */
          Ilist p = ilist_prepend(NULL, INT_MAX);  /* terminator */
          p = ilist_prepend(p, c + 1);
          int j;
          for (j = idx - 1; j >= 0; j--)
            p = ilist_prepend(p, stack[j].child);
          return p;
        }
        else if (ARITY(child) > 0) {
          stack[top].t = child; stack[top].child = 0; top++;
        }
      }
    }
  }
  return NULL;
}  /* pos_of_subterm */

/*************
 *
 *   position_of_subterm()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Ilist position_of_subterm(Term t, Term subterm)
{
  Ilist pos = pos_of_subterm(t, subterm);
  if (pos == NULL)
    return NULL;
  else {
    return ilist_remove_last(pos);
  }
}  /* position_of_subterm */

/*************
 *
 *   symbol_occurrences()
 *
 *************/

/* DOCUMENTATION
Return the number of occurrences of a symbol in a term.
*/

/* PUBLIC */
int symbol_occurrences(Term t, int symnum)
{
  Term stack[1000];
  int top = 0;
  int n = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (!VARIABLE(s)) {
      if (SYMNUM(s) == symnum) n++;
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return n;
}  /* symbol_occurrences */

/*************
 *
 *   args_distinct_vars()
 *
 *************/

/* DOCUMENTATION
Is the Term a nonvariable with distinct variables as arguments?
(Constants satisfy this.)
*/

/* PUBLIC */
BOOL args_distinct_vars(Term t)
{
#if 1
  if (VARIABLE(t))
    return FALSE;
  else {
    int i;
    for (i = 0; i < ARITY(t); i++) {
      if (!VARIABLE(ARG(t,i)))
	return FALSE;
      else {
	int j;
	for (j = 0; j < i; j++)
	  if (VARNUM(ARG(t,i)) == VARNUM(ARG(t,j)))
	    return FALSE;
      }
    }
    return TRUE;
  }
#else
  if (VARIABLE(t))
    return FALSE;
  else {
    int *p = safe_calloc(ARITY(t), sizeof(int));
    int i;
    BOOL ok = TRUE;
    for (i = 0; i < ARITY(t) && ok; i++) {
      Term s = ARG(t,i);
      if (!VARIABLE(s))
	ok = FALSE;
      else if (p[VARNUM(s)])
	ok = FALSE;
      else
	p[VARNUM(s)] = TRUE;
    }
    safe_free(p);
    return ok;
  }
#endif
}  /* args_distinct_vars */

/*************
 *
 *   hash_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
unsigned hash_term(Term t)
{
  /* Iterative hash using a stack. We need to process children left-to-right
     and combine with shifts, so we use a post-order approach. */
  struct { Term t; int child; unsigned hash; } stack[1000];
  int top = 0;

  if (VARIABLE(t)) return VARNUM(t);

  stack[top].t = t; stack[top].child = 0; stack[top].hash = SYMNUM(t); top++;

  while (top > 0) {
    int idx = top - 1;
    Term s = stack[idx].t;
    int c = stack[idx].child;
    if (c >= ARITY(s)) {
      unsigned h = stack[idx].hash;
      top--;
      if (top > 0) {
        /* Return hash to parent */
        stack[top-1].hash = (stack[top-1].hash << 3) ^ h;
        stack[top-1].child++;
      }
      else {
        return h;
      }
    }
    else {
      Term child = ARG(s, c);
      if (VARIABLE(child)) {
        stack[idx].hash = (stack[idx].hash << 3) ^ VARNUM(child);
        stack[idx].child = c + 1;
      }
      else {
        /* Push child */
        stack[top].t = child; stack[top].child = 0;
        stack[top].hash = SYMNUM(child); top++;
      }
    }
  }
  return 0;  /* unreachable */
}  /* hash_term */

/*************
 *
 *   skolem_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL skolem_term(Term t)
{
  return is_skolem(SYMNUM(t));
}  /* skolem_term */

/*************
 *
 *   contains_skolem_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL contains_skolem_term(Term t)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (!VARIABLE(s)) {
      if (skolem_term(s)) return TRUE;
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return FALSE;
}  /* contains_skolem_term */

/*************
 *
 *   contains_skolem_function()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL contains_skolem_function(Term t)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (!VARIABLE(s)) {
      if (COMPLEX(s) && skolem_term(s)) return TRUE;
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return FALSE;
}  /* contains_skolem_function */

/*************
 *
 *   term0()
 *
 *************/

/* DOCUMENTATION
Build constant Term.
*/

/* PUBLIC */
Term term0(char *sym)
{
  return get_rigid_term(sym, 0);
}  /* term0 */

/*************
 *
 *   term1()
 *
 *************/

/* DOCUMENTATION
Build a unary term.  The argument Term is not copied.
*/

/* PUBLIC */
Term term1(char *sym, Term arg)
{
  Term t = get_rigid_term(sym, 1);
  ARG(t,0) = arg;
  return t;
}  /* term1 */

/*************
 *
 *   term2()
 *
 *************/

/* DOCUMENTATION
Build a binary term.  The argument Terms are not copied.
*/

/* PUBLIC */
Term term2(char *sym, Term arg1, Term arg2)
{
  Term t = get_rigid_term(sym, 2);
  ARG(t,0) = arg1;
  ARG(t,1) = arg2;
  return t;
}  /* term2 */

/*************
 *
 *   symbol_in_term()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL symbol_in_term(int symnum, Term t)
{
  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (!VARIABLE(s)) {
      if (SYMNUM(s) == symnum) return TRUE;
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return FALSE;
}  /* symbol_in_term */

/*************
 *
 *   same_structure()
 *
 *************/

/* DOCUMENTATION
If variables are ignored, are the terms identical?
*/

/* PUBLIC */
BOOL same_structure(Term a, Term b)
{
  struct { Term a; Term b; } stack[1000];
  int top = 0;
  stack[top].a = a; stack[top].b = b; top++;
  while (top > 0) {
    top--;
    Term sa = stack[top].a;
    Term sb = stack[top].b;
    if (VARIABLE(sa) || VARIABLE(sb)) {
      if (!(VARIABLE(sa) && VARIABLE(sb))) return FALSE;
    }
    else if (SYMNUM(sa) != SYMNUM(sb)) {
      return FALSE;
    }
    else {
      int i;
      for (i = ARITY(sa)-1; i >= 0; i--) {
        stack[top].a = ARG(sa,i); stack[top].b = ARG(sb,i); top++;
      }
    }
  }
  return TRUE;
}  /* same_structure */

/*************
 *
 *   copy_plist_of_terms()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist copy_plist_of_terms(Plist terms)
{
  Plist head = NULL;
  Plist *tail = &head;
  while (terms != NULL) {
    Plist node = get_plist();
    node->v = copy_term(terms->v);
    node->next = NULL;
    *tail = node;
    tail = &node->next;
    terms = terms->next;
  }
  return head;
}  /* copy_plist_of_terms */

/*************
 *
 *   zap_plist_of_terms()
 *
 *************/

/* DOCUMENTATION
Free a Plist of terms.
*/

/* PUBLIC */
void zap_plist_of_terms(Plist lst)
{
  Plist p = lst;
  while (p != NULL) {
    Plist p2 = p;
    p = p->next;
    zap_term(p2->v);
    free_plist(p2);
  }
}  /* zap_plist_of_terms */

/*************
 *
 *   eq_term()
 *
 *************/

/* DOCUMENTATION
This function checks if an atom is an equality atom (positive or negative)
for the purposes of paramodulation and demodulation.
*/

/* PUBLIC */
BOOL eq_term(Term a)
{
  return is_eq_symbol(SYMNUM(a));
}  /* eq_term */

/*************
 *
 *   plist_of_subterms()  -- shallow
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist plist_of_subterms(Term t)
{
  Plist subterms = NULL;
  int i;
  for (i = 0; i < ARITY(t); i++)
    subterms = plist_append(subterms, ARG(t,i));
  return subterms;
}  /* plist_of_subterms */

/*************
 *
 *   tlist_member()
 *
 *************/

/* DOCUMENTATION
This function checks if a term is a member of a Plist.
The function term_ident(t1,t2) is used.
*/

/* PUBLIC */
BOOL tlist_member(Term t, Plist lst)
{
  while (lst) {
    if (term_ident(lst->v, t)) return TRUE;
    lst = lst->next;
  }
  return FALSE;
}  /* tlist_member */

/*************
 *
 *   position_of_term_in_tlist()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int position_of_term_in_tlist(Term t, Plist lst)
{
  Plist p;
  int i;
  for (p = lst, i = 1; p; p = p->next, i++)
    if (term_ident(p->v, t))
      return i;
  return -1;
}  /* position_of_term_in_tlist */

/*************
 *
 *   tlist_subset()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL tlist_subset(Plist a, Plist b)
{
  while (a != NULL) {
    if (!tlist_member(a->v, b))
      return FALSE;
    a = a->next;
  }
  return TRUE;
}  /* tlist_subset */

/*************
 *
 *   tlist_set()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL tlist_set(Plist a)
{
  while (a != NULL) {
    if (tlist_member(a->v, a->next))
      return FALSE;
    a = a->next;
  }
  return TRUE;
}  /* tlist_set */

/*************
 *
 *   free_vars_term()
 *
 *************/

/* DOCUMENTATION
Return the set of constants that look like variables.
The terms are newly constructed; if they are not used,
the list should be deallocated with zap_tlist().
*/

/* PUBLIC */
Plist free_vars_term(Term t, Plist vars)
{
  if (VARIABLE(t))
    fatal_error("free_vars_term, VARIABLE term");

  Term stack[1000];
  int top = 0;
  stack[top++] = t;
  while (top > 0) {
    Term s = stack[--top];
    if (VARIABLE(s))
      fatal_error("free_vars_term, VARIABLE term");
    if (ARITY(s) == 0) {
      if (variable_name(sn_to_str(SYMNUM(s))) && !tlist_member(s, vars))
        vars = plist_append(vars, copy_term(s));
    }
    else {
      int i;
      for (i = ARITY(s) - 1; i >= 0; i--)
        stack[top++] = ARG(s,i);
    }
  }
  return vars;
}  /* free_vars_term */

/*************
 *
 *   init_any_consts()
 *
 *************/

static void init_any_consts(void)
{
  int i;
  char str[64];
  AnyConsts[0] = str_to_sn(ANYCONST, 0);
  for (i = 1; i < MAX_ANYCONSTS; i++) {
    snprintf(str, 64, "%s_%d", ANYCONST, i);
    AnyConsts[i] = str_to_sn(str, 0);
  }
  AnyConstsInited = TRUE;
}  /* init_any_consts */

/*************
 *
 *   any_const()
 *
 *************/

/* DOCUMENTATION
Return the _AnyConst index (0 for _AnyConst, 1-9 for _AnyConst_1 .. _9)
if sn is an _AnyConst symbol; otherwise return -1.
*/

/* PUBLIC */
int any_const(int sn)
{
  int i;
  if (!AnyConstsInited)
    init_any_consts();
  for (i = 0; i < MAX_ANYCONSTS; i++) {
    if (AnyConsts[i] == sn)
      return i;
  }
  return -1;
}  /* any_const */

/*************
 *
 *   any_const_sn()
 *
 *************/

/* DOCUMENTATION
Return the symbol number for _AnyConst (n==0) or _AnyConst_n (n==1..9).
*/

/* PUBLIC */
int any_const_sn(int n)
{
  if (!AnyConstsInited)
    init_any_consts();
  return AnyConsts[n];
}  /* any_const_sn */

