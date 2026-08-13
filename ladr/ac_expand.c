/*  Copyright (C) 2026 Jeffrey P. Machado, Larry Lesyna.

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

#include "ac_expand.h"
#include "accanon.h"
#include "paramod.h"
#include "resolve.h"

/*************
 *
 *   ac_extension_of()
 *
 *   Promoted from provers.src/search.c's make_ac_extension() (which was
 *   `static`, so xproofs.c -- in ladr/, a layer search.c depends on, not
 *   the reverse -- could not call it to replay AC_EXT_JUST steps).
 *
 *   For a positive unit equation s = t where s (or t) has an AC top
 *   symbol f, build the Peterson-Stickel extension  f(s,X) = f(t,X)
 *   (X fresh).  Returns NULL if the clause does not qualify.
 *
 *************/

/* PUBLIC */
Topform ac_extension_of(Topform c)
{
  Term atom, alpha, beta, lhs, rhs, var, new_atom;
  Topform ext;
  int f, vnum;

  if (c->ac_extension || c->is_formula || c->literals == NULL ||
      c->literals->next != NULL || !c->literals->sign ||
      !eq_term(c->literals->atom))
    return NULL;
  atom = c->literals->atom;
  alpha = ARG(atom, 0);
  beta = ARG(atom, 1);
  if (!VARIABLE(alpha) && is_assoc_comm(SYMNUM(alpha)))
    f = SYMNUM(alpha);
  else if (!VARIABLE(beta) && is_assoc_comm(SYMNUM(beta)))
    f = SYMNUM(beta);
  else
    return NULL;

  vnum = greatest_variable_in_clause(c->literals) + 1;
  if (vnum >= MAX_VARS)
    return NULL;
  var = get_variable_term(vnum);

  lhs = get_rigid_term(sn_to_str(f), 2);
  ARG(lhs, 0) = copy_term(alpha);
  ARG(lhs, 1) = var;
  rhs = get_rigid_term(sn_to_str(f), 2);
  ARG(rhs, 0) = copy_term(beta);
  ARG(rhs, 1) = copy_term(var);
  new_atom = build_binary_term(str_to_sn(eq_sym(), 2), lhs, rhs);

  ext = get_topform();
  ext->literals = new_literal(TRUE, new_atom);
  upward_clause_links(ext);
  ext->justification = ac_ext_just(c);
  ext->ac_extension = 1;
  return ext;
}  /* ac_extension_of */

/*************
 *
 *   Phantom axiom set: build_ac_axiom_set() and friends.
 *
 *   Comm/assoc "phantom" axioms are SYNTHESIZED here, one pair per
 *   AC-declared symbol -- see build_ac_axiom_set()'s own comment for why
 *   that's correct (not forgery): assoc_comm(f) already semantically
 *   entails them, and a verifier checks citations against ITS OWN
 *   problem file, which for a faithful TPTP rendering of an AC theory
 *   already states them explicitly, regardless of whether Prover9's own
 *   search process ever touched them as literal clauses.
 *
 *************/

struct ac_axiom_entry {
  int symbol_num;
  BOOL usable;
  Topform comm;          /* synthesized axiom: f(x,y)=f(y,x) */
  Topform assoc;         /* synthesized axiom: f(f(x,y),z)=f(x,f(y,z)) */
  int assoc_l2r_dir;     /* direction to rewrite f(x,f(y,z)) -> f(f(x,y),z) via `assoc` */
  int assoc_r2l_dir;     /* direction to rewrite f(f(x,y),z) -> f(x,f(y,z)) via `assoc` */
};

#define MAX_AC_AXIOM_ENTRIES 32

/* Bound on a single demodulator's own pattern-variable count (i.e. the
   number of groups a match partitions a subject into: one per pattern
   variable, plus one more for a partial-match leftover).  This is NOT
   the same scale as MAX_ACM_ARGS (a group's own CONTENT can be up to
   MAX_ACM_ARGS elements) -- real demodulators have a handful of
   variables at most; this just needs to be a safe, small upper bound to
   avoid an MAX_ACM_ARGS x MAX_ACM_ARGS stack array. */
#define MAX_AC_GROUPS 32

struct ac_axiom_set {
  int n;
  struct ac_axiom_entry entries[MAX_AC_AXIOM_ENTRIES];
};

static
void collect_ac_symbols(Term t, int *syms, int *n)
{
  int i;
  if (VARIABLE(t))
    return;
  if (is_assoc_comm(SYMNUM(t))) {
    int sn = SYMNUM(t);
    BOOL found = FALSE;
    for (i = 0; i < *n; i++)
      if (syms[i] == sn) { found = TRUE; break; }
    if (!found && *n < MAX_AC_AXIOM_ENTRIES)
      syms[(*n)++] = sn;
  }
  for (i = 0; i < ARITY(t); i++)
    collect_ac_symbols(ARG(t,i), syms, n);
}  /* collect_ac_symbols */

/* Build the genuine (INPUT_JUST) clause f(x0,x1) = f(x1,x0) or
   f(f(x0,x1),x2) = f(x0,f(x1,x2)) for symbol f.  assoc_shape selects
   which; direction 1 always means "use as written" (matching
   demod_at_position's convention). */
static
Topform synth_ac_axiom(int f, BOOL assoc_shape)
{
  Term x0 = get_variable_term(0), x1 = get_variable_term(1);
  Term lhs, rhs, atom;
  Topform c;

  if (!assoc_shape) {
    lhs = build_binary_term(f, x0, x1);
    x0 = get_variable_term(0); x1 = get_variable_term(1);
    rhs = build_binary_term(f, x1, x0);
  }
  else {
    Term x2 = get_variable_term(2);
    lhs = build_binary_term(f, build_binary_term(f, x0, x1), x2);
    x0 = get_variable_term(0); x1 = get_variable_term(1); x2 = get_variable_term(2);
    rhs = build_binary_term(f, x0, build_binary_term(f, x1, x2));
  }
  atom = build_binary_term(str_to_sn(eq_sym(), 2), lhs, rhs);

  c = get_topform();
  c->literals = new_literal(TRUE, atom);
  upward_clause_links(c);
  c->justification = input_just();
  return c;
}  /* synth_ac_axiom */

/* PUBLIC
   Phantom comm/assoc axioms, one pair per AC-declared symbol found in
   `proof`.  These are SYNTHESIZED, not sourced from the search's own
   clause pool -- see the note at the top of this file for why that's
   the right call: assoc_comm(f) already semantically entails them (they
   are not extraneous facts, just its explicit unfolding), citing them
   in the search itself is pure combinatorial overhead (their maximally
   general shape makes every use a genuine, expensive AC-unification
   problem, for zero deductive gain over the built-in mechanism), and a
   verifier checks the printed proof's citations against ITS OWN problem
   file (which, for any faithful TPTP rendering of an AC theory, already
   states comm/assoc explicitly -- TPTP has no assoc_comm(...) syntax) --
   not against whatever Prover9's search happened to touch internally.
   Each synthesized clause is assigned an id from *next_id (so it doesn't
   collide with proof step ids); see ac_axiom_set_clauses() for getting
   them into the printed output. */
Ac_axiom_set build_ac_axiom_set(Plist proof, int *next_id)
{
  int syms[MAX_AC_AXIOM_ENTRIES];
  int nsyms = 0;
  Plist p;
  Ac_axiom_set set;
  int i;

  for (p = proof; p; p = p->next) {
    Topform c = p->v;
    Literals lit;
    for (lit = c->literals; lit; lit = lit->next)
      collect_ac_symbols(lit->atom, syms, &nsyms);
  }

  set = safe_malloc(sizeof(struct ac_axiom_set));
  set->n = nsyms;

  for (i = 0; i < nsyms; i++) {
    int f = syms[i];
    set->entries[i].symbol_num = f;

    set->entries[i].comm = synth_ac_axiom(f, FALSE);
    set->entries[i].comm->id = (*next_id)++;

    set->entries[i].assoc = synth_ac_axiom(f, TRUE);
    set->entries[i].assoc->id = (*next_id)++;
    /* synth_ac_axiom(f,TRUE) always builds f(f(x,y),z)=f(x,f(y,z)): */
    set->entries[i].assoc_r2l_dir = 1;
    set->entries[i].assoc_l2r_dir = -1;

    set->entries[i].usable = TRUE;
  }
  return set;
}  /* build_ac_axiom_set */

/* PUBLIC */
void zap_ac_axiom_set(Ac_axiom_set set)
{
  if (set != NULL)
    safe_free(set);
}  /* zap_ac_axiom_set */

/* PUBLIC */
Plist ac_axiom_set_clauses(Ac_axiom_set set)
{
  Plist clauses = NULL;
  int i;
  if (set == NULL)
    return NULL;
  for (i = 0; i < set->n; i++) {
    clauses = plist_prepend(clauses, set->entries[i].comm);
    clauses = plist_prepend(clauses, set->entries[i].assoc);
  }
  return clauses;
}  /* ac_axiom_set_clauses */

/* PUBLIC */
BOOL ac_axiom_set_has(Ac_axiom_set set, int symbol_num)
{
  int i;
  if (set == NULL)
    return FALSE;
  for (i = 0; i < set->n; i++)
    if (set->entries[i].symbol_num == symbol_num)
      return set->entries[i].usable;
  return FALSE;
}  /* ac_axiom_set_has */

static
struct ac_axiom_entry *find_entry(Ac_axiom_set set, int symbol_num)
{
  int i;
  for (i = 0; i < set->n; i++)
    if (set->entries[i].symbol_num == symbol_num)
      return &set->entries[i];
  return NULL;
}  /* find_entry */

/*************
 *
 *   Deep-shape utilities.
 *
 *************/

/* AC-equality: equal after AC-canonicalization -- the comparison for
   pairing subject elements with sigma-reconstructed pattern elements,
   whose INTERIORS can be bracketed differently (apply() rebuilds a
   match_ac binding in its own shape) even though the terms are the same
   modulo AC.  Works on copies; ac_canonical() mutates in place. */
static
BOOL ac_equal_term(Term a, Term b)
{
  Term ca = copy_term(a);
  Term cb = copy_term(b);
  BOOL eq;
  ac_canonical(ca, -1);
  ac_canonical(cb, -1);
  eq = term_ident(ca, cb);
  zap_term(ca);
  zap_term(cb);
  return eq;
}  /* ac_equal_term */

/* Does t contain an AC-declared symbol anywhere?  (Dispatch test for
   the deep-bridging fallback: a pattern with no AC symbol at all cannot
   benefit from an AC-aware retry of a failed plain replay.)  PUBLIC so
   expand_proof() can ask the same question when deciding whether a
   failed PLAIN para replay is worth promoting to the AC path. */
/* PUBLIC */
BOOL term_contains_ac(Term t)
{
  int i;
  if (VARIABLE(t))
    return FALSE;
  if (is_assoc_comm(SYMNUM(t)))
    return TRUE;
  for (i = 0; i < ARITY(t); i++)
    if (term_contains_ac(ARG(t,i)))
      return TRUE;
  return FALSE;
}  /* term_contains_ac */

/* Does subst bind any variable that occurs in c?  (Deep-para mode has
   no groups_found_in_node() check to trigger the into-side
   instantiation, so it asks the substitution directly.) */
static
BOOL context_binds_any(Context subst, Topform c)
{
  Ilist vnums = varnums_in_clause(c->literals);
  Ilist p;
  BOOL any = FALSE;
  for (p = vnums; p != NULL && !any; p = p->next)
    if (subst->terms[p->i] != NULL)
      any = TRUE;
  zap_ilist(vnums);
  return any;
}  /* context_binds_any */

/*************
 *
 *   AC-aware rediscovery: find_ac_demod_candidate().
 *
 *   The recorded DEMOD_JUST triple's position/sequence number is
 *   documented as advisory under AC canonicalization (demod.c's
 *   demod_bt: "the term is reshaped between steps, so exact replay is
 *   not possible") -- only the demodulator ID is trustworthy.  This
 *   walks `work`'s literals looking for AC-match candidates (via
 *   btm.c's match_bt_first/next), enumerating them with a single flat
 *   alt_index so a caller can retry on overall failure.
 *
 *************/

struct ac_find_ctx {
  Term lhs;
  int target_sn;
  int alt_index;
  int count;
  BOOL done;
  Context found_subst;
  Term found_node;
  Btm_state found_bt;
};

static
void try_node(Term node, struct ac_find_ctx *ctx)
{
  if (ctx->done)
    return;
  if (COMPLEX(node) && SYMNUM(node) == ctx->target_sn) {
    Context c = get_context();
    /* match_bt requires its SUBJECT to be ac_canonical (sorted +
       right-associated) -- see match_bt_first()'s own doc.  The live
       search keeps all terms canonical, but our reshaped/instantiated
       replay clauses are NOT sorted, so matching a collapsing or
       duplicating pattern (e.g. +(A,A)=A) against a chain whose equal
       elements aren't adjacent would silently fail.  Match against a
       canonical COPY to discover the binding, but keep found_node = the
       REAL node so the caller's
       position is into the real clause; deep_bridge() reshapes the
       real (unsorted) subject via do_reorder()'s from-any-order bubble
       + ac_equal pairing, so it doesn't need the real node sorted.  The
       copy is intentionally leaked: the returned subst binds into it,
       and the caller reads those bindings after this returns. */
    Term cnode = copy_term(node);
    Btm_state bt;
    ac_canonical(cnode, -1);
    bt = match_bt_first(ctx->lhs, c, cnode, TRUE);
    while (bt != NULL && !ctx->done) {
      if (ctx->count == ctx->alt_index) {
        ctx->found_subst = c;
        ctx->found_node = node;
        ctx->found_bt = bt;
        ctx->done = TRUE;
        /* bindings stay live in c for the caller -- do not cancel here.
           The caller owns `bt` now and MUST call match_bt_cancel(bt)
           before free_context(c): match_bt_first/next bind straight into
           c via their own internal trail, which free_context() does NOT
           unwind (unlike ordinary unify()/match() trails, it never runs
           through undo_subst()).  Skipping match_bt_cancel() returns a
           dirty Context (stale non-NULL terms[]/contexts[] slots) to the
           global freelist, silently corrupting whatever unrelated
           get_context() call recycles it next -- this is exactly the
           mechanism behind the para_pos()/unify() NULL-write crash this
           comment was added to fix. */
      }
      else {
        ctx->count++;
        bt = match_bt_next(bt);
      }
    }
    if (!ctx->done)
      free_context(c);
  }
}  /* try_node */

static
void walk_term(Term t, struct ac_find_ctx *ctx)
{
  int i;
  if (ctx->done || VARIABLE(t))
    return;
  try_node(t, ctx);
  if (ctx->done)
    return;
  for (i = 0; i < ARITY(t) && !ctx->done; i++)
    walk_term(ARG(t,i), ctx);
}  /* walk_term */

/* PUBLIC */
BOOL find_ac_demod_candidate(Topform work, Topform demod, int direction,
			    int alt_index,
			    Ilist *out_tree_pos, Context *out_subst,
			    Term *out_matched_node, Btm_state *out_bt)
{
  struct ac_find_ctx ctx;
  /* AC-headed demodulators are ORIENTED only (direction 1), but the
     deep-bridging fallback replays PLAIN demod citations too, and those
     can rewrite right-to-left -- honor the recorded direction. */
  Term lhs = ARG(demod->literals->atom, direction == 1 ? 0 : 1);
  Literals lit;
  int litnum = 0;

  /* match_bt needs its PATTERN ac_canonical too (its own doc); the
     demodulators come from proof clauses the search kept canonical, but
     canonicalize a copy defensively -- cheap, done once for the whole
     walk.  (Intentionally leaked, like the per-node subject copies.) */
  {
    Term clhs = copy_term(lhs);
    ac_canonical(clhs, -1);
    ctx.lhs = clhs;
  }
  ctx.target_sn = SYMNUM(lhs);
  ctx.alt_index = alt_index;
  ctx.count = 0;
  ctx.done = FALSE;
  ctx.found_subst = NULL;
  ctx.found_node = NULL;
  ctx.found_bt = NULL;

  for (lit = work->literals; lit && !ctx.done; lit = lit->next) {
    litnum++;
    walk_term(lit->atom, &ctx);
    if (ctx.done) {
      Ilist rel_pos = position_of_subterm(lit->atom, ctx.found_node);
      *out_tree_pos = ilist_prepend(rel_pos, litnum);
      *out_subst = ctx.found_subst;
      *out_matched_node = ctx.found_node;
      *out_bt = ctx.found_bt;
      return TRUE;
    }
  }
  return FALSE;
}  /* find_ac_demod_candidate */

/*************
 *
 *   Positional ordinary rewrite: descend_to_parent(), demod_at_position().
 *
 *   Applies one ordinary (non-AC) demodulator step at a KNOWN position
 *   (rather than particular_demod()'s "guess the Nth matchable node"
 *   scheme, which fatal_error()s on a mismatch -- since the bridging
 *   synthesizer and find_ac_demod_candidate() already know the exact
 *   node, there is nothing to guess).  Produces a genuine PARA_JUST
 *   citing `demodulator`, exactly like any ordinary DEMOD_JUST substep.
 *
 *************/

static
Term descend_to_parent(Term t, Ilist pos, Term *parent_out, int *child_index_out)
{
  Term parent = NULL;
  int last_i = 0;
  while (pos != NULL) {
    parent = t;
    last_i = pos->i;
    t = ARG(t, pos->i - 1);
    pos = pos->next;
  }
  *parent_out = parent;
  *child_index_out = last_i;
  return t;
}  /* descend_to_parent */

/* Rewrite the subterm at `litnum`/`rel_pos` within `c` (mutated in
   place -- caller must have already copy_clause()'d a fresh working
   clause) by applying `demodulator` (direction `dir`).  On success,
   fills out_from_pos and out_into_pos (matching particular_demod()'s own
   convention) and returns TRUE.  Returns FALSE only if `demodulator`
   genuinely doesn't match at that exact position -- a synthesizer bug,
   should not happen; callers treat FALSE as "give up on this candidate". */
static
BOOL demod_at_position(Topform c, Topform demodulator, int dir,
		       int litnum, Ilist rel_pos,
		       Ilist *out_from_pos, Ilist *out_into_pos)
{
  Literals lit = ith_literal(c->literals, litnum);
  Term parent = NULL;
  int child_index = 0;
  Term site = descend_to_parent(lit->atom, rel_pos, &parent, &child_index);
  Term alpha, beta, result;
  Context subst = get_context();
  Trail tr = NULL;

  if (dir == 1) {
    alpha = ARG(demodulator->literals->atom, 0);
    beta  = ARG(demodulator->literals->atom, 1);
  }
  else {
    alpha = ARG(demodulator->literals->atom, 1);
    beta  = ARG(demodulator->literals->atom, 0);
  }

  if (!match(alpha, subst, site, &tr)) {
    free_context(subst);
    return FALSE;
  }
  result = apply(beta, subst);
  undo_subst(tr);
  free_context(subst);

  if (parent == NULL)
    lit->atom = result;
  else
    ARG(parent, child_index - 1) = result;

  /* `result`'s own subterms don't yet have their "container" backlink
     set to `c` (apply() has no notion of the enclosing Topform) --
     mirrors particular_demod()'s identical fixup after its own in-place
     rewrite (demod.c).  Without this, check_upward_clause_links() (run
     by expand_proof's final check_parents_and_uplinks_in_proof) fails
     with "bad uplinks" on every AC-bridged step. */
  upward_clause_links(c);

  *out_from_pos = ilist_prepend(ilist_prepend(NULL, dir), 1);
  *out_into_pos = ilist_prepend(copy_ilist(rel_pos), litnum);
  return TRUE;
}  /* demod_at_position */

/*************
 *
 *   Bridging driver: reshape the subtree at a known (litnum, base_pos)
 *   into the exact grouped shape a real AC match needs, one ordinary
 *   phantom-axiom step at a time.  Validated design (flat permutation +
 *   grouping) against real match()/apply() in a standalone prototype
 *   before being wired in here.
 *
 *************/

struct bridge_ctx {
  Topform current;       /* clause as of the most recent step */
  int litnum;
  Ilist base_pos;         /* path from the literal atom to the found node's TOP; fixed for the whole bridge */
  int f;                  /* the AC symbol OF THE NODE CURRENTLY BEING
			     BRIDGED -- deep recursion (deep_bridge/
			     bridge_to_exact_term) saves/restores this
			     and `ax` around each AC node it descends
			     into, since different nodes can be headed
			     by different AC symbols */
  struct ac_axiom_entry *ax;
  Ac_axiom_set axioms;    /* full set, for per-symbol lookup in deep recursion */
  int *next_id;
  I3list *map;
  int old_id;
  int *old_id_n;
  Plist *new_proof;
  BOOL failed;
};

/* Generalized micro-step: copy bctx->current, rewrite it at
   base_pos ++ rel via (demod=ax_clause, dir), record justification,
   splice into new_proof, update bctx->current.  rel is an arbitrary
   relative path below the found node's top (1 = left child, 2 = right
   child) -- needed by the exact-shape re-bracketing pass, which must
   operate inside LEFT children, unreachable via do_step()'s right-spine
   depth convention.  rel is copied; the caller keeps ownership. */
static
void do_step_at(struct bridge_ctx *bctx, Topform ax_clause, int dir,
		Ilist rel)
{
  Topform work;
  Ilist rel_pos;
  Ilist from_pos, into_pos;

  if (bctx->failed)
    return;

  rel_pos = ilist_cat(copy_ilist(bctx->base_pos), copy_ilist(rel));

  work = copy_clause(bctx->current);
  *bctx->map = alist2_insert(*bctx->map, *bctx->next_id, bctx->old_id,
			     (*bctx->old_id_n)++);
  work->id = (*bctx->next_id)++;

  if (!demod_at_position(work, ax_clause, dir, bctx->litnum, rel_pos,
			 &from_pos, &into_pos)) {
    bctx->failed = TRUE;
    return;
  }
  work->justification = para_just(PARA_JUST, ax_clause, from_pos,
				  bctx->current, into_pos);
  bctx->current = work;
  *bctx->new_proof = plist_prepend(*bctx->new_proof, work);
}  /* do_step_at */

/* Append one more step at right-spine nesting depth `depth` within the
   found node's own subtree (a path of `depth` second-argument descents)
   -- the interface the flat-permutation machinery (do_swap_at_depth /
   do_reorder / do_close_group) uses; body shared with do_step_at(). */
static
void do_step(struct bridge_ctx *bctx, Topform ax_clause, int dir, int depth)
{
  Ilist rel = NULL;
  int i;
  for (i = 0; i < depth; i++)
    rel = ilist_prepend(rel, 2);
  do_step_at(bctx, ax_clause, dir, rel);
  zap_ilist(rel);
}  /* do_step */

/* Build rel ++ [2]*d (a fresh list; caller zaps). */
static
Ilist rel_plus_depth(Ilist rel, int d)
{
  Ilist r = copy_ilist(rel);
  int i;
  for (i = 0; i < d; i++)
    r = ilist_append(r, 2);
  return r;
}  /* rel_plus_depth */

/* One elementary swap of the first two elements at nesting depth `d`
   within the chain at base_pos ++ rel (0 = swap the top two).  Mirrors
   the validated prototype's swap_at_depth() exactly, but each
   micro-step goes through do_step_at() so it becomes a real, justified
   proof step. */
static
void do_swap_at(struct bridge_ctx *bctx, Ilist rel, int d)
{
  Ilist full_pos, rel_d;
  Term node, second;

  if (bctx->failed)
    return;

  rel_d = rel_plus_depth(rel, d);
  full_pos = ilist_cat(copy_ilist(bctx->base_pos), copy_ilist(rel_d));
  node = term_at_pos(ith_literal(bctx->current->literals, bctx->litnum)->atom,
		     full_pos);
  zap_ilist(full_pos);
  if (node == NULL || !COMPLEX(node) || ARITY(node) != 2) {
    bctx->failed = TRUE;   /* navigation fell off the chain -- decline */
    zap_ilist(rel_d);
    return;
  }

  second = ARG(node, 1);
  if (COMPLEX(second) && SYMNUM(second) == bctx->f && ARITY(second) == 2) {
    /* f(x,f(y,z)) -> f(f(x,y),z) -> f(f(y,x),z) -> f(y,f(x,z)).
       The middle comm step operates on the CLOSED PAIR f(x,y) -- i.e.
       one level DOWN-LEFT of this node (rel_d ++ [1]), NOT on the node
       itself: comm at the node would swap its two whole arguments,
       giving f(z, f(x,y)) -- and when z is itself f-headed, the
       follow-up assoc_r2l still matches, silently garbling the chain
       out of right-associated form so later depth navigation walks off
       it.  The old right-spine-only do_step() convention could not even
       EXPRESS a [1] descent. */
    do_step_at(bctx, bctx->ax->assoc, bctx->ax->assoc_l2r_dir, rel_d);
    {
      Ilist rel_dl = ilist_append(copy_ilist(rel_d), 1);
      do_step_at(bctx, bctx->ax->comm, 1, rel_dl);
      zap_ilist(rel_dl);
    }
    do_step_at(bctx, bctx->ax->assoc, bctx->ax->assoc_r2l_dir, rel_d);
  }
  else {
    /* last two elements of the chain: no 'z' remainder, plain comm. */
    do_step_at(bctx, bctx->ax->comm, 1, rel_d);
  }
  zap_ilist(rel_d);
}  /* do_swap_at */

/* term_ident pairing for the shallow (validated Phase 1/2) paths;
   ac_equal_term pairing for the deep path, where a subject element can
   be the same term modulo AC with a differently-bracketed interior
   (apply() rebuilds match_ac bindings in its own shape) -- the interior
   gets aligned by deep recursion after pairing. */
static
int find_index(Term *flat, int n, Term target, BOOL deep)
{
  int i;
  for (i = 0; i < n; i++)
    if (deep ? ac_equal_term(flat[i], target) : term_ident(flat[i], target))
      return i;
  return -1;
}  /* find_index */

/* Reorder the chain at base_pos ++ rel to the flat order tgt[0..n-1]
   (same multiset -- modulo AC when deep -- target order), one bubble at
   a time.  Defensive: a subject chain SHORTER than n (a candidate whose
   multiset doesn't actually cover the target -- callers should have
   pre-checked, but an interior partial match_ac can slip a smaller
   subtree through) fails the candidate cleanly instead of walking
   ARG(leaf,1) off the end of the chain. */
static
void do_reorder_at(struct bridge_ctx *bctx, Ilist rel, Term *tgt, int n,
		   BOOL deep)
{
  int i;
  for (i = 0; i < n - 1 && !bctx->failed; i++) {
    Term node, flat[MAX_ACM_ARGS];
    int nflat, k;
    Ilist full_pos = ilist_cat(copy_ilist(bctx->base_pos), copy_ilist(rel));
    node = term_at_pos(ith_literal(bctx->current->literals, bctx->litnum)->atom,
		       full_pos);
    zap_ilist(full_pos);
    if (node == NULL) {
      bctx->failed = TRUE;
      return;
    }
    /* skip the first i already-placed elements */
    {
      int skip;
      for (skip = 0; skip < i; skip++) {
	if (!(COMPLEX(node) && SYMNUM(node) == bctx->f && ARITY(node) == 2)) {
	  bctx->failed = TRUE;  /* chain shorter than the target list */
	  return;
	}
	node = ARG(node, 1);
      }
    }
    nflat = 0;
    flatten(node, flat, &nflat);
    k = find_index(flat, nflat, tgt[i], deep);
    if (k < 0) {
      bctx->failed = TRUE;
      return;
    }
    if (k > 0) {
      /* bubble_to_front operates relative to the CURRENT suffix, i.e. at
	 depth `i` within this chain. */
      int d;
      for (d = k - 1; d >= 0 && !bctx->failed; d--)
	do_swap_at(bctx, rel, i + d);
    }
  }
}  /* do_reorder_at */

/* The original fixed-position interfaces, kept so the validated
   Phase 1/2 call sites are textually untouched. */
static
void do_reorder(struct bridge_ctx *bctx, Term *tgt, int n)
{
  do_reorder_at(bctx, NULL, tgt, n, FALSE);
}  /* do_reorder */

/* Close off the first `m` elements (of the chain remaining after `i`
   already-placed groups) into their own sub-bracket, via (m-1)
   applications of assoc_l2r -- mirrors the validated prototype's
   close_group() exactly, but through do_step_at(). */
static
void do_close_group_at(struct bridge_ctx *bctx, Ilist rel, int i, int m)
{
  int j;
  if (m <= 1 || bctx->failed)
    return;
  /* Recurse innermost-first: close the (m-1)-group starting one level
     deeper, THEN fold the element at depth i into it via one assoc_l2r
     at depth i. */
  for (j = m - 1; j >= 1; j--) {
    Ilist rel_d = rel_plus_depth(rel, i + j - 1);
    do_step_at(bctx, bctx->ax->assoc, bctx->ax->assoc_l2r_dir, rel_d);
    zap_ilist(rel_d);
  }
}  /* do_close_group_at */

static
void do_close_group(struct bridge_ctx *bctx, int i, int m)
{
  do_close_group_at(bctx, NULL, i, m);
}  /* do_close_group */

/* Full grouped bridge for the found node's subtree: reorder to the
   concatenation of groups[0..ngroups-1] (each group's own element list,
   in that group's own order), then carve out the group boundaries.
   Mirrors the validated prototype's bridge_to_groups(). */
static
void do_bridge_to_groups(struct bridge_ctx *bctx, Term **groups,
			int *group_sizes, int ngroups)
{
  Term flat_tgt[MAX_ACM_ARGS];
  int nflat = 0;
  int i, j;

  for (i = 0; i < ngroups; i++)
    for (j = 0; j < group_sizes[i]; j++)
      flat_tgt[nflat++] = groups[i][j];

  do_reorder(bctx, flat_tgt, nflat);
  if (bctx->failed)
    return;

  /* Each closed group collapses to occupy exactly one slot, so group i's
     own (still-flat) elements always start at absolute depth i, once
     groups 0..i-1 are already closed -- NOT at a cumulative sum of prior
     group sizes (that would be true only if closing left the earlier
     groups' elements still occupying their original per-leaf depths,
     which it doesn't). */
  for (i = 0; i < ngroups - 1 && !bctx->failed; i++) {
    do_close_group(bctx, i, group_sizes[i]);
  }
}  /* do_bridge_to_groups */

/* Number of flattened leaves of t w.r.t. AC symbol f (a term not headed
   by f counts as one leaf). */
static
int count_ac_leaves(Term t, int f)
{
  if (COMPLEX(t) && SYMNUM(t) == f && ARITY(t) == 2)
    return count_ac_leaves(ARG(t,0), f) + count_ac_leaves(ARG(t,1), f);
  return 1;
}  /* count_ac_leaves */

/* Right-associate the f-chain at base_pos ++ rel via real phantom assoc
   steps: while any left child along the chain is itself f-headed,
   rewrite f(f(a,b),c) -> f(a,f(b,c)) at that level.  Zero steps on an
   already right-associated chain, so always safe to run.  This is
   ac_canonical()'s re-bracketing half (no sorting -- do_reorder handles
   order separately), performed as kept, verifiable steps: in-place
   ac_canonical() is not an option on the pure-regrouping path, where
   the chain still belongs to `into`, a recorded proof clause that must
   not be mutated. */
static
void do_right_associate_at(struct bridge_ctx *bctx, Ilist rel)
{
  int d = 0;
  while (!bctx->failed) {
    Term node;
    Ilist path;
    int i;
    /* node = subterm at base_pos ++ rel ++ [2]*d */
    path = ilist_cat(copy_ilist(bctx->base_pos), copy_ilist(rel));
    for (i = 0; i < d; i++)
      path = ilist_append(path, 2);
    node = term_at_pos(ith_literal(bctx->current->literals, bctx->litnum)->atom,
		       path);
    if (!(node != NULL && COMPLEX(node) && SYMNUM(node) == bctx->f &&
	  ARITY(node) == 2)) {
      zap_ilist(path);
      return;  /* end of chain */
    }
    while (!bctx->failed) {
      Term left = ARG(node, 0);
      Ilist rel2;
      if (!(COMPLEX(left) && SYMNUM(left) == bctx->f && ARITY(left) == 2))
	break;
      rel2 = copy_ilist(rel);
      for (i = 0; i < d; i++)
	rel2 = ilist_append(rel2, 2);
      do_step_at(bctx, bctx->ax->assoc, bctx->ax->assoc_r2l_dir, rel2);
      zap_ilist(rel2);
      if (bctx->failed) {
	zap_ilist(path);
	return;
      }
      node = term_at_pos(ith_literal(bctx->current->literals, bctx->litnum)->atom,
			 path);
    }
    zap_ilist(path);
    d++;
  }
}  /* do_right_associate_at */

/* Re-bracket the (already ordered, already group-closed) chain at
   base_pos ++ rel into the exact top-level bracket tree of `shape`.
   Precondition (established by do_reorder + the do_close_group loop in
   do_bridge_to_groups): the chain's slots correspond 1:1, in order, to
   shape's flattened leaves -- each slot a single element or one closed
   (right-associated) group; only the LAST leaf's group may still lie
   splayed on the chain's tail, which is harmless because an in-order
   tree's last leaf is always reachable by pure right-spine descent, so
   no close below ever spans it.  A slot's INTERNAL shape never matters:
   the final plain unify binds shape's leaf (a variable, or a non-f term
   whose group is necessarily a single element) to the slot as a whole.
   Assoc-only -- the leaf order already matches, so no comm steps are
   needed.  Zero steps when shape is right-associated, so always safe to
   run. */
static
void do_rebracket_to_shape(struct bridge_ctx *bctx, Ilist rel, Term shape)
{
  Term left;
  int kl;

  if (bctx->failed)
    return;
  if (!(COMPLEX(shape) && SYMNUM(shape) == bctx->f && ARITY(shape) == 2))
    return;  /* leaf: the slot here already is what unify needs */

  left = ARG(shape, 0);
  kl = count_ac_leaves(left, bctx->f);

  if (kl > 1) {
    /* Close the first kl slots of this chain into one left child
       (internally right-associated), via kl-1 assoc folds, innermost
       first -- do_close_group()'s scheme at an arbitrary position. */
    int j, i;
    for (j = kl - 1; j >= 1 && !bctx->failed; j--) {
      Ilist rel2 = copy_ilist(rel);
      for (i = 0; i < j - 1; i++)
	rel2 = ilist_append(rel2, 2);
      do_step_at(bctx, bctx->ax->assoc, bctx->ax->assoc_l2r_dir, rel2);
      zap_ilist(rel2);
    }
    /* give the (now single) left child `left`'s own internal bracketing */
    {
      Ilist rel_l = ilist_append(copy_ilist(rel), 1);
      do_rebracket_to_shape(bctx, rel_l, left);
      zap_ilist(rel_l);
    }
  }
  /* kl == 1: the left child is a single slot -- nothing to close, and a
     leaf needs no internal reshaping (see header comment). */

  {
    Ilist rel_r = ilist_append(copy_ilist(rel), 2);
    do_rebracket_to_shape(bctx, rel_r, ARG(shape, 1));
    zap_ilist(rel_r);
  }
}  /* do_rebracket_to_shape */

/*************
 *
 *   Deep bridging: reshape the subject at base_pos ++ rel to be EXACTLY
 *   sigma(pattern)'s tree, at EVERY level -- not just one top-level AC
 *   chain.  Needed whenever the pattern's head is not the AC symbol but
 *   the pattern contains AC symbols inside, and whenever
 *   sigma-reconstructed elements are AC-equal to the subject's elements
 *   without being term_ident to them (apply() rebuilds a match_ac
 *   binding in its own bracketing).
 *
 *   After deep_bridge() + align_repeated_vars(), a PLAIN match/unify of
 *   the pattern against the subject region succeeds and re-derives one
 *   consistent substitution, so the real step replays as an ordinary
 *   single-position operation, exactly like the shallow bridges.
 *
 *************/

/* Occurrence record: an Ilist [varnum | rel-path...] per VARIABLE leaf
   of the pattern, collected in traversal order (see
   align_repeated_vars).  The variable's slot itself needs no reshaping
   -- a plain match binds it to whatever is there -- but REPEATED
   occurrences must end term_ident to each other, which AC-equal pairing
   does not guarantee. */

static void deep_bridge(struct bridge_ctx *bctx, Ilist rel, Term pattern,
			Context subst, Term partial, Plist *occs);

/* Does the subject chain at base_pos ++ rel consist of EXACTLY the
   multiset tgt[0..n-1], modulo AC (one-to-one AC-equal pairing, nothing
   missing, nothing left over)?  The guard both deep_bridge() and
   bridge_to_exact_term() run before reordering: a candidate can carry
   an interior partial match_ac (subject subtree strictly larger or
   smaller than sigma's reconstruction), and reordering on a mismatched
   chain either walks off its end or strands elements. */
static
BOOL chain_multiset_matches(struct bridge_ctx *bctx, Ilist rel,
			    Term *tgt, int n, int f)
{
  Term node, flat[MAX_ACM_ARGS];
  BOOL used[MAX_ACM_ARGS];
  int nflat = 0, i, j;
  Ilist full_pos = ilist_cat(copy_ilist(bctx->base_pos), copy_ilist(rel));

  node = term_at_pos(ith_literal(bctx->current->literals, bctx->litnum)->atom,
		     full_pos);
  zap_ilist(full_pos);
  if (node == NULL)
    return FALSE;
  if (COMPLEX(node) && SYMNUM(node) == f)
    flatten(node, flat, &nflat);
  else {
    flat[0] = node;
    nflat = 1;
  }
  if (nflat != n)
    return FALSE;
  for (i = 0; i < nflat; i++)
    used[i] = FALSE;
  for (i = 0; i < n; i++) {
    int k = -1;
    for (j = 0; j < nflat; j++)
      if (!used[j] && ac_equal_term(flat[j], tgt[i])) {
	k = j;
	break;
      }
    if (k < 0)
      return FALSE;
    used[k] = TRUE;
  }
  return TRUE;
}  /* chain_multiset_matches */

/* Walk `pattern`'s f-tree at base_pos ++ rel (whose f-skeleton the
   subject now shares, thanks to do_rebracket_to_shape); at each leaf,
   record a VARIABLE occurrence or recurse deep_bridge() into a complex
   leaf's slot.  tail_has_partial is TRUE only along the path to the
   RIGHTMOST leaf when a partial (superset-match leftover) is splayed on
   the chain's tail: a variable there simply absorbs the partial (the
   plain match binds it to the fatter chain -- same behavior as the
   validated shallow path), but a complex leaf cannot sit on top of a
   partial, so that candidate is declined. */
static
void deep_bridge_leaves(struct bridge_ctx *bctx, int f, Ilist rel,
			Term pattern, Context subst, Plist *occs,
			BOOL tail_has_partial)
{
  if (bctx->failed)
    return;
  if (COMPLEX(pattern) && SYMNUM(pattern) == f && ARITY(pattern) == 2) {
    Ilist rel_l = ilist_append(copy_ilist(rel), 1);
    Ilist rel_r = ilist_append(copy_ilist(rel), 2);
    deep_bridge_leaves(bctx, f, rel_l, ARG(pattern,0), subst, occs, FALSE);
    deep_bridge_leaves(bctx, f, rel_r, ARG(pattern,1), subst, occs,
		       tail_has_partial);
    zap_ilist(rel_l);
    zap_ilist(rel_r);
  }
  else if (VARIABLE(pattern))
    *occs = plist_prepend(*occs,
			  ilist_prepend(copy_ilist(rel), VARNUM(pattern)));
  else if (tail_has_partial)
    bctx->failed = TRUE;  /* complex leaf can't absorb the partial */
  else
    deep_bridge(bctx, rel, pattern, subst, NULL, occs);
}  /* deep_bridge_leaves */

static
void deep_bridge(struct bridge_ctx *bctx, Ilist rel, Term pattern,
		 Context subst, Term partial, Plist *occs)
{
  if (bctx->failed)
    return;

  if (VARIABLE(pattern)) {
    *occs = plist_prepend(*occs,
			  ilist_prepend(copy_ilist(rel), VARNUM(pattern)));
    return;
  }

  if (!is_assoc_comm(SYMNUM(pattern))) {
    /* Non-AC node: the heads already agree (guaranteed by the
       match_bt/unify_bt that produced subst); descend into children. */
    int i;
    for (i = 0; i < ARITY(pattern) && !bctx->failed; i++) {
      Ilist rel_i = ilist_append(copy_ilist(rel), i+1);
      deep_bridge(bctx, rel_i, ARG(pattern,i), subst, NULL, occs);
      zap_ilist(rel_i);
    }
    return;
  }

  /* AC node: the Stage-2 chain machinery, at this node's position, with
     AC-equal pairing (interiors get aligned by the leaf recursion). */
  {
    int f = SYMNUM(pattern);
    int save_f = bctx->f;
    struct ac_axiom_entry *save_ax = bctx->ax;
    struct ac_axiom_entry *ax = find_entry(bctx->axioms, f);
    Term pat_flat[MAX_AC_GROUPS];
    int npat = 0, i, ngroups, ntotal;
    Term **groups;
    Term *group_store;   /* heap -- a per-frame [32][2500] array would
			    blow the stack under recursion */
    int group_sizes[MAX_AC_GROUPS];
    Term flat_tgt[MAX_ACM_ARGS];

    if (ax == NULL || !ax->usable) {
      bctx->failed = TRUE;
      return;
    }
    bctx->f = f;
    bctx->ax = ax;

    do_right_associate_at(bctx, rel);

    flatten(pattern, pat_flat, &npat);
    ngroups = npat + (partial != NULL ? 1 : 0);
    if (npat > MAX_AC_GROUPS || ngroups > MAX_AC_GROUPS) {
      bctx->failed = TRUE;
      bctx->f = save_f;
      bctx->ax = save_ax;
      return;
    }

    groups = malloc(ngroups * sizeof(Term *));
    group_store = malloc((size_t) ngroups * MAX_ACM_ARGS * sizeof(Term));
    if (groups == NULL || group_store == NULL)
      fatal_error("deep_bridge, malloc failed");

    for (i = 0; i < npat; i++) {
      Term bound = apply(pat_flat[i], subst);
      int gs = 0;
      groups[i] = group_store + (size_t) i * MAX_ACM_ARGS;
      if (COMPLEX(bound) && SYMNUM(bound) == f)
	flatten(bound, groups[i], &gs);
      else {
	groups[i][0] = bound;
	gs = 1;
      }
      group_sizes[i] = gs;
    }
    if (partial != NULL) {
      int gs = 0;
      groups[npat] = group_store + (size_t) npat * MAX_ACM_ARGS;
      if (COMPLEX(partial) && SYMNUM(partial) == f)
	flatten(partial, groups[npat], &gs);
      else {
	groups[npat][0] = partial;
	gs = 1;
      }
      group_sizes[npat] = gs;
    }

    ntotal = 0;
    for (i = 0; i < ngroups && !bctx->failed; i++) {
      int j;
      for (j = 0; j < group_sizes[i]; j++) {
	if (ntotal >= MAX_ACM_ARGS) {
	  bctx->failed = TRUE;
	  break;
	}
	flat_tgt[ntotal++] = groups[i][j];
      }
    }

    /* Guard: the subject chain must be EXACTLY this multiset (mod AC)
       before any reordering -- see chain_multiset_matches(). */
    if (!bctx->failed &&
	!chain_multiset_matches(bctx, rel, flat_tgt, ntotal, f))
      bctx->failed = TRUE;

    if (!bctx->failed)
      do_reorder_at(bctx, rel, flat_tgt, ntotal, TRUE);
    for (i = 0; i < ngroups - 1 && !bctx->failed; i++)
      do_close_group_at(bctx, rel, i, group_sizes[i]);
    if (!bctx->failed)
      do_rebracket_to_shape(bctx, rel, pattern);

    free(groups);
    free(group_store);

    if (!bctx->failed)
      deep_bridge_leaves(bctx, f, rel, pattern, subst, occs,
			 partial != NULL);

    bctx->f = save_f;
    bctx->ax = save_ax;
  }
}  /* deep_bridge */

/* Reshape the subject at base_pos ++ rel to be term_ident to `target`
   (precondition: AC-equal to it).  Used by align_repeated_vars() to
   make every occurrence of a repeated pattern variable bit-identical,
   so the final plain match re-derives ONE consistent binding. */

static void bridge_to_exact_leaves(struct bridge_ctx *bctx, int f,
				   Ilist rel, Term target);

static
void bridge_to_exact_term(struct bridge_ctx *bctx, Ilist rel, Term target)
{
  Term node;
  Ilist full;

  if (bctx->failed)
    return;

  full = ilist_cat(copy_ilist(bctx->base_pos), copy_ilist(rel));
  node = term_at_pos(ith_literal(bctx->current->literals, bctx->litnum)->atom,
		     full);
  zap_ilist(full);
  if (node == NULL) {
    bctx->failed = TRUE;
    return;
  }
  if (term_ident(node, target))
    return;  /* already exact -- the common case */

  if (VARIABLE(target) || ARITY(target) == 0) {
    /* AC-equal atomics are identical; a mismatch here means the
       precondition didn't hold (e.g. a partial-fattened first
       occurrence) -- decline the candidate. */
    bctx->failed = TRUE;
    return;
  }

  if (!is_assoc_comm(SYMNUM(target))) {
    int i;
    if (SYMNUM(node) != SYMNUM(target)) {
      bctx->failed = TRUE;
      return;
    }
    for (i = 0; i < ARITY(target) && !bctx->failed; i++) {
      Ilist rel_i = ilist_append(copy_ilist(rel), i+1);
      bridge_to_exact_term(bctx, rel_i, ARG(target,i));
      zap_ilist(rel_i);
    }
    return;
  }

  /* AC node: right-associate, reorder to target's own flat order
     (AC-equal pairing), re-bracket to target's exact tree, then align
     each element's interior. */
  {
    int f = SYMNUM(target);
    int save_f = bctx->f;
    struct ac_axiom_entry *save_ax = bctx->ax;
    struct ac_axiom_entry *ax = find_entry(bctx->axioms, f);
    Term tgt_flat[MAX_ACM_ARGS];
    int n = 0;

    if (ax == NULL || !ax->usable) {
      bctx->failed = TRUE;
      return;
    }
    bctx->f = f;
    bctx->ax = ax;

    do_right_associate_at(bctx, rel);
    flatten(target, tgt_flat, &n);
    if (!chain_multiset_matches(bctx, rel, tgt_flat, n, f)) {
      bctx->failed = TRUE;   /* not AC-equal after all (e.g. a
				partial-fattened first occurrence) */
      bctx->f = save_f;
      bctx->ax = save_ax;
      return;
    }
    do_reorder_at(bctx, rel, tgt_flat, n, TRUE);
    if (!bctx->failed)
      do_rebracket_to_shape(bctx, rel, target);
    if (!bctx->failed)
      bridge_to_exact_leaves(bctx, f, rel, target);

    bctx->f = save_f;
    bctx->ax = save_ax;
  }
}  /* bridge_to_exact_term */

static
void bridge_to_exact_leaves(struct bridge_ctx *bctx, int f, Ilist rel,
			    Term target)
{
  if (bctx->failed)
    return;
  if (COMPLEX(target) && SYMNUM(target) == f && ARITY(target) == 2) {
    Ilist rel_l = ilist_append(copy_ilist(rel), 1);
    Ilist rel_r = ilist_append(copy_ilist(rel), 2);
    bridge_to_exact_leaves(bctx, f, rel_l, ARG(target,0));
    bridge_to_exact_leaves(bctx, f, rel_r, ARG(target,1));
    zap_ilist(rel_l);
    zap_ilist(rel_r);
  }
  else
    bridge_to_exact_term(bctx, rel, target);
}  /* bridge_to_exact_leaves */

/* occs arrives in pattern-traversal order (caller reverses the
   prepend-built list first).  For each variable with more than one
   occurrence: read the FIRST occurrence's content fresh (copied --
   every do_step_at copies the whole clause, so raw pointers go stale)
   and bridge every LATER occurrence to be term_ident to it.  Positions
   are pattern positions of DISTINCT leaves, so bridging one occurrence
   never disturbs another. */
static
void align_repeated_vars(struct bridge_ctx *bctx, Plist occs)
{
  Plist o1, o2;
  for (o1 = occs; o1 && !bctx->failed; o1 = o1->next) {
    Ilist e1 = o1->v;
    int v = e1->i;
    BOOL first = TRUE;
    Term content1 = NULL;
    for (o2 = occs; o2 != o1; o2 = o2->next)
      if (((Ilist) o2->v)->i == v) {
	first = FALSE;
	break;
      }
    if (!first)
      continue;
    for (o2 = o1->next; o2 && !bctx->failed; o2 = o2->next) {
      Ilist e2 = o2->v;
      if (e2->i != v)
	continue;
      if (content1 == NULL) {
	Ilist full = ilist_cat(copy_ilist(bctx->base_pos),
			       copy_ilist(e1->next));
	Term t = term_at_pos(ith_literal(bctx->current->literals,
					 bctx->litnum)->atom, full);
	zap_ilist(full);
	if (t == NULL) {
	  bctx->failed = TRUE;
	  break;
	}
	content1 = copy_term(t);
      }
      bridge_to_exact_term(bctx, e2->next, content1);
    }
    if (content1 != NULL)
      zap_term(content1);
  }
}  /* align_repeated_vars */

static
void zap_occs(Plist occs)
{
  Plist p;
  for (p = occs; p; p = p->next)
    zap_ilist(p->v);
  zap_plist(occs);
}  /* zap_occs */

/* (is_right_associated() used to live here: the bridging entries
   declined candidates whose matched node wasn't right-associated.
   do_right_associate_at() now re-brackets such chains with real phantom
   steps instead, so nothing needs the predicate any more.) */

/* Top-level PARTIAL (superset) AC demod match: an AC-headed pattern P
   matches only SOME of the chain's elements; the rest are
   subst->partial_term.  match_bt allows this (its "partial" flag), and
   it is exactly how a collapsing/absorbing demodulator applies inside a
   bigger chain -- e.g. +(A,A)=A rewriting a duplicated pair.  But the
   FINAL rewrite goes through demod_at_position()'s PLAIN match(), which
   does NOT do superset matching, so the matched elements must first be
   CLOSED into their own left sub-bracket B shaped exactly like
   sigma(P); the chain becomes f(B, rest) and the demod rewrites B at
   position [1].  Fills *out_rel with that relative path (caller owns
   it) and returns; leaves bctx->failed set on any mismatch. */
static
void deep_bridge_partial(struct bridge_ctx *bctx, Term pattern,
			 Context subst, Term partial, Plist *occs,
			 Ilist *out_rel)
{
  int f = SYMNUM(pattern);
  struct ac_axiom_entry *ax = find_entry(bctx->axioms, f);
  Term pat_flat[MAX_AC_GROUPS];
  Term flat_tgt[MAX_ACM_ARGS];
  int npat = 0, i, ntotal = 0, matched_count;
  Ilist rel_left;

  *out_rel = NULL;
  if (ax == NULL || !ax->usable) { bctx->failed = TRUE; return; }
  bctx->f = f;
  bctx->ax = ax;

  do_right_associate_at(bctx, NULL);
  if (bctx->failed) return;

  /* matched elements = sigma applied to every pattern leaf, flattened */
  flatten(pattern, pat_flat, &npat);
  for (i = 0; i < npat; i++) {
    Term bound = apply(pat_flat[i], subst);
    if (COMPLEX(bound) && SYMNUM(bound) == f) {
      Term sub[MAX_ACM_ARGS];
      int ns = 0, j;
      flatten(bound, sub, &ns);
      for (j = 0; j < ns && ntotal < MAX_ACM_ARGS; j++)
	flat_tgt[ntotal++] = sub[j];
    }
    else if (ntotal < MAX_ACM_ARGS)
      flat_tgt[ntotal++] = bound;
  }
  matched_count = ntotal;

  /* partial (leftover) elements */
  {
    Term sub[MAX_ACM_ARGS];
    int ns = 0, j;
    if (COMPLEX(partial) && SYMNUM(partial) == f)
      flatten(partial, sub, &ns);
    else { sub[0] = partial; ns = 1; }
    for (j = 0; j < ns && ntotal < MAX_ACM_ARGS; j++)
      flat_tgt[ntotal++] = sub[j];
  }

  if (matched_count < 2 || ntotal <= matched_count) {
    /* Not actually a superset match (nothing left over, or the pattern
       collapsed to a single slot) -- let the caller's ordinary
       full-match path handle it. */
    bctx->failed = TRUE;
    return;
  }

  if (!chain_multiset_matches(bctx, NULL, flat_tgt, ntotal, f)) {
    bctx->failed = TRUE;
    return;
  }
  do_reorder_at(bctx, NULL, flat_tgt, ntotal, TRUE);
  if (bctx->failed) return;

  /* Close the first matched_count elements into one left sub-bracket;
     the chain is now f( B, rest ) with B at position [1]. */
  do_close_group_at(bctx, NULL, 0, matched_count);
  if (bctx->failed) return;

  /* Give B exactly sigma(pattern)'s tree and align repeated pattern
     variables inside it, so the plain rewrite at [1] re-derives one
     consistent substitution. */
  rel_left = ilist_append(NULL, 1);
  deep_bridge(bctx, rel_left, pattern, subst, NULL, occs);
  *out_rel = rel_left;
}  /* deep_bridge_partial */

/*************
 *
 *   expand_ac_demod_entry(): top-level orchestrator.
 *
 *************/

/* PUBLIC */
Plist expand_ac_demod_entry(Topform work, Topform demod, int direction,
			   Ac_axiom_set axioms,
			   int *next_id, I3list *map,
			   int old_id, int *old_id_n,
			   int *alt_start,
			   Topform *out_result)
{
  int alt_index;
  /* Pattern side by direction: AC-headed citations are ORIENTED only
     (dir 1), but the deep-bridging fallback replays PLAIN demod
     citations too, and those can rewrite right-to-left. */
  Term pattern = ARG(demod->literals->atom, direction == 1 ? 0 : 1);
  Plist new_proof = NULL;
  BOOL dbg = (getenv("PC_DEBUG_TRACE") != NULL);

  if (dbg)
    fprintf(stderr, "AC_DEMOD_STAT: entry old_id=%d demod_id=%d alt_start=%d\n",
	    old_id, (int) demod->id, *alt_start);

  if (!term_contains_ac(pattern)) {
    /* Nothing AC anywhere in the pattern: an AC-aware retry of a failed
       plain replay cannot succeed where the plain one didn't. */
    if (dbg)
      fprintf(stderr, "AC_DEMOD_STAT: old_id=%d demod_id=%d FAILURE "
	      "(pattern contains no AC symbol; nothing to bridge)\n",
	      old_id, (int) demod->id);
    *out_result = NULL;
    return NULL;
  }

  for (alt_index = *alt_start; alt_index < 1000; alt_index++) {
    Ilist tree_pos;
    Context subst;
    Term matched_node;
    Btm_state bt;

    if (!find_ac_demod_candidate(work, demod, direction, alt_index,
				 &tree_pos, &subst, &matched_node, &bt)) {
      if (dbg)
	fprintf(stderr, "AC_DEMOD_STAT: old_id=%d demod_id=%d EXHAUSTED "
		"at alt_index=%d\n", old_id, (int) demod->id, alt_index);
      break;  /* candidates exhausted */
    }

    /* No right-associated pre-check any more: deep_bridge()'s own
       do_right_associate_at() re-brackets via real phantom steps. */
    (void) matched_node;

    {
      struct bridge_ctx bctx;
      Plist occs = NULL;
      Ilist litnum_and_pos = tree_pos;
      int litnum = litnum_and_pos->i;

      bctx.current = work;
      bctx.litnum = litnum;
      bctx.base_pos = litnum_and_pos->next;
      bctx.f = 0;    /* set per AC node by deep_bridge() */
      bctx.ax = NULL;
      bctx.axioms = axioms;
      bctx.next_id = next_id;
      bctx.map = map;
      bctx.old_id = old_id;
      bctx.old_id_n = old_id_n;
      bctx.new_proof = &new_proof;
      bctx.failed = FALSE;

      /* Reshape the whole matched region to sigma(pattern)'s exact tree
	 -- every AC level, not just the top chain (the pattern's head
	 need not even be an AC symbol) -- then make repeated pattern
	 variables' occurrences bit-identical so the final plain match
	 re-derives one consistent substitution.

	 A top-level PARTIAL (superset) AC match -- pattern AC-headed and
	 subst carries a partial_term -- needs the matched elements closed
	 into a sub-bracket first (plain match() can't do superset); the
	 demod then rewrites that sub-bracket at rel_rewrite instead of at
	 the whole node.  See deep_bridge_partial(). */
      {
	Ilist rel_rewrite = NULL;   /* NULL = rewrite the whole node */
	Term partial = subst->partial_term;
	if (partial != NULL && COMPLEX(pattern) &&
	    is_assoc_comm(SYMNUM(pattern))) {
	  deep_bridge_partial(&bctx, pattern, subst, partial, &occs,
			      &rel_rewrite);
	  /* deep_bridge_partial sets bctx.failed for a non-superset match
	     (nothing actually left over); fall back to the ordinary
	     full-match path in that case. */
	  if (bctx.failed && rel_rewrite == NULL) {
	    bctx.failed = FALSE;
	    zap_occs(occs);
	    occs = NULL;
	    deep_bridge(&bctx, NULL, pattern, subst, NULL, &occs);
	  }
	}
	else
	  deep_bridge(&bctx, NULL, pattern, subst, partial, &occs);

	if (!bctx.failed) {
	  occs = reverse_plist(occs);  /* prepend-built -> traversal order */
	  align_repeated_vars(&bctx, occs);
	}
	zap_occs(occs);

	if (!bctx.failed) {
	  /* Final real step: the site is now shaped exactly like the
	     pattern, so the ordinary demodulator applies as a plain,
	     single-position step (at the matched sub-bracket, for a
	     superset match). */
	  if (rel_rewrite != NULL)
	    do_step_at(&bctx, demod, direction, rel_rewrite);
	  else
	    do_step(&bctx, demod, direction, 0);
	}
	zap_ilist(rel_rewrite);
      }

      /* match_bt_cancel() before free_context() -- see try_node()'s
	 comment; this is the same requirement as the is_right_associated
	 early-continue above, just on the success/bctx.failed path. */
      match_bt_cancel(bt);
      free_context(subst);

      if (!bctx.failed) {
	if (dbg)
	  fprintf(stderr, "AC_DEMOD_STAT: old_id=%d demod_id=%d alt_index=%d "
		  "SUCCESS\n", old_id, (int) demod->id, alt_index);
	/* Advance past this candidate so the caller's chain-odometer can
	   resume from the next one when the END of the compound chain
	   doesn't reproduce the recorded clause (demod rediscovery is
	   position-multi-valued, exactly like para candidates; see
	   maybe_ac_para_retry in xproofs.c). */
	*alt_start = alt_index + 1;
	*out_result = bctx.current;
	/* Same order hazard as expand_ac_para_entry's identical fix (see
	   the long comment there): new_proof is in prepend (newest-first)
	   order, and the caller's splice loop head-to-tail-prepends into
	   the outer proof, so a MULTI-step list would land reversed --
	   children printing before the bridge steps they cite, failing
	   check_parents_and_uplinks_in_proof ("parents not seen"). */
	return reverse_plist(new_proof);
      }
      else {
	/* This candidate didn't pan out.  Deliberately leak the partial
	   step sequence's clauses rather than risk freeing structure
	   still shared with `work`/`current` (this is a rare backtrack
	   path in a one-shot, post-hoc proof-expansion utility, not a
	   hot path -- correctness over memory economy here). */
	if (dbg)
	  fprintf(stderr, "AC_DEMOD_STAT: old_id=%d demod_id=%d alt_index=%d "
		  "declined (bridge or final rewrite step failed)\n",
		  old_id, (int) demod->id, alt_index);
	new_proof = NULL;
      }
    }
  }

  if (dbg)
    fprintf(stderr, "AC_DEMOD_STAT: old_id=%d demod_id=%d TOTAL FAILURE "
	    "(all alt_index exhausted)\n", old_id, (int) demod->id);
  *out_result = NULL;
  return NULL;
}  /* expand_ac_demod_entry */

/*************
 *
 *   Phase 2: AC-aware rediscovery for PARA_JUST -- find_ac_para_candidate().
 *
 *   PARA_JUST's into_pos records the exact literal AND position the
 *   original search's paramodulation applied at (para_into() builds it
 *   explicitly at the moment of application -- never ambiguous the way
 *   DEMOD_JUST's multi-citation position is), but not which grouping of
 *   into's own AC-chain elements the original unifier picked; that part
 *   is rediscovered here, by walking every subterm of every literal of
 *   `into` (the recorded position is not re-used, on the same "trust
 *   only what's unambiguous, rediscover the rest" principle as Phase 1)
 *   looking for a node whose top symbol matches alpha's, and enumerating
 *   candidate unifiers via btu.c's unify_bt_first/next -- full AC
 *   unification, unlike Phase 1's one-sided match_bt_first/next, since
 *   paramodulation unifies two terms that can each carry variables.
 *
 *************/

struct ac_find_para_ctx {
  Term alpha;
  int target_sn;
  int alt_index;
  int count;
  BOOL done;
  Context found_from_subst;
  Context found_into_subst;
  Term found_node;
  Btu_state found_bt;
};

static
void try_node_para(Term node, struct ac_find_para_ctx *ctx)
{
  if (ctx->done)
    return;
  if (COMPLEX(node) && SYMNUM(node) == ctx->target_sn) {
    Context c1 = get_context();
    Context c2 = get_context();
    Btu_state bt = unify_bt_first(ctx->alpha, c1, node, c2);
    while (bt != NULL && !ctx->done) {
      if (ctx->count == ctx->alt_index) {
	ctx->found_from_subst = c1;
	ctx->found_into_subst = c2;
	ctx->found_node = node;
	ctx->found_bt = bt;
	ctx->done = TRUE;
	/* bindings stay live in c1/c2 -- caller owns bt now and MUST call
	   unify_bt_cancel(bt) before free_context() on EITHER context.
	   unify_bt_first/next bind straight into c1/c2 via their own
	   internal trail, exactly like match_bt_first/next does (see
	   try_node()'s comment above for the dirty-Context-freelist
	   mechanism this guards against) -- the same hazard applies here
	   verbatim, not just by analogy: btu.c and btm.c share the
	   underlying Context/Trail machinery. */
      }
      else {
	ctx->count++;
	bt = unify_bt_next(bt);
      }
    }
    if (!ctx->done) {
      free_context(c1);
      free_context(c2);
    }
  }
}  /* try_node_para */

static
void walk_term_para(Term t, struct ac_find_para_ctx *ctx)
{
  int i;
  if (ctx->done || VARIABLE(t))
    return;
  try_node_para(t, ctx);
  if (ctx->done)
    return;
  for (i = 0; i < ARITY(t) && !ctx->done; i++)
    walk_term_para(ARG(t,i), ctx);
}  /* walk_term_para */

/* PUBLIC
   Enumeration is keyed on alpha's head symbol, whatever it is -- an
   AC-headed alpha gets the shallow group bridging, any other complex
   alpha gets deep bridging; only a bare-variable alpha has nothing to
   key the walk on and is declined.

   When `into_pos` is non-NULL (the recorded PARA_JUST site), unifiers
   are enumerated AT THAT NODE first.  para_into() builds into_pos
   explicitly at application time -- unlike DEMOD_JUST sequence numbers
   it is not advisory -- so a full walk over every same-head subterm
   produces many valid-but-irrelevant AC unifiers (observed: residual
   c_21726, every free-walk candidate left no redex for the trailing
   rewrite).  Full walk is the fallback if the recorded site has no
   unifier at all. */
BOOL find_ac_para_candidate(Topform from, Ilist from_pos, Topform into,
			   Ilist into_pos,
			   int alt_index,
			   Ilist *out_into_tree_pos, Context *out_from_subst,
			   Context *out_into_subst, Term *out_alpha,
			   Term *out_matched_node, Btu_state *out_bt)
{
  struct ac_find_para_ctx ctx;
  Literals from_lit = ith_literal(from->literals, from_pos->i);
  int from_side = (from_pos->next->i == 1 ? 0 : 1);
  Term alpha = ARG(from_lit->atom, from_side);
  Literals lit;
  int litnum = 0;

  if (VARIABLE(alpha))
    return FALSE;

  ctx.alpha = alpha;
  ctx.target_sn = SYMNUM(alpha);
  ctx.alt_index = alt_index;
  ctx.count = 0;
  ctx.done = FALSE;
  ctx.found_from_subst = NULL;
  ctx.found_into_subst = NULL;
  ctx.found_node = NULL;
  ctx.found_bt = NULL;

  /* Prefer the recorded into site. */
  if (into_pos != NULL) {
    Literals into_lit = ith_literal(into->literals, into_pos->i);
    Term into_term = (into_lit != NULL)
      ? term_at_pos(into_lit->atom, into_pos->next) : NULL;
    if (into_term != NULL && !VARIABLE(into_term)) {
      try_node_para(into_term, &ctx);
      if (ctx.done) {
	*out_into_tree_pos = copy_ilist(into_pos);
	*out_from_subst = ctx.found_from_subst;
	*out_into_subst = ctx.found_into_subst;
	*out_alpha = alpha;
	*out_matched_node = ctx.found_node;
	*out_bt = ctx.found_bt;
	return TRUE;
      }
    }
    /* Recorded site had no unifier for this alt_index.  If alt_index>0
       the site simply ran out of alts -- do not fall through into a
       free walk (that would renumber alts and reintroduce irrelevant
       sites).  Only fall through when alt_index==0 and the site itself
       produced nothing, so a free walk might still recover. */
    if (alt_index > 0)
      return FALSE;
    /* reset for free-walk fallback */
    ctx.count = 0;
    ctx.done = FALSE;
  }

  for (lit = into->literals; lit && !ctx.done; lit = lit->next) {
    litnum++;
    walk_term_para(lit->atom, &ctx);
    if (ctx.done) {
      Ilist rel_pos = position_of_subterm(lit->atom, ctx.found_node);
      *out_into_tree_pos = ilist_prepend(rel_pos, litnum);
      *out_from_subst = ctx.found_from_subst;
      *out_into_subst = ctx.found_into_subst;
      *out_alpha = alpha;
      *out_matched_node = ctx.found_node;
      *out_bt = ctx.found_bt;
      return TRUE;
    }
  }
  return FALSE;
}  /* find_ac_para_candidate */

/*************
 *
 *   groups_found_in_node(): the "is this candidate pure regrouping"
 *   precondition for Phase 2's into-side-only bridging.
 *
 *   Phase 1's demod bridging only ever permutes/regroups the SUBJECT's
 *   own existing pieces -- match_bt never binds the subject's own
 *   variables, so there is nothing else it could do.  Full AC
 *   unification (unify_bt) is not so constrained: the found (from_subst,
 *   into_subst) pair could, in general, bind a variable WITHIN
 *   matched_node's own scope to a piece that comes from alpha's side --
 *   a genuine instantiation, not a permutation, which do_bridge_to_groups
 *   (comm/assoc rewrites only) cannot perform.  This checks that every
 *   leaf of every target group can be found, by exact identity, among
 *   matched_node's OWN flattened elements, with none left over -- i.e.
 *   the candidate's unifier only ever regrouped pieces already present
 *   in `node`, never introduced a new one.  Returning FALSE here is not
 *   a soundness concern -- see expand_ac_para_entry()'s call site -- it
 *   just means this candidate is out of scope for this implementation
 *   pass and the next alt_index should be tried instead.
 *
 *************/

static
BOOL groups_found_in_node(Term node, int f, Term **groups,
			  int *group_sizes, int ngroups)
{
  Term flat[MAX_ACM_ARGS];
  BOOL used[MAX_ACM_ARGS];
  int nflat = 0, i, j;

  if (COMPLEX(node) && SYMNUM(node) == f)
    flatten(node, flat, &nflat);
  else {
    flat[0] = node;
    nflat = 1;
  }
  for (i = 0; i < nflat; i++)
    used[i] = FALSE;

  for (i = 0; i < ngroups; i++) {
    for (j = 0; j < group_sizes[i]; j++) {
      int k = -1, m;
      for (m = 0; m < nflat; m++) {
	if (!used[m] && term_ident(flat[m], groups[i][j])) { k = m; break; }
      }
      if (k < 0)
	return FALSE;
      used[k] = TRUE;
    }
  }
  /* Every one of node's own leaves must be claimed by some group too --
     an unclaimed leftover would be stranded outside every group once
     do_bridge_to_groups reshapes according to the found grouping. */
  for (i = 0; i < nflat; i++)
    if (!used[i])
      return FALSE;
  return TRUE;
}  /* groups_found_in_node */

/*************
 *
 *   ac_result_matches_expected(): is `result` an acceptable stand-in for
 *   the recorded proof clause `expected`?
 *
 *   clause_ident() (literals.c) requires EXACT identity -- same literal
 *   order, same variable numbers -- which Phase 1's bridging always
 *   satisfies (match_bt only ever binds the DEMODULATOR's variables,
 *   never the subject's, so the subject's own numbering never changes).
 *   Phase 2's into-side instantiation genuinely binds `into`'s own
 *   previously-free variables, and AC unification is multi-valued with
 *   no record of which specific unifier the original search used, so an
 *   independently-rediscovered (but equally sound) substitution can
 *   legitimately reconstruct a clause that is AC-equivalent to `expected`
 *   without being bit-for-bit identical to it.  This compares on COPIES
 *   (ac_canonical() mutates in place) after AC-canonicalizing both
 *   sides, using variant() (unify.c) instead of
 *   term_ident() so a consistent variable renaming doesn't cause a
 *   spurious reject -- still fully sound: a variant of an AC-canonical
 *   form of `expected` is exactly as valid a replacement for the compact
 *   citation as an identical copy would be.
 *
 *************/
/* PUBLIC */
BOOL ac_result_matches_expected(Topform result, Topform expected)
{
  Literals l1 = result->literals, l2 = expected->literals;
  BOOL ok = TRUE;

  while (l1 && l2 && ok) {
    Term c1, c2;

    if (l1->sign != l2->sign) { ok = FALSE; break; }
    c1 = copy_term(l1->atom);
    c2 = copy_term(l2->atom);
    ac_canonical(c1, -1);
    ac_canonical(c2, -1);
    /* AC-variant check: each side AC-MATCHES the other (btm.c's
       match_bt, the same one-sided AC matcher the live search uses);
       mutual instances modulo AC = identical modulo AC + a consistent
       variable renaming.  Comparing the two ac_canonical() forms with
       variant() instead would be ORDER-FRAGILE: ac_canonical's sort key
       includes variable NUMBERS, so a renaming that changes the sort
       order can make two genuine AC-variants canonicalize into forms
       that are no longer term-variants (the ac_canonical() calls above
       are retained only to keep match_bt's inputs in its expected
       canonical form).  match_bt_cancel() must run before
       free_context() -- see try_node()'s comment on the
       dirty-Context-freelist hazard. */
    {
      Context cx = get_context();
      Btm_state bt = match_bt_first(c1, cx, c2, FALSE);
      BOOL fwd = (bt != NULL);
      if (bt != NULL)
	match_bt_cancel(bt);
      free_context(cx);
      if (fwd) {
	cx = get_context();
	bt = match_bt_first(c2, cx, c1, FALSE);
	ok = (bt != NULL);
	if (bt != NULL)
	  match_bt_cancel(bt);
	free_context(cx);
      }
      else
	ok = FALSE;
    }
    zap_term(c1);
    zap_term(c2);
    l1 = l1->next;
    l2 = l2->next;
  }
  return ok && l1 == NULL && l2 == NULL;
}  /* ac_result_matches_expected */

/*************
 *
 *   expand_ac_para_entry(): Phase 2 top-level orchestrator.
 *
 *   Alpha's own top-level AC structure, flattened exactly like a
 *   DEMOD_JUST pattern's LHS in Phase 1, determines the target grouping
 *   (via apply(alpha_flat[i], from_subst) -- the exact same
 *   group-building logic as expand_ac_demod_entry, just sourced from
 *   alpha/from_subst instead of a demodulator's lhs/match substitution).
 *
 *   Two cases, tried in order:
 *
 *   1. Pure regrouping: matched_node's own EXISTING flattened elements
 *      already contain every needed leaf (groups_found_in_node()) --
 *      permute/regroup them via do_bridge_to_groups() et al., completely
 *      unchanged from Phase 1.  This is sound by construction: comm/assoc
 *      rewrites only ever permute a clause's own existing pieces.
 *
 *   2. Into-side instantiation ("both-sides"): the common case for
 *      genuine AC-dependent paramodulation, not a rare corner case.
 *      Comm/assoc rewriting cannot invent a value
 *      for a free variable -- that is universal instantiation, a
 *      different, independently-sound FOL rule.  When pure regrouping
 *      fails, commit directly to a real INSTANCE_JUST step -- instantiate_
 *      clause() applied to into's WHOLE clause (matching paramodulate()'s own
 *      apply_lit_para() semantics: the substitution must apply
 *      everywhere the variable occurs, not just at the rewritten
 *      position, or the resulting clause would be internally
 *      inconsistent) -- then retry case 1 against the now-more-specific
 *      matched_node.  This exact "instantiate a parent into its own
 *      step, then build the real inference off of it" shape already has
 *      two independent precedents in this codebase:
 *      ivy.c's instantiate_inference() (same instantiate_clause() core,
 *      same upward_clause_links()/inherit_attributes() follow-up) and
 *      apps.src/directproof.c's forward_proof() CASE 3 (using the same
 *      general instance_just() constructor used here, rather than
 *      ivy.c's Ivy-specific ivy_just(INSTANCE_JUST,...) wrapper).
 *      Genuine FROM-side instantiation (from's own free variables, via
 *      from_subst) is not implemented: alpha's own AC substructure is
 *      already bracket-independent via flatten(), which covers the
 *      "from-side also needs reshaping" concern; extend symmetrically
 *      if a case ever needs from's own free variables bound too.
 *
 *   Once bridged, matched_node's shape matches alpha's own
 *   un-substituted recursive structure level-for-level, so the final
 *   real step is just an ordinary, position-based para_pos() call --
 *   paramodulate() already calls upward_clause_links() internally
 *   (paramod.c:186), so no demod_at_position()-style uplink fixup is
 *   needed for THAT step (only the instantiation step needs its own,
 *   per instantiate_clause()'s own contract -- see call site below).
 *
 *   Bounded retry over match alternatives (per the original spec):
 *   rediscovery via unify_bt is multi-valued -- a mechanically valid
 *   bridge + para_pos() replay does not guarantee the SAME clause the
 *   original search actually derived (a different, equally sound AC
 *   unifier can reconstruct a different-looking clause).  `expected` is
 *   the recorded proof clause the caller is trying to reproduce; a
 *   `result` that replays but fails ac_result_matches_expected() against
 *   it is treated exactly like any other failed candidate (falls through
 *   to the shared "leak and continue" reset below) so the alt_index loop
 *   tries the next alternative instead of committing to the first one
 *   found: an exact clause_ident() bar is fundamentally too strict for
 *   comparing an independently-rediscovered AC unifier's result against
 *   the search's own (unrecorded) substitution choice; see
 *   ac_result_matches_expected()'s own comment.
 *
 *   Judging the candidate here is only possible when the PARA_JUST is
 *   the WHOLE recorded line.  When the compound justification carries a
 *   secondary rewrite suffix (para(...) followed by rewrite([...]) --
 *   the recorded clause is the END of that chain, and the bare
 *   paramodulant built here can never equal it.  For that case the
 *   caller passes
 *   expected == NULL, this function returns each mechanically valid
 *   candidate in turn (resuming from `alt_start`, which is advanced past
 *   every returned candidate), and the caller replays the rewrite suffix
 *   on top and judges the END of the chain against the recorded clause,
 *   rolling back and calling again on a mismatch -- see the
 *   maybe_ac_para_retry path in xproofs.c's expand_proof().
 *
 *************/

/* PUBLIC */
Plist expand_ac_para_entry(Topform from, Ilist from_pos,
			  Topform into, Ilist into_pos,
			  Ac_axiom_set axioms,
			  int *next_id, I3list *map,
			  int old_id, int *old_id_n,
			  int *alt_start,
			  Topform expected,
			  Topform *out_result)
{
  int alt_index;
  Plist new_proof = NULL;
  BOOL dbg = (getenv("PC_DEBUG_TRACE") != NULL);

  if (dbg)
    fprintf(stderr, "AC_PARA_STAT: entry from_id=%d into_id=%d alt_start=%d%s\n",
	    (int) from->id, (int) into->id, *alt_start,
	    expected == NULL ? " (deferred judging: caller replays the rewrite suffix first)" : "");

  for (alt_index = *alt_start; alt_index < 1000; alt_index++) {
    Ilist into_tree_pos;
    Context from_subst, into_subst;
    Term alpha, matched_node;
    Btu_state bt;
    int f;
    struct ac_axiom_entry *ax;
    BOOL deep_mode;

    /* Pass the recorded into_pos so rediscovery enumerates AC unifiers
       at the search's actual application site first (see
       find_ac_para_candidate). */
    if (!find_ac_para_candidate(from, from_pos, into, into_pos, alt_index,
				&into_tree_pos, &from_subst, &into_subst,
				&alpha, &matched_node, &bt)) {
      if (dbg)
	fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d EXHAUSTED at alt_index=%d\n",
		(int) from->id, (int) into->id, alt_index);
      break;  /* candidates exhausted */
    }

    if (dbg && getenv("PC_DEBUG_TRACE2") != NULL) {
      Term a_i = apply(alpha, from_subst);
      Term m_i = apply(matched_node, into_subst);
      fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d WITNESS "
	      "alpha_applied=", (int) from->id, (int) into->id, alt_index);
      fprint_term(stderr, a_i);
      fprintf(stderr, "  matched_node_applied=");
      fprint_term(stderr, m_i);
      fprintf(stderr, "\n");
      zap_term(a_i);
      zap_term(m_i);
    }

    deep_mode = !is_assoc_comm(SYMNUM(alpha));

    if (deep_mode) {
      /* Alpha's head is not the AC symbol (e.g. n-headed with '+'
	 inside, promoted here by xproofs.c when their plain replay
	 fails): the shallow top-level group machinery doesn't apply;
	 deep_bridge() below reshapes the matched region to sigma(alpha)'s
	 exact tree at every AC level, looking up the per-symbol axiom
	 entry itself. */
      f = 0;
      ax = NULL;
      if (!term_contains_ac(alpha)) {
	if (dbg)
	  fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d "
		  "declined (alpha contains no AC symbol; nothing to bridge)\n",
		  (int) from->id, (int) into->id, alt_index);
	unify_bt_cancel(bt);
	free_context(from_subst);
	free_context(into_subst);
	continue;
      }
    }
    else {
      f = SYMNUM(alpha);
      ax = find_entry(axioms, f);

      if (ax == NULL || !ax->usable) {
	/* A non-right-associated matched_node is NOT a reason to decline
	   any more -- do_right_associate_at() below re-brackets it with
	   real phantom steps (into may be an ac_extension clause, whose
	   LHS is built left-nested). */
	if (dbg)
	  fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d "
		  "declined (no usable comm/assoc axiom for this symbol)\n",
		  (int) from->id, (int) into->id, alt_index);
	unify_bt_cancel(bt);
	free_context(from_subst);
	free_context(into_subst);
	continue;
      }
    }

    {
      struct bridge_ctx bctx;
      Term alpha_flat[MAX_AC_GROUPS];
      int nalpha = 0, i;
      Term *groups[MAX_AC_GROUPS];
      static Term group_storage[MAX_AC_GROUPS][MAX_ACM_ARGS];
      int group_sizes[MAX_AC_GROUPS];
      /* Always set for real by the `if (!deep_mode)` block below before
         its only reads (each gated by deep_mode==false at that point,
         which -- since deep_mode only ever transitions false->true, at
         "force deep path below" further down, never back -- can only be
         reached via a path that already ran this block). That two-
         sequential-if invariant is real but easy to break with a future
         edit and not provable by every compiler's dataflow analysis (an
         older gcc flagged this as "may be used uninitialized"); the 0
         here is a defensive floor, not a behavior change on any
         currently reachable path. */
      int ngroups = 0;
      Ilist litnum_and_pos = into_tree_pos;
      int litnum = litnum_and_pos->i;
      Topform bridge_into = into;

      if (!deep_mode) {
	flatten(alpha, alpha_flat, &nalpha);
	ngroups = nalpha;
	for (i = 0; i < nalpha; i++) {
	  Term bound = apply(alpha_flat[i], from_subst);
	  int gs = 0;
	  if (COMPLEX(bound) && SYMNUM(bound) == f)
	    flatten(bound, group_storage[i], &gs);
	  else {
	    group_storage[i][0] = bound;
	    gs = 1;
	  }
	  groups[i] = group_storage[i];
	  group_sizes[i] = gs;
	}
      }

      if (deep_mode) {
	/* Deep mode has no groups_found_in_node() trigger for the
	   into-side instantiation -- ask the substitution directly.
	   Same INSTANCE_JUST construction as the shallow path below
	   (see its comments, especially the do-NOT-renumber one; the
	   same connector-variable-encoding argument applies to
	   deep_bridge()'s apply()-based comparisons verbatim). */
	if (context_binds_any(into_subst, bridge_into)) {
	  Topform into2 = instantiate_clause(bridge_into, into_subst);
	  Plist pairs = context_to_pairs(varnums_in_clause(bridge_into->literals),
					 into_subst);
	  upward_clause_links(into2);
	  inherit_attributes(bridge_into, into_subst, NULL, NULL, into2);
	  into2->justification = instance_just(bridge_into, pairs);
	  *map = alist2_insert(*map, *next_id, old_id, (*old_id_n)++);
	  into2->id = (*next_id)++;
	  new_proof = plist_prepend(new_proof, into2);
	  if (dbg)
	    fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d "
		    "instantiated into (new clause id=%d) to resolve "
		    "into-side variables (deep mode)\n",
		    (int) from->id, (int) into->id, alt_index, (int) into2->id);
	  bridge_into = into2;
	}
      }
      else if (!groups_found_in_node(matched_node, f, groups, group_sizes, ngroups)) {
	/* matched_node here is still into's own UNSUBSTITUTED term, so this
	   first check only ever succeeds for the "pure regrouping" case
	   (nothing new needed).  Whenever into's own free variables must be
	   bound to satisfy alpha, commit to a real, kept INSTANCE_JUST step
	   (into's own variables get bound throughout the WHOLE clause, not
	   just at this position -- see the function-header comment for why
	   that matters) and check the ACTUAL result once, below. */
	{
	  Topform into2 = instantiate_clause(bridge_into, into_subst);
	  Plist pairs = context_to_pairs(varnums_in_clause(bridge_into->literals),
					 into_subst);
	  upward_clause_links(into2);
	  /* Do NOT renumber here.  groups[] (built above from alpha via
	     apply(_, from_subst)) and into2's own variables (built via
	     apply_lit(_, into_subst)) both go through the SAME apply()
	     multiplier*MAX_VARS+VARNUM encoding -- a "connector" variable
	     shared between from_subst and into_subst (e.g. ac->c3 of the
	     unify_ac call that produced this candidate -- see unify_ac()'s
	     own comment on ac->c3 in btu.c) is therefore encoded IDENTICALLY
	     in both, and groups_found_in_node() below can term_ident-match
	     them directly.  Renumbering into2 here, before that check,
	     reassigns fresh canonical numbers to into2's variables ONLY,
	     breaking the correspondence with groups[]'s still-unrenumbered
	     copy of the same connector -- even an exact, textbook-perfect
	     unifier would then get declined as a "genuine mismatch," not
	     because of a real structural gap.  Renumbering is still
	     necessary before para_pos()'s own unify() call (that IS the
	     actual segfault trigger), so it now happens once, at the very
	     end, on the fully bridged clause -- see the renumber_variables()
	     call right before the para_pos() call below. */
	  inherit_attributes(bridge_into, into_subst, NULL, NULL, into2);
	  into2->justification = instance_just(bridge_into, pairs);
	  *map = alist2_insert(*map, *next_id, old_id, (*old_id_n)++);
	  into2->id = (*next_id)++;
	  new_proof = plist_prepend(new_proof, into2);
	  if (dbg)
	    fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d "
		    "instantiated into (new clause id=%d) to resolve "
		    "into-side variables\n",
		    (int) from->id, (int) into->id, alt_index, (int) into2->id);
	  bridge_into = into2;
	  matched_node = term_at_pos(ith_literal(bridge_into->literals, litnum)->atom,
				     litnum_and_pos->next);

	  /* Substituting a free variable can bind it to a value that is
	     itself AC-headed, landing an f-headed term in a LEFT position
	     -- e.g. into's own original shape at this position might have
	     been f(w, ...) with w a bare variable (trivially right-
	     associated, since a variable is never f-headed), but once w is
	     bound to, say, f(a,b), the position becomes f(f(a,b), ...),
	     violating do_bridge_to_groups's depth-based navigation
	     invariant even though the flat multiset is unchanged.  This is
	     always safe to fix by re-canonicalizing in place: ac_canonical()
	     only re-brackets/re-sorts an AC subterm (same multiset, "the top
	     node itself is not changed" per its own doc), so groups_found_
	     in_node()'s by-value multiset check below is unaffected, and
	     do_bridge_to_groups always re-flattens its input fresh rather
	     than trusting a stale position, so a re-bracketed starting shape
	     is exactly as usable as one that happened to start canonical. */
	  ac_canonical(matched_node, -1);

	  /* Now check the REAL result: does into2's actual content at this
	     position (after instantiate_clause()) contain everything
	     alpha's own groups need?  do_bridge_to_groups below mutates
	     bridge_into in place based on groups[]/group_sizes[] (computed
	     from alpha, not from into) -- it must not proceed on an
	     unconfirmed assumption. */
	  if (!groups_found_in_node(matched_node, f, groups, group_sizes, ngroups)) {
	    /* term_ident multiset check failed after instantiate.  Can
	       be a genuine structural miss OR an AC-commuted / encoding
	       mismatch where the pieces are present but not bit-identical
	       to groups[] (observed: c_21726 unifiers that AC-commute
	       alpha's two summands so the equation RHS becomes complex,
	       which is exactly the residual search step).  Fall through
	       to deep_bridge on the instantiated clause rather than
	       declining -- deep_bridge reshapes via apply/match and does
	       not require groups_found_in_node's exact leaf identities. */
	    if (dbg)
	      fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d "
		      "groups_found failed after instantiate; trying "
		      "deep_bridge fallback\n",
		      (int) from->id, (int) into->id, alt_index);
	    deep_mode = TRUE;  /* force deep path below */
	    f = 0;
	    ax = NULL;
	  }

	  /* No post-instantiation right-associated check any more:
	     ac_canonical() above already re-brackets into2's chain, and
	     do_right_associate_at() below handles the pure-regrouping
	     path (where the chain belongs to `into` itself and can only
	     be re-bracketed via real steps). */
	}
      }

      bctx.current = bridge_into;
      bctx.litnum = litnum;
      bctx.base_pos = litnum_and_pos->next;
      bctx.f = f;         /* 0 in deep mode; deep_bridge sets it per AC node */
      bctx.ax = ax;
      bctx.axioms = axioms;
      bctx.next_id = next_id;
      bctx.map = map;
      bctx.old_id = old_id;
      bctx.old_id_n = old_id_n;
      bctx.new_proof = &new_proof;
      bctx.failed = FALSE;

      if (deep_mode) {
	/* Reshape the whole matched region to sigma(alpha)'s exact tree
	   at every AC level, then align repeated alpha variables so
	   para_pos()'s plain unify re-derives one consistent
	   substitution -- the same machinery the demod side uses. */
	Plist occs = NULL;
	deep_bridge(&bctx, NULL, alpha, from_subst, NULL, &occs);
	if (!bctx.failed) {
	  occs = reverse_plist(occs);
	  align_repeated_vars(&bctx, occs);
	}
	zap_occs(occs);
      }
      else {
	/* The chain at the bridging site may not be right-associated
	   (into may be an ac_extension clause, built left-nested) -- and
	   do_reorder/do_swap navigate by right-spine depth, which
	   requires it.  Zero steps when already right-associated. */
	do_right_associate_at(&bctx, NULL);

	do_bridge_to_groups(&bctx, groups, group_sizes, ngroups);

	/* do_bridge_to_groups leaves a RIGHT-associated chain of closed
	   group-slots, but para_pos()'s plain unify() walks ALPHA's own
	   bracket tree -- for a left-nested alpha (every ac_extension
	   clause: f(f(...),z)) the shapes disagree and unify fails.
	   Re-bracket to alpha's exact tree; assoc-only, zero steps when
	   alpha is already right-associated. */
	if (!bctx.failed)
	  do_rebracket_to_shape(&bctx, NULL, alpha);
      }

      /* unify_bt_cancel() before free_context() -- see try_node_para()'s
	 comment; same requirement as Phase 1's is_right_associated
	 early-continue above, just on the success/bctx.failed path. */
      unify_bt_cancel(bt);
      free_context(from_subst);
      free_context(into_subst);

      if (!bctx.failed) {
	Topform result;
	/* Deferred from the instantiate_clause() site above: renumber the
	   fully bridged clause's variables now, once, right before the only
	   call that actually needs bounded numbers (para_pos()'s own
	   unify()) -- matching para_pos()'s existing convention of
	   renumbering its own paramodulant immediately after building it. */
	renumber_variables(bctx.current, MAX_VARS);
	result = para_pos(from, from_pos, bctx.current, into_tree_pos);
	if (result != NULL &&
	    (expected == NULL || ac_result_matches_expected(result, expected))) {
	  int nsteps = 0;
	  Plist qq;
	  if (dbg)
	    for (qq = new_proof; qq; qq = qq->next) nsteps++;
	  *map = alist2_insert(*map, *next_id, old_id, (*old_id_n)++);
	  result->id = (*next_id)++;
	  new_proof = plist_prepend(new_proof, result);
	  *out_result = result;
	  /* Advance past this candidate so the caller can resume from the
	     next one if this candidate fails the caller's own end-of-chain
	     judging (see alt_start's contract in ac_expand.h). */
	  *alt_start = alt_index + 1;
	  if (dbg)
	    fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d "
		    "SUCCESS ngroups=%d bridge_steps=%d result_id=%d next_id_after=%d\n",
		    (int) from->id, (int) into->id, alt_index, ngroups, nsteps,
		    (int) result->id, *next_id);
	  if (dbg && getenv("PC_DEBUG_TRACE2") != NULL) {
	    fprintf(stderr, "AC_PARA_STAT: result clause: ");
	    fprint_clause(stderr, result);
	  }
	  /* new_proof is currently [result, ...bridge steps..., into2] (built
	     by prepending in CHRONOLOGICAL order: into2 first, result last,
	     so result -- the most recently created -- sits at the head).
	     The caller's own splice loop ("for (q = ac_steps; ...) new_proof
	     = plist_prepend(new_proof, q->v);") walks this HEAD-TO-TAIL and
	     prepends each element into the OUTER proof in that same order --
	     which means result gets prepended into the outer list BEFORE
	     into2, so after the ONE global reverse_plist() at the very end
	     of expand_proof(), result (a CHILD, citing into2 as a parent)
	     would print BEFORE into2 -- violating the "parents before
	     children" invariant check_parents_and_uplinks_in_proof() enforces
	     strictly (confirmed directly: this crashed exactly that way on
	     first implementation).  Reversing here before returning fixes
	     it: the caller's splice then walks [into2, ...,result] instead,
	     so into2 gets prepended first among this group, landing before
	     result once everything is reversed together at the very end. */
	  return reverse_plist(new_proof);
	}
	if (dbg) {
	  if (result == NULL)
	    fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d "
		    "bridged ok but final para_pos still returned NULL\n",
		    (int) from->id, (int) into->id, alt_index);
	  else
	    fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d "
		    "declined (bridged and replayed fine, but this candidate's "
		    "result doesn't match the recorded clause -- AC unification "
		    "is multi-valued, so a different, equally valid unifier can "
		    "reconstruct a different clause; trying the next alt_index)\n",
		    (int) from->id, (int) into->id, alt_index);
	}
      }
      else if (dbg)
	fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d alt_index=%d "
		"do_bridge_to_groups failed\n", (int) from->id, (int) into->id, alt_index);
      /* This candidate didn't pan out -- deliberately leak the partial
	 bridging sequence's clauses, same rationale as
	 expand_ac_demod_entry()'s own failure path: correctness over
	 memory economy in a one-shot, post-hoc proof-expansion utility. */
      new_proof = NULL;
    }
  }

  if (dbg)
    fprintf(stderr, "AC_PARA_STAT: from_id=%d into_id=%d TOTAL FAILURE (all alt_index exhausted)\n",
	    (int) from->id, (int) into->id);
  *out_result = NULL;
  return NULL;
}  /* expand_ac_para_entry */

/*************
 *
 *   In-process AC demod-chain explorer (lookahead + bounded DFS).
 *
 *   expand_proof's chain odometer only checks the END of a multi-demod
 *   compound citation against the recorded clause; intermediate clauses
 *   were never stored, and a wrong early alt can still let later demods
 *   "succeed" at the wrong redex.  Long back-demod chains therefore
 *   burn the attempt budget advancing choice point 0 while choice
 *   point 1 never matches any of those outputs.
 *
 *   explore_ac_demod_chain() searches intermediate clause states
 *   explicitly, with one-step lookahead pruning, and returns a plan the
 *   ordinary expand path can replay.  No subprocess / no search.c
 *   reentry -- only the same expand_ac_demod_entry / particular_demod
 *   primitives the live expand path already uses.
 *
 *************/

#define AC_CHAIN_MAX_ALTS    64
#define AC_CHAIN_MAX_LEN     32
#define AC_CHAIN_MAX_STATES  8192
#define AC_PLAIN_POS_SCAN    256  /* max sequence numbers to try for plain */

/* PUBLIC
   Try particular_demod at the recorded position first, then scan other
   sequence numbers.  Under AC reshaping earlier in a compound chain the
   recorded position is advisory (demod.c); a non-AC-headed demod like
   n(n(n(x)))=n(x) has no AC rediscovery path, so scanning is the only
   way to rediscover its redex.  Mutates `c` on success. */
BOOL particular_demod_scan(Topform c, Topform demod, int preferred_pos,
			   int direction, Ilist *from_pos, Ilist *ipos)
{
  int t;
  if (preferred_pos > 0 &&
      particular_demod(c, demod, preferred_pos, direction, from_pos, ipos))
    return TRUE;
  for (t = 1; t <= AC_PLAIN_POS_SCAN; t++) {
    if (t == preferred_pos)
      continue;
    if (particular_demod(c, demod, t, direction, from_pos, ipos))
      return TRUE;
  }
  return FALSE;
}  /* particular_demod_scan */

/* PUBLIC */
BOOL ac_demod_step_viable(Topform work, Topform demod, int direction,
			  int position)
{
  Term pattern;
  Ilist from_pos, into_pos;
  Topform copy;
  Ilist tree_pos;
  Context subst;
  Term matched_node;
  Btm_state bt;

  if (work == NULL || demod == NULL || demod->literals == NULL ||
      !eq_term(demod->literals->atom))
    return FALSE;

  pattern = ARG(demod->literals->atom, direction == 1 ? 0 : 1);

  /* Plain positional replay (non-AC-headed demodulators only -- same
     dispatch gate expand_proof uses), scanning sequence numbers because
     AC reshaping earlier in the chain invalidates the recorded one. */
  if (!is_assoc_comm(SYMNUM(ARG(demod->literals->atom, 0)))) {
    copy = copy_clause(work);
    if (particular_demod_scan(copy, demod, position, direction,
			      &from_pos, &into_pos)) {
      zap_ilist(from_pos);
      zap_ilist(into_pos);
      return TRUE;
    }
  }

  if (!term_contains_ac(pattern))
    return FALSE;

  /* Any AC rediscovery hit is enough for viability. */
  if (find_ac_demod_candidate(work, demod, direction, 0,
			      &tree_pos, &subst, &matched_node, &bt)) {
    match_bt_cancel(bt);
    free_context(subst);
    zap_ilist(tree_pos);
    return TRUE;
  }
  return FALSE;
}  /* ac_demod_step_viable */

/* Apply one demod citation to `work` at a planned alt.
   Plan encoding (shared with expand_proof's chain_plan):
     -1        = plain particular_demod at the recorded position only
     -2 - pos  = plain particular_demod at sequence number `pos`
                 (pos >= 1), used when the explorer finds a redex at a
                 non-recorded sequence after AC reshaping
     >= 0      = AC alt_start for expand_ac_demod_entry
   Returns the rewritten clause (a new Topform), or NULL.  Does not
   mutate `work`. */
static
Topform ac_demod_apply_planned(Topform work, Topform demod, int direction,
			       int position, int planned_alt,
			       Ac_axiom_set axioms)
{
  if (planned_alt < 0) {
    Topform copy;
    Ilist from_pos, into_pos;
    int pos;
    if (is_assoc_comm(SYMNUM(ARG(demod->literals->atom, 0))))
      return NULL;
    if (planned_alt == -1)
      pos = position;
    else
      pos = -2 - planned_alt;   /* planned_alt = -2-pos => pos */
    if (pos <= 0)
      return NULL;
    copy = copy_clause(work);
    if (particular_demod(copy, demod, pos, direction, &from_pos, &into_pos)) {
      zap_ilist(from_pos);
      zap_ilist(into_pos);
      return copy;
    }
    return NULL;
  }
  else {
    int next_id = 1000000;   /* throwaway -- steps are not kept */
    I3list map = NULL;
    int old_id_n = 0;
    int alt = planned_alt;
    Topform result = NULL;
    Plist steps;

    steps = expand_ac_demod_entry(work, demod, direction, axioms,
				  &next_id, &map, 0, &old_id_n,
				  &alt, &result);
    zap_i3list(map);
    /* Deliberately leak `steps` (orphan bridge clauses) -- same
       convention as expand_ac_demod_entry's own failed-candidate path.
       `result` is the clause we need; it is not in `work`. */
    (void) steps;
    return result;
  }
}  /* ac_demod_apply_planned */

struct ac_explore_ctx {
  Topform *demods;
  int *dirs;
  int *positions;
  int n;
  Topform expected;
  Ac_axiom_set axioms;
  int states;
  int max_states;
  int alts_out[AC_CHAIN_MAX_LEN];
  BOOL found;
  BOOL dbg;
};

static
BOOL ac_explore_dfs(struct ac_explore_ctx *ctx, Topform current, int depth)
{
  Topform demod;
  int dir, pos;
  Term pattern;
  BOOL try_plain;
  int a;

  if (ctx->found)
    return TRUE;
  if (ctx->states >= ctx->max_states)
    return FALSE;

  if (depth == ctx->n) {
    /* Goal check.  renumber_variables mutates; current is an orphan
       probe clause so that is fine.  Also try a flipped equality:
       many back_demod compounds end in flip(a) after the rewrite
       list, and expand_proof applies that flip as a separate
       secondary step after the demods -- the explorer must accept
       either orientation or it will reject every otherwise-correct
       demod plan (observed: residual c_22979, 15 demods + flip). */
    renumber_variables(current, MAX_VARS);
    if (ac_result_matches_expected(current, ctx->expected)) {
      ctx->found = TRUE;
      return TRUE;
    }
    if (current->literals != NULL &&
	current->literals->next == NULL &&
	eq_term(current->literals->atom)) {
      Topform flipped = copy_clause(current);
      flip_eq(flipped->literals->atom, 1);
      renumber_variables(flipped, MAX_VARS);
      if (ac_result_matches_expected(flipped, ctx->expected)) {
	ctx->found = TRUE;
	return TRUE;
      }
    }
    return FALSE;
  }

  if (depth >= AC_CHAIN_MAX_LEN)
    return FALSE;

  demod = ctx->demods[depth];
  dir = ctx->dirs[depth];
  pos = ctx->positions[depth];
  pattern = ARG(demod->literals->atom, dir == 1 ? 0 : 1);
  try_plain = !is_assoc_comm(SYMNUM(ARG(demod->literals->atom, 0)));

  /* Branch: plain particular_demod at every sequence number that
     matches.  After AC reshaping the recorded position is often
     wrong; multiple sites may also match, and only one of them lets
     the rest of the chain close -- so enumerate, do not stop at the
     first hit.  Plan values: -1 = recorded pos; -2-p = sequence p. */
  if (try_plain) {
    int p;
    for (p = 1; p <= AC_PLAIN_POS_SCAN; p++) {
      int planned = (p == pos) ? -1 : (-2 - p);
      Topform res = ac_demod_apply_planned(current, demod, dir, pos,
					   planned, ctx->axioms);
      if (res == NULL)
	continue;
      ctx->states++;
      if (depth + 1 < ctx->n &&
	  !ac_demod_step_viable(res, ctx->demods[depth + 1],
				ctx->dirs[depth + 1],
				ctx->positions[depth + 1])) {
	if (ctx->states >= ctx->max_states)
	  return FALSE;
	continue;
      }
      ctx->alts_out[depth] = planned;
      if (ac_explore_dfs(ctx, res, depth + 1))
	return TRUE;
      if (ctx->states >= ctx->max_states)
	return FALSE;
    }
  }

  /* Branch: AC rediscovery alts 0,1,2,... */
  if (term_contains_ac(pattern)) {
    for (a = 0; a < AC_CHAIN_MAX_ALTS; a++) {
      Topform res = ac_demod_apply_planned(current, demod, dir, pos, a,
					   ctx->axioms);
      if (res == NULL)
	break;   /* candidates exhausted at this citation */
      ctx->states++;
      if (depth + 1 < ctx->n &&
	  !ac_demod_step_viable(res, ctx->demods[depth + 1],
				ctx->dirs[depth + 1],
				ctx->positions[depth + 1])) {
	/* Dead branch: this alt leaves no redex for the next demod. */
	if (ctx->states >= ctx->max_states)
	  return FALSE;
	continue;
      }
      ctx->alts_out[depth] = a;
      if (ac_explore_dfs(ctx, res, depth + 1))
	return TRUE;
      if (ctx->states >= ctx->max_states)
	return FALSE;
    }
  }

  return FALSE;
}  /* ac_explore_dfs */

/* PUBLIC */
Ilist explore_ac_demod_chain(Topform start,
			     Topform *demods, int *directions, int *positions,
			     int n,
			     Topform expected,
			     Ac_axiom_set axioms)
{
  struct ac_explore_ctx ctx;
  int i;
  Ilist plan = NULL;
  BOOL dbg = (getenv("PC_DEBUG_TRACE") != NULL);

  if (start == NULL || demods == NULL || n <= 0 || expected == NULL)
    return NULL;
  if (n > AC_CHAIN_MAX_LEN)
    n = AC_CHAIN_MAX_LEN;

  ctx.demods = demods;
  ctx.dirs = directions;
  ctx.positions = positions;
  ctx.n = n;
  ctx.expected = expected;
  ctx.axioms = axioms;
  ctx.states = 0;
  ctx.max_states = AC_CHAIN_MAX_STATES;
  ctx.found = FALSE;
  ctx.dbg = dbg;

  if (dbg)
    fprintf(stderr, "AC_CHAIN_EXPLORE: start n=%d max_states=%d\n",
	    n, ctx.max_states);

  ac_explore_dfs(&ctx, start, 0);

  if (!ctx.found) {
    if (dbg)
      fprintf(stderr, "AC_CHAIN_EXPLORE: FAILED after %d states\n",
	      ctx.states);
    return NULL;
  }

  for (i = 0; i < n; i++)
    plan = ilist_append(plan, ctx.alts_out[i]);

  if (dbg) {
    fprintf(stderr, "AC_CHAIN_EXPLORE: SUCCESS after %d states, plan:",
	    ctx.states);
    for (i = 0; i < n; i++)
      fprintf(stderr, " %d", ctx.alts_out[i]);
    fprintf(stderr, "\n");
  }
  return plan;
}  /* explore_ac_demod_chain */
