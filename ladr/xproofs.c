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

#include "xproofs.h"
#include "demod.h"
#include "ac_expand.h"
#include "btu.h"    /* get/set_ac_superset_limit -- see expand_proof */
#include "dioph.h"  /* get/set_ac_walk_budget    -- see expand_proof */

/* #define DEBUG_EXPAND */

/* Private definitions and types */

/*************
 *
 *   check_parents_and_uplinks_in_proof()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void check_parents_and_uplinks_in_proof(Plist proof)
{
  Ilist seen = NULL;
  Plist p;
  for (p = proof; p; p = p->next) {
    Topform c = p->v;
    Ilist parents = get_parents(c->justification, FALSE);
    if (!check_upward_clause_links(c)) {
      printf("bad uplinks: "); fprint_clause(stdout, c);
      fatal_error("check_parents_and_uplinks_in_proof, bad uplinks");
    }
    if (!ilist_subset(parents, seen)) {
      printf("seen:    "); p_ilist(seen);
      printf("parents: "); p_ilist(parents);
      fatal_error("check_parents_and_uplinks_in_proof, parents not seen");
    }
    seen = ilist_prepend(seen, c->id);
    zap_ilist(parents);
  }
  zap_ilist(seen);
}  /* check_parents_and_uplinks_in_proof */

/*************
 *
 *   xx_res2()
 *
 *************/

static
Topform xx_res2(Topform c, int n)
{
  Literals lit = ith_literal(c->literals, n);

  if (lit == NULL ||
      lit->sign == TRUE ||
      !eq_term(lit->atom))
    return NULL;
  else {
    Context subst = get_context();
    Trail tr = NULL;
    Topform res;

    if (unify(ARG(lit->atom,0), subst, ARG(lit->atom,1), subst, &tr)) {
      Literals l2;
      res = get_topform();
      for (l2 = c->literals; l2; l2 = l2->next)
	if (l2 != lit)
	  res->literals = append_literal(res->literals, apply_lit(l2,  subst));

      res->attributes = cat_att(res->attributes,
			     inheritable_att_instances(c->attributes, subst));

      res->justification = xxres_just(c, n);
      upward_clause_links(res);
      renumber_variables(res, MAX_VARS);
      undo_subst(tr);
    }
    else {
      res = NULL;
    }
    free_context(subst);
    return res;
  }
}  /* xx_res2 */

/*************
 *
 *   xx_simp2()
 *
 *************/

static
BOOL xx_simp2(Topform c, int n)
{
  Literals lit = ith_literal(c->literals, n);
  Term a = lit->atom;

  /* Same condition as simplify_literals2's removal case (ladr/subsume.c) --
     must stay in sync, or expand_step's XX_JUST replay (below) fails to
     reconstruct a proof that used the newer distinctness-based removal
     (docs/distinctness-unification-spec.md).  This function independently
     re-verifies the removal rather than trusting the recorded
     justification, so it needs to know about the same rule. */
  if ((!lit->sign && eq_term(a) && term_ident(ARG(a,0), ARG(a,1))) ||
      (lit->sign && eq_term(a) && provably_distinct(ARG(a,0), ARG(a,1))) ||
      eq_removable_literal(c, lit)) {
    zap_term(lit->atom);
    lit->atom = NULL;
    c->literals = remove_null_literals(c->literals);
    c->justification = append_just(c->justification, xx_just(n));
    return TRUE;
  }
  else {
    fprintf(stderr, "xx_simp2: literal %d in clause cannot be removed: ", n);
    fprint_clause(stderr, c);
    return FALSE;
  }
}  /* xx_simp2 */

/*************
 *
 *   factor()
 *
 *************/

static
Topform factor(Topform c, int n1, int n2)
{
  Topform fac;
  Literals l1 = ith_literal(c->literals, n1);
  Literals l2 = ith_literal(c->literals, n2);
  Context subst = get_context();

  Trail tr = NULL;

  if (l1->sign == l2->sign && unify(l1->atom, subst, l2->atom, subst, &tr)) {
    Literals lit;
    fac = get_topform();
    for (lit = c->literals; lit; lit = lit->next)
      if (lit != l2)
	fac->literals = append_literal(fac->literals, apply_lit(lit,  subst));

    fac->attributes = cat_att(fac->attributes,
			      inheritable_att_instances(c->attributes, subst));

    fac->justification = factor_just(c, n1, n2);
    upward_clause_links(fac);
    renumber_variables(fac, MAX_VARS);
    undo_subst(tr);
  }
  else
    fac = NULL;
  free_context(subst);
  return fac;
}  /* factor */

/*************
 *
 *   merge1()
 *
 *************/

static
BOOL merge1(Topform c, int n)
{
  Literals target = ith_literal(c->literals, n);
  Literals prev = ith_literal(c->literals, n-1);
  Literals lit = c->literals;
  BOOL go = TRUE;

  while (go) {
    if (lit->sign == target->sign && term_ident(lit->atom, target->atom))
      go = FALSE;
    else
      lit = lit->next;
  }
  if (lit == target) {
    fprintf(stderr, "merge1, literal does not merge\n");
    return FALSE;
  }
  prev->next = target->next;
  zap_literal(target);
  c->justification = append_just(c->justification, merge_just(n));
  return TRUE;
}  /* merge1 */

/*************
 *
 *   proof_id_to_clause()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Topform proof_id_to_clause(Plist proof, int id)
{
  Plist p = proof;
  while (p && ((Topform) p->v)->id != id)
    p = p->next;
  if (p == NULL)
    return NULL;
  else
    return p->v;
}  /* proof_id_to_clause */

/*************
 *
 *   greatest_id_in_proof()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int greatest_id_in_proof(Plist proof)
{
  int max_id = 0;
  Plist p;
  for (p = proof; p; p = p->next) {
    Topform c = p->v;
    /* Only consider IDs that fit in int (original proof IDs).
       Expansion IDs from overflowed unsigned long long are skipped. */
    if (c->id <= INT_MAX && (int)c->id > max_id)
      max_id = (int)c->id;
  }
  return max_id;
}  /* greatest_id_in_proof */

/*************
 *
 *   expand_proof()
 *
 *************/

/* DOCUMENTATION
Given a proof, return a more detailed proof, entirely new, leaving the
given proof unchanged.  Also returned is an I3list mapping new IDs to
pairs <old_id, n>.  The n compnent identifies the sub-steps arising
from the expansions, e.g.,  66 -> <23,4> means that step 66 in the new
proof corresponds to the 4th substep in expanding step 23 of the old proof.

Clauses in the new proof that match clauses in the old proof retain
the IDs from the old proof, and there is no entry in the map for them.

If a replay operation fails or a replayed step does not reproduce the
recorded clause, NULL is returned (with *pmap set to NULL) and a
diagnostic goes to stderr; callers should fall back to the given proof.
*/

/* Whether j (assumed j->type == PARA_JUST) needs the AC-aware replay
   path -- either side (from's rewriting term, or into's target
   subterm) is headed by an AC-declared symbol.  Used both by the "no
   expansion necessary" shortcut below (which must NOT take a bare
   PARA_JUST step's fast path when this is true: para_pos()'s own plain
   unify() can't replay it, so there is genuine bridging work to do even
   though there is nothing to "unroll" -- a paramod step is already
   atomic) and by the main PARA_JUST dispatch itself. */
static
BOOL para_just_needs_ac(Plist proof, Just j)
{
  Topform from = proof_id_to_clause(proof, j->u.para->from_id);
  Topform into = proof_id_to_clause(proof, j->u.para->into_id);
  Ilist from_pos = j->u.para->from_pos;
  Ilist into_pos = j->u.para->into_pos;
  Literals from_lit = ith_literal(from->literals, from_pos->i);
  int from_side = (from_pos->next->i == 1 ? 0 : 1);
  Term alpha = ARG(from_lit->atom, from_side);
  Literals into_lit = ith_literal(into->literals, into_pos->i);
  Term into_term = term_at_pos(into_lit->atom, into_pos->next);
  BOOL from_ac = !VARIABLE(alpha) && is_assoc_comm(SYMNUM(alpha));
  BOOL into_ac = (into_term != NULL && !VARIABLE(into_term) &&
		  is_assoc_comm(SYMNUM(into_term)));
  return from_ac || into_ac;
}  /* para_just_needs_ac */

/* Whether a FAILED plain replay of this PARA_JUST step is worth
   promoting to the AC-aware path: either side contains an AC symbol
   ANYWHERE -- not just at its head, which is all para_just_needs_ac()
   tests.  An n-headed alpha with '+' inside can make plain unify()
   pick a different unifier than the search's AC one (the replay
   "succeeds" but reproduces the wrong clause) or fail outright -- real
   w70 cases old 9, 24 and 18586 respectively. */
static
BOOL para_just_worth_ac_retry(Plist proof, Just j)
{
  Topform from = proof_id_to_clause(proof, j->u.para->from_id);
  Topform into = proof_id_to_clause(proof, j->u.para->into_id);
  Ilist from_pos = j->u.para->from_pos;
  Ilist into_pos = j->u.para->into_pos;
  Literals from_lit = ith_literal(from->literals, from_pos->i);
  int from_side = (from_pos->next->i == 1 ? 0 : 1);
  Term alpha = ARG(from_lit->atom, from_side);
  Literals into_lit = ith_literal(into->literals, into_pos->i);
  Term into_term = term_at_pos(into_lit->atom, into_pos->next);
  return term_contains_ac(alpha) ||
	 (into_term != NULL && term_contains_ac(into_term));
}  /* para_just_worth_ac_retry */

/* --- chain odometer (see maybe_ac_para_retry in expand_proof) ---

   Demod rediscovery is position-multi-valued: a citation can replay
   mechanically at the WRONG subterm, and the whole compound chain then
   lands on a different clause than recorded -- with no way to tell
   until the end (intermediates aren't recorded).  Each AC/deep demod
   citation in a chain is therefore a CHOICE POINT.  During an attempt,
   chain_used records one entry per choice point, in encounter order:
   -1  = the plain path replayed this citation
   a>=0 = the deep path replayed it, and `a` is the advanced resume
	  point (used candidate + skipped ones; passing a-1 replays the
	  same candidate, passing a takes the next).
   On a final mismatch (or a citation exhausting during a retry), a new
   PLAN is built: replay positions before the advance point unchanged,
   advance that one position, and leave everything after it fresh
   (plan defaults to -1 beyond its length). */

static
int chain_nth_or(Ilist p, int n, int dflt)
{
  while (n-- > 0 && p != NULL)
    p = p->next;
  return p != NULL ? p->i : dflt;
}  /* chain_nth_or */

static
Ilist build_chain_plan(Ilist used, int adv_pos)
{
  Ilist plan = NULL;
  Ilist p;
  int i;
  for (p = used, i = 0; p != NULL && i <= adv_pos; p = p->next, i++) {
    int v;
    if (i < adv_pos) {
      /* Replay the same choice.  AC alts are stored post-increment
	 (expand_ac_demod_entry advances alt_start), so subtract one.
	 Plain encodings are negative (-1 recorded, or -2-pos from the
	 explorer) and are stored as-is -- do not decrement. */
      v = (p->i < 0) ? p->i : p->i - 1;
    }
    else {
      /* Advance this choice: plain -1 promotes into AC alt 0; other
	 plain encodings step to the next sequence number; AC alts
	 keep the stored resume point (already past the last try). */
      if (p->i == -1)
	v = 0;
      else if (p->i < -1)
	v = p->i - 1;   /* -2-pos -> next pos */
      else
	v = p->i;
    }
    plan = ilist_append(plan, v);
  }
  return plan;
}  /* build_chain_plan */

/* PUBLIC */
Plist expand_proof(Plist proof, I3list *pmap)
{
  Plist new_proof = NULL; /* build it backward, reverse at end */
  I3list map = NULL;     /* map new IDs to <old-id,n> for intermediate steps */
  int old_id, old_id_n;  /* for mapping new steps to old */
  int next_id;
  Plist p;
  Ac_axiom_set Ac_axioms;  /* genuine comm/assoc input axioms, per AC symbol */
  BOOL dbg = (getenv("PC_DEBUG_TRACE") != NULL);
  int stat_para_total = 0, stat_para_ac = 0;
  int save_ss_limit = get_ac_superset_limit();
  int save_walk_combos, save_walk_seconds;

  /* Post-hoc expansion needs COMPLETE, un-truncated AC unification: the
     search may run superset-restricted (ac_superset_limit >= 0 uses the
     INCOMPLETE next_combo_ss enumerator, capped at MAX_COMBOS) and
     walk-budgeted (abandonments) -- fine mid-search, but at replay time
     those truncations cut candidate streams at a DIFFERENT point than
     they cut the search's own (the renumbered/instantiated replay terms
     order the dioph basis differently), so a recorded step's unifier
     can fall in our truncated tail and become unreachable.  Lift the
     limits here; restore before returning (the caller may keep
     searching for more proofs). */
  get_ac_walk_budget(&save_walk_combos, &save_walk_seconds);
  set_ac_superset_limit(-1);
  set_ac_walk_budget(-1, -1);

  /* Start numbering the new proof where the old one ends. */

  next_id = greatest_id_in_proof(proof) + 1;
  Ac_axioms = build_ac_axiom_set(proof, &next_id);

  /* Prepend FIRST, before the main loop, so these end up FIRST once
     new_proof is reversed at the very end -- they must be positioned
     before anything that might cite them as a parent (any AC bridging
     step built during the main loop below), or check_parents_and_
     uplinks_in_proof()'s strict "parents already seen" walk fatals.
     (Confirmed: this was latent since Phase 1 -- doing this prepend
     AFTER the main loop instead put these clauses LAST, which only
     happened to go unnoticed because Phase 1's real validation run
     rarely exercised a bridging step that actually cited one of these
     as a parent; Phase 2's into-side instantiation hits it routinely.) */
  {
    Plist ac_clauses = ac_axiom_set_clauses(Ac_axioms);
    Plist q;
    for (q = ac_clauses; q; q = q->next)
      new_proof = plist_prepend(new_proof, q->v);
    zap_plist(ac_clauses);
  }

  for (p = proof; p; p = p->next) {
    Topform c = p->v;         /* the clause we're expanding */
    Topform current = NULL;   /* by substeps, this becomes identical to c */
    BOOL ac_para_verified = FALSE;  /* see the final identity check below */
    int ac_alt_start = 0;     /* AC PARA_JUST candidate resume point --
				 advanced past each returned candidate so
				 maybe_ac_para_retry below can ask for the
				 next one (see ac_expand.h) */
    BOOL force_ac_para = FALSE;  /* set when a PLAIN para replay failed
				    (or reproduced the wrong clause) and
				    either side contains an AC symbol
				    anywhere: retry via the AC path --
				    see para_just_worth_ac_retry() */
    Ilist chain_plan = NULL;   /* demod-citation choice plan for THIS
				  attempt; NULL = first attempt (every
				  position defaults to -1 = plain first).
				  See the chain-odometer comment above. */
    Ilist chain_used = NULL;   /* what each choice point actually did
				  this attempt, in encounter order */
    int chain_k = 0;           /* choice points encountered so far */
    int chain_k_failed = -1;   /* position that exhausted mid-chain, or -1 */
    int chain_attempts = 0;    /* total retries, capped */
    BOOL chain_explored = FALSE; /* TRUE once explore_ac_demod_chain ran
				    for the current primary candidate */
    Topform chain_start = NULL;  /* working clause after primary, before
				    secondary demods -- explorer input */
    Just j;
    Plist new_proof_before = new_proof;  /* per-clause fallback snapshot */
    I3list map_before = map;
    int next_id_before = next_id;
    BOOL res_has_flip = FALSE;

    j = c->justification;
    old_id = c->id;
    old_id_n = 0;  /* this counts substeps of the expansion */

    if (dbg)
      fprintf(stderr, "TRACE_CLAUSE: old_id=%d next_id_before=%d\n", old_id, next_id_before);

    if (j->type == PARA_JUST) {
      stat_para_total++;
      if (para_just_needs_ac(proof, j))
	stat_para_ac++;
    }

#ifdef DEBUG_EXPAND
    printf("\nexpanding: "); fprint_clause(stdout, c);
#endif

    /* Detect flip in a binary-res lst (negative sat_lit anywhere in the
       triples).  When present, we want to expand so a separate flip
       step is inserted before the resolve -- cleaner for the rider. */
    if (j->type == BINARY_RES_JUST) {
      Ilist q = j->u.lst;
      if (q) q = q->next;  /* skip nucleus id */
      while (q && q->next && q->next->next) {
	if (q->next->next->i < 0) { res_has_flip = TRUE; break; }
	q = q->next->next->next;
      }
    }

   retry_this_clause:  /* AC PARA_JUST candidate retry re-enters here with
			  j/old_id_n/current freshly reset and new_proof/map/
			  next_id rolled back -- see maybe_ac_para_retry. */

    if (j->next == NULL &&
	j->type != HYPER_RES_JUST &&
	j->type != UR_RES_JUST &&
	!(j->type == BINARY_RES_JUST && ilist_count(j->u.lst) > 4) &&
	!(j->type == PARA_JUST &&
	  (para_just_needs_ac(proof, j) || force_ac_para)) &&
	!res_has_flip) {

      /* No expansion is necessary for this step.
	 We take a shortcut by just copying the clause.
      */

      current = copy_clause_ija(c);
      new_proof = plist_prepend(new_proof, current);

      /* The next 2 steps get undone below.  They are performed here
	 so that the state is consistent with the cases in which
	 some expansion occurs.
       */

      map = alist2_insert(map, next_id, old_id, old_id_n++);
      current->id = next_id++;
    }
    else {
      /* To adjust literal numbers when literals disappear. */
      int merges = 0;
      int unit_deletes = 0;
      int xx_simplify = 0;
      /* primary inference */

      if (j->type == COPY_JUST ||
	  j->type == BACK_DEMOD_JUST ||
	  j->type == PROPOSITIONAL_JUST ||
	  j->type == BACK_UNIT_DEL_JUST) {
	/* Note that we get "current" directly from the new proof.
	   This prevents an unnecessary "copy" inference.
	   This assumes there is some secondary justification.
	*/
	current = proof_id_to_clause(new_proof, j->u.id);
      }
      else if (j->type == HYPER_RES_JUST ||
	       j->type == UR_RES_JUST ||
	       j->type == BINARY_RES_JUST) {
	/* c ncn ncn ncn ... (length is 3m+1) */
	Ilist p = j->u.lst;
	Topform c1 = proof_id_to_clause(proof, p->i);
	int j = 0;  /* literals resolved; subtract from nucleus position */
	p = p->next;
	while (p != NULL) {
	  Topform resolvent;
	  int n1 = p->i - j;  /* literal number in c1 */
	  int sat_id = p->next->i;
	  if (sat_id == 0)
	    resolvent = xx_resolve2(c1, n1, TRUE);
	  else {
	    Topform c2 = proof_id_to_clause(proof, sat_id);
	    int n2 = p->next->next->i;
	    /* Flip-unrolling: when sat_lit is negative, the resolve was
	       done against a flipped form of the satellite literal.
	       Insert an explicit flip step into the expanded proof so the
	       resolve uses a normal positive sat_lit -- makes the resolve
	       reading cleaner and lets the substitution rider show the
	       unifier without the flip annotation getting in the way. */
	    if (n2 < 0) {
	      int actual_lit = -n2;
	      Literals lit_to_flip = ith_literal(c2->literals, actual_lit);
	      if (lit_to_flip != NULL && lit_to_flip->atom != NULL &&
		  eq_term(lit_to_flip->atom)) {
		Topform flip_step = copy_inference(c2);
		Term atom = ith_literal(flip_step->literals,
					actual_lit)->atom;
		flip_eq(atom, actual_lit);
		map = alist2_insert(map, next_id, old_id, old_id_n++);
		flip_step->id = next_id++;
		new_proof = plist_prepend(new_proof, flip_step);
		c2 = flip_step;
		n2 = actual_lit;
	      }
	    }
	    resolvent = resolve2(c1, n1, c2, n2, TRUE);
	    if (resolvent == NULL) {
	      fprintf(stderr, "expand_step: Lit %d: ", n1);
	      fprint_clause(stderr, c1);
	      fprintf(stderr, "expand_step: Lit %d: ", n2);
	      fprint_clause(stderr, c2);
	      fprintf(stderr, "expand_step, clauses don't resolve\n");
	      goto expand_failed;
	    }
	  }
	  map = alist2_insert(map, next_id, old_id, old_id_n++);
	  resolvent->id = next_id++;
	  new_proof = plist_prepend(new_proof, resolvent);
	  c1 = resolvent;
	  j++;
	  p = p->next->next->next;
	}
	current = c1;
      }
      else if (j->type == PARA_JUST) {
	Topform from = proof_id_to_clause(proof, j->u.para->from_id);
	Topform into = proof_id_to_clause(proof, j->u.para->into_id);
	Ilist from_pos = j->u.para->from_pos;
	Ilist into_pos = j->u.para->into_pos;

	if (para_just_needs_ac(proof, j) || force_ac_para) {
	  /* AC paramodulation: ordinary unify() (para_pos()'s own, plain)
	     can't replay it -- rediscover a valid AC unifier and bridge
	     the into side into the exact shape a plain, ordinary para_pos()
	     call then finishes correctly.  See ac_expand.c.

	     When the compound justification carries a secondary rewrite
	     suffix (j->next != NULL), the recorded clause c is the END of
	     that chain, so the bare paramodulant can never equal it --
	     pass expected == NULL (accept each mechanically valid
	     candidate) and judge the end of the chain at the final check
	     below, retrying with the next candidate on a mismatch (the
	     maybe_ac_para_retry path). */
	  Plist ac_steps = expand_ac_para_entry(from, from_pos, into, into_pos,
						Ac_axioms, &next_id, &map,
						old_id, &old_id_n,
						&ac_alt_start,
						j->next == NULL ? c : NULL,
						&current);
	  Plist q;
	  if (dbg)
	    fprintf(stderr, "TRACE_AFTER_AC_PARA: old_id=%d current=%s next_id=%d\n",
		    old_id, current ? "non-NULL" : "NULL", next_id);
	  if (current == NULL)
	    goto expand_failed;   /* candidates exhausted -- no retry left */
	  /* For a bare PARA_JUST (no suffix), expand_ac_para_entry() already
	     verified current against c via ac_result_matches_expected()
	     (AC-canonical + variant, not exact identity -- see that
	     function's own header comment for why exact clause_ident() is
	     the wrong bar here).  With a suffix, current is so far only
	     mechanically valid; the final check below judges it. */
	  ac_para_verified = TRUE;
	  for (q = ac_steps; q; q = q->next)
	    new_proof = plist_prepend(new_proof, q->v);
	  if (dbg) {
	    Plist qq;
	    fprintf(stderr, "TRACE_SPLICED: old_id=%d new_proof ids:", old_id);
	    for (qq = new_proof; qq; qq = qq->next)
	      fprintf(stderr, " %d", (int) ((Topform) qq->v)->id);
	    fprintf(stderr, "\n");
	  }
	}
	else {
	  current = para_pos(from, from_pos, into, into_pos);  /* does just. */
	  if (current == NULL) {
	    if (!force_ac_para && para_just_worth_ac_retry(proof, j)) {
	      /* Plain unify failed but a side contains an AC symbol
		 somewhere -- promote to the AC-aware path and retry. */
	      if (dbg)
		fprintf(stderr, "AC_PARA_PROMOTE: old_id=%d plain para does "
			"not replay; retrying via the AC path\n", old_id);
	      force_ac_para = TRUE;
	      zap_ilist(chain_plan);
	      chain_plan = NULL;
	      zap_ilist(chain_used);
	      chain_used = NULL;
	      chain_k_failed = -1;
	      chain_k = 0;
	      chain_explored = FALSE;
	      chain_start = NULL;
	      new_proof = new_proof_before;
	      map = map_before;
	      next_id = next_id_before;
	      j = c->justification;
	      old_id_n = 0;
	      goto retry_this_clause;
	    }
	    fprintf(stderr, "expand_step, paramodulation does not replay\n");
	    goto expand_failed;
	  }
	  map = alist2_insert(map, next_id, old_id, old_id_n++);
	  current->id = next_id++;
	  new_proof = plist_prepend(new_proof, current);
	}
      }
      else if (j->type == FACTOR_JUST) {
	Ilist p = j->u.lst;
	Topform parent = proof_id_to_clause(proof, p->i);
	int lit1 = p->next->i;
	int lit2 = p->next->next->i;

	current = factor(parent, lit1, lit2);
	if (current == NULL) {
	  fprintf(stderr, "expand_step, clauses don't factor\n");
	  goto expand_failed;
	}
	map = alist2_insert(map, next_id, old_id, old_id_n++);
	current->id = next_id++;
	new_proof = plist_prepend(new_proof, current);
      }
      else if (j->type == XXRES_JUST) {
	Ilist p = j->u.lst;
	Topform parent = proof_id_to_clause(proof, p->i);
	int lit = p->next->i;

	current = xx_res2(parent, lit);
	if (current == NULL) {
	  fprintf(stderr, "expand_step, xx resolution does not replay\n");
	  goto expand_failed;
	}
	map = alist2_insert(map, next_id, old_id, old_id_n++);
	current->id = next_id++;
	new_proof = plist_prepend(new_proof, current);
      }
      else if (j->type == AC_EXT_JUST) {
	Topform parent = proof_id_to_clause(proof, j->u.id);
	current = ac_extension_of(parent);
	if (current == NULL) {
	  fprintf(stderr, "expand_step, ac_extension does not replay\n");
	  goto expand_failed;
	}
	map = alist2_insert(map, next_id, old_id, old_id_n++);
	current->id = next_id++;
	new_proof = plist_prepend(new_proof, current);
      }
      else if (j->type == NEW_SYMBOL_JUST) {
	Topform parent = proof_id_to_clause(proof, j->u.id);
	/* Assume EQ unit with right side constant. */
	int sn = SYMNUM(ARG(c->literals->atom,1));
	current = new_constant(parent, sn);
	if (current == NULL) {
	  fprintf(stderr, "expand_step, new_constant does not replay\n");
	  goto expand_failed;
	}
	map = alist2_insert(map, next_id, old_id, old_id_n++);
	current->id = next_id++;
	new_proof = plist_prepend(new_proof, current);
      }
      else {
	fprintf(stderr, "expand_step, unknown primary justification\n");
	current = copy_clause_ija(c);
	map = alist2_insert(map, next_id, old_id, old_id_n++);
	current->id = next_id++;
	new_proof = plist_prepend(new_proof, current);
      }

#ifdef DEBUG_EXPAND
      printf("primary: "); fprint_clause(stdout, current);
#endif

      /* secondary inferences */

      /* Snapshot the post-primary clause for the in-process chain
	 explorer (below).  On AC PARA retries this is re-set each
	 attempt to the new paramodulant. */
      chain_start = current;

      /* In-process demod-chain explorer: for multi-citation rewrite
	 chains that involve AC, search intermediate states up front
	 (with one-step lookahead) and install a plan the odometer
	 path below will simply replay.  Pure in-process -- no
	 subprocess.  Re-runs when the primary candidate changes
	 (chain_explored cleared on para retry). */
      if (!chain_explored && current != NULL && j != NULL) {
	Just sj;
	for (sj = j->next; sj; sj = sj->next) {
	  if (sj->type == DEMOD_JUST) {
	    I3list dp;
	    int nd = 0;
	    BOOL needs_ac = FALSE;
	    Topform demods_arr[32];
	    int dirs_arr[32];
	    int poss_arr[32];
	    for (dp = sj->u.demod; dp && nd < 32; dp = dp->next) {
	      Topform d = proof_id_to_clause(proof, dp->i);
	      Term pat;
	      if (d == NULL || d->literals == NULL) continue;
	      demods_arr[nd] = d;
	      dirs_arr[nd] = dp->k;
	      poss_arr[nd] = dp->j;
	      pat = ARG(d->literals->atom, dp->k == 1 ? 0 : 1);
	      if (is_assoc_comm(SYMNUM(ARG(d->literals->atom, 0))) ||
		  term_contains_ac(pat))
		needs_ac = TRUE;
	      nd++;
	    }
	    if (nd >= 2 && needs_ac) {
	      Ilist ep = explore_ac_demod_chain(current, demods_arr,
					       dirs_arr, poss_arr, nd,
					       c, Ac_axioms);
	      chain_explored = TRUE;
	      if (ep != NULL) {
		zap_ilist(chain_plan);
		chain_plan = ep;
		if (dbg)
		  fprintf(stderr, "AC_CHAIN_EXPLORE: old_id=%d installed "
			  "plan (%d demods)\n", old_id, nd);
	      }
	      else if (dbg)
		fprintf(stderr, "AC_CHAIN_EXPLORE: old_id=%d no plan; "
			"falling through to odometer\n", old_id);
	    }
	    break;  /* at most one DEMOD_JUST secondary block */
	  }
	}
      }

      for (j = j->next; j; j = j->next) {
	if (j->type == DEMOD_JUST) {
	  /* list of triples: <ID, position, direction> */
	  I3list p;
	  for (p = j->u.demod; p; p = p->next) {
	    Topform demod = proof_id_to_clause(proof, p->i);
	    int position = p->j;
	    int direction = p->k;
	    Ilist from_pos, into_pos;

	    if (is_assoc_comm(SYMNUM(ARG(demod->literals->atom, 0)))) {
	      /* AC demod: the recorded position is advisory (demod_bt's
		 own comment -- the term is reshaped between steps under
		 AC canonicalization), so it must be rediscovered, and the
		 single compound step must be decomposed into phantom
		 comm/assoc steps bracketing the real, now-ordinary
		 rewrite.  See ac_expand.c.  This is a chain-odometer
		 choice point: rediscovery is position-multi-valued, so
		 the plan may direct a later attempt to a different
		 candidate. */
	      Topform result;
	      int planned = chain_nth_or(chain_plan, chain_k, -1);
	      int alt = (planned == -1 ? 0 : planned);
	      Plist ac_steps = expand_ac_demod_entry(current, demod, direction,
						     Ac_axioms,
						     &next_id, &map,
						     old_id, &old_id_n,
						     &alt, &result);
	      Plist q;
	      if (result == NULL) {
		chain_k_failed = chain_k;
		goto maybe_ac_para_retry;
	      }
	      for (q = ac_steps; q; q = q->next)
		new_proof = plist_prepend(new_proof, q->v);
	      current = result;
	      chain_used = ilist_append(chain_used, alt);
	      chain_k++;
	    }
	    else {
	      /* Chain-odometer choice point: a plan value >= 0 skips the
		 plain attempt entirely and goes deep from that resume
		 point (the plain result usually appears in the deep
		 candidate stream too, so re-choosing is possible). */
	      int planned = chain_nth_or(chain_plan, chain_k, -1);
	      BOOL plain_ok = FALSE;
	      Topform work = NULL;
	      if (planned < 0) {
		/* Plain path.  plan -1 = recorded position; plan -2-p =
		   sequence number p (from the chain explorer when the
		   recorded position was stale after AC reshaping). */
		int plain_pos = (planned == -1) ? position : (-2 - planned);
		work = copy_clause(current);
		map = alist2_insert(map, next_id, old_id, old_id_n++);
		work->id = next_id++;
		if (plain_pos > 0)
		  plain_ok = particular_demod(work, demod, plain_pos,
					      direction,
					      &from_pos, &into_pos);
		if (!plain_ok && planned == -1) {
		  /* Explorer did not pin a position: scan. */
		  plain_ok = particular_demod_scan(work, demod, position,
						   direction,
						   &from_pos, &into_pos);
		}
		if (!plain_ok) {
		  /* Undo `work`'s bookkeeping (never spliced; the clause
		     itself is leaked, matching the failure-path
		     convention). */
		  next_id--;
		  map = alist2_remove(map, next_id);
		  old_id_n--;
		}
	      }
	      if (plain_ok) {
		work->justification = para_just(PARA_JUST,
						demod, from_pos,
						current, into_pos);
		current = work;
		new_proof = plist_prepend(new_proof, current);
		chain_used = ilist_append(chain_used, planned < 0 ? planned : -1);
		chain_k++;
	      }
	      else {
		/* Plain replay failed at the recorded (advisory)
		   position, or the plan says to re-choose.  If the
		   demodulator's pattern contains an AC symbol ANYWHERE --
		   not just at its head (the dispatch above tests only the
		   head) -- the deep-bridging AC path can rediscover the
		   match and reshape the subject so an ordinary rewrite
		   finishes it. */
		Topform result;
		Plist ac_steps, q;
		int alt = (planned < 0 ? 0 : planned);
		ac_steps = expand_ac_demod_entry(current, demod, direction,
						 Ac_axioms, &next_id, &map,
						 old_id, &old_id_n,
						 &alt, &result);
		if (result == NULL) {
		  chain_k_failed = chain_k;
		  goto maybe_ac_para_retry;
		}
		for (q = ac_steps; q; q = q->next)
		  new_proof = plist_prepend(new_proof, q->v);
		current = result;
		chain_used = ilist_append(chain_used, alt);
		chain_k++;
	      }
	    }
	    /* One-step lookahead: if another demod follows and cannot
	       apply to the clause we just produced, this choice is a
	       dead end -- fail this choice point now instead of
	       burning the rest of the chain and the end-check. */
	    if (p->next != NULL) {
	      Topform next_d = proof_id_to_clause(proof, p->next->i);
	      if (next_d != NULL &&
		  !ac_demod_step_viable(current, next_d, p->next->k,
					p->next->j)) {
		if (dbg)
		  fprintf(stderr, "AC_CHAIN_LOOKAHEAD: old_id=%d choice %d "
			  "kills next demod %d\n",
			  old_id, chain_k - 1, p->next->i);
		chain_k_failed = chain_k - 1;
		goto maybe_ac_para_retry;
	      }
	    }
#ifdef DEBUG_EXPAND
	    printf("demod: "); fprint_clause(stdout, current);
#endif
	  }
	}
	else if (j->type == FLIP_JUST) {
	  Term atom;
	  int n = j->u.id;
	  Topform work = copy_inference(current);
	  current = work;
	  map = alist2_insert(map, next_id, old_id, old_id_n++);
	  current->id = next_id++;
	  atom = ith_literal(current->literals, n)->atom;
	  if (!eq_term(atom)) {
	    fprintf(stderr, "expand_step, cannot flip nonequality\n");
	    goto maybe_ac_para_retry;
	  }
	  flip_eq(atom, n);  /* updates justification */
	  new_proof = plist_prepend(new_proof, current);
#ifdef DEBUG_EXPAND
	  printf("flip: "); fprint_clause(stdout, current);
#endif
	}
	else if (j->type == MERGE_JUST) {
	  int n = j->u.id - merges;
	  Topform work = copy_inference(current);
	  current = work;
	  map = alist2_insert(map, next_id, old_id, old_id_n++);
	  current->id = next_id++;
	  if (!merge1(current, n))  /* updates justification */
	    goto maybe_ac_para_retry;
	  new_proof = plist_prepend(new_proof, current);
#ifdef DEBUG_EXPAND
	  printf("merge: "); fprint_clause(stdout, current);
#endif
	  merges++;
	}
	else if (j->type == UNIT_DEL_JUST) {
	  Ilist p = j->u.lst;
	  /* p->i's sign is a flip flag (resolve2()'s own contract: n2 < 0
	     means "literal abs(n2), flipped" -- see unit_del_just(d, -i)
	     in subsume.c), not part of its magnitude.  unit_deletes only
	     ever adjusts for previously-removed literals shifting the
	     count down, so it must be subtracted from the MAGNITUDE, with
	     the sign then reapplied -- subtracting it from the raw
	     (possibly negative) p->i corrupts both when unit_deletes > 0
	     and p->i < 0 (e.g. p->i=-2, unit_deletes=1 gave n=-3: looked
	     up a nonexistent 3rd literal and crashed on a NULL atom,
	     instead of the intended flipped literal 1). */
	  int n = (p->i < 0 ? -1 : 1) * (abs(p->i) - unit_deletes);
	  Topform unit = proof_id_to_clause(proof, p->next->i);
	  Topform work = resolve2(unit, 1,current, n, TRUE);
	  if (work == NULL) {
	    fprintf(stderr, "expand_step: Lit %d: ", n);
	    fprint_clause(stderr, current);
	    fprintf(stderr, "expand_step: Lit %d: ", 1);
	    fprint_clause(stderr, unit);
	    fprintf(stderr, "expand_step, clauses don't unit_del\n");
	    goto maybe_ac_para_retry;
	  }
	  current = work;
	  map = alist2_insert(map, next_id, old_id, old_id_n++);
	  current->id = next_id++;
	  new_proof = plist_prepend(new_proof, current);
	  unit_deletes++;
#ifdef DEBUG_EXPAND
	  printf("unit_del: "); fprint_clause(stdout, current);
#endif
	}
	else if (j->type == XX_JUST) {
	  int n = j->u.id - xx_simplify;
	  Topform work = copy_inference(current);
	  current = work;
	  map = alist2_insert(map, next_id, old_id, old_id_n++);
	  current->id = next_id++;
	  if (!xx_simp2(current,n))
	    goto maybe_ac_para_retry;
	  new_proof = plist_prepend(new_proof, current);
	  xx_simplify++;
#ifdef DEBUG_EXPAND
	  printf("xx_simplify: "); fprint_clause(stdout, current);
#endif
	}
	else {
	  fprintf(stderr, "expand_step, unknown secondary justification\n");
	  new_proof = plist_prepend(new_proof, current);
	}
      }

      renumber_variables(current, MAX_VARS);

#ifdef DEBUG_EXPAND
      printf("secondary: "); fprint_clause(stdout, current);
#endif

      }

    /* Okay.  Now current should be identical to c. */

    if (current == c) {
      fprintf(stderr, "expand_proof, current == c\n");
      goto expand_failed;
    }
    else if ((ac_para_verified || chain_used != NULL)
	     ? !ac_result_matches_expected(current, c)
	     : !clause_ident(current->literals, c->literals)) {
      /* The AC-variant comparison applies to ANY chain that went through
	 the AC-aware choice-point machinery (an AC para candidate, or
	 any demod citation -- chain_used non-NULL), not just AC para:
	 a rediscovered demod rewrite at a different-but-valid position
	 yields an AC-variant of the recorded clause (different
	 arrangement, hence different renumbering), which is logically
	 the same clause and exactly as valid a replacement -- and every
	 downstream step of the EXPANDED proof is re-derived from our
	 replacement, so the printed proof stays internally consistent. */
      if (ac_para_verified ||
	  chain_used != NULL ||
	  (!force_ac_para && c->justification->type == PARA_JUST &&
	   para_just_worth_ac_retry(proof, c->justification)))
	/* One of this clause's multi-valued choices may be wrong -- the
	   AC para candidate, a demod citation's rewrite position, or
	   the plain para unifier itself.  The retry dispatcher below
	   works through them in that order. */
	goto maybe_ac_para_retry;
      fprint_clause(stderr, c);
      fprint_clause(stderr, current);
      fprintf(stderr, "expand step, result is not identical\n");
      goto expand_failed;
    }
    else {
      /* Now we undo the numbering of the last substep (including
	 the cases in which no expansion is done).  This is so that
	 the clauses in the expanded proof that match the clauses
	 in the original proof have the same IDs.  That is, only
	 the clauses introduced by expansion (e.g., intermedediate
	 demodulants) get new IDs.
       */
      current->id = c->id;
      next_id--;
      map = alist2_remove(map, next_id);
      if (dbg) {
	Plist qq;
	fprintf(stderr, "TRACE_RENUMBERED: old_id=%d freed_id=%d new_proof ids:", old_id, next_id);
	for (qq = new_proof; qq; qq = qq->next)
	  fprintf(stderr, " %d", (int) ((Topform) qq->v)->id);
	fprintf(stderr, "\n");
      }
#ifdef DEBUG_EXPAND
      printf("end: "); fprint_clause(stdout, current);
#endif
    }  /* expand */
    continue;  /* success: skip the per-clause fallback below */

   maybe_ac_para_retry:
    /* Something in this clause's compound chain failed for the current
       combination of choices -- an AC para candidate, and/or a demod
       citation's rediscovered rewrite position -- or the end of the
       chain doesn't match the recorded clause.  Both kinds of choice are
       multi-valued, so retry a different combination:

       1. Chain odometer: advance the LAST demod choice point (or the
	  one before a mid-chain exhaustion), replaying every choice
	  before it and leaving everything after it fresh.  The same
	  para candidate is replayed (ac_alt_start is rewound by one).
       2. When the odometer is exhausted (or there were no demod choice
	  points): advance the AC PARA candidate (Stage-1 behavior) and
	  reset the odometer.
       3. Neither available: fall through to the compact fallback.

       Terminates: chain_attempts is capped, every para retry advances
       ac_alt_start, and para exhaustion returns current == NULL, which
       goes straight to expand_failed. */
    chain_attempts++;
    if (chain_attempts < 128 && chain_used != NULL) {
      int adv_pos = (chain_k_failed >= 0 ? chain_k_failed - 1
					 : ilist_count(chain_used) - 1);
      if (adv_pos >= 0) {
	zap_ilist(chain_plan);
	chain_plan = build_chain_plan(chain_used, adv_pos);
	zap_ilist(chain_used);
	chain_used = NULL;
	chain_k_failed = -1;
	chain_k = 0;
	/* Keep chain_explored: same primary, odometer is refining the
	   demod plan the explorer (if any) did not fully settle. */
	if (dbg)
	  fprintf(stderr, "AC_CHAIN_RETRY: old_id=%d advancing demod choice "
		  "point %d (attempt %d)\n", old_id, adv_pos, chain_attempts);
	if (ac_para_verified)
	  ac_alt_start--;  /* replay the SAME para candidate */
	new_proof = new_proof_before;
	map = map_before;
	next_id = next_id_before;
	current = NULL;
	ac_para_verified = FALSE;
	j = c->justification;
	old_id_n = 0;
	goto retry_this_clause;
      }
    }
    if (chain_attempts < 128 && ac_para_verified) {
      if (dbg)
	fprintf(stderr, "AC_PARA_RETRY: old_id=%d rolling back this "
		"candidate, resuming at alt_index=%d\n", old_id, ac_alt_start);
      zap_ilist(chain_plan);
      chain_plan = NULL;   /* fresh odometer for the next para candidate */
      zap_ilist(chain_used);
      chain_used = NULL;
      chain_k_failed = -1;
      chain_k = 0;
      chain_explored = FALSE;  /* new primary -> re-explore demods */
      chain_start = NULL;
      new_proof = new_proof_before;
      map = map_before;
      next_id = next_id_before;
      current = NULL;
      ac_para_verified = FALSE;
      j = c->justification;
      old_id_n = 0;
      goto retry_this_clause;
    }
    if (chain_attempts < 128 && !force_ac_para &&
	c->justification->type == PARA_JUST &&
	para_just_worth_ac_retry(proof, c->justification)) {
      /* The PLAIN para replay itself may have picked a different unifier
	 than the search's AC one (possible whenever a side contains an
	 AC symbol below its head) -- promote to the AC-aware path and
	 retry from scratch. */
      if (dbg)
	fprintf(stderr, "AC_PARA_PROMOTE: old_id=%d plain para replayed "
		"to a different clause; retrying via the AC path\n", old_id);
      force_ac_para = TRUE;
      zap_ilist(chain_plan);
      chain_plan = NULL;
      zap_ilist(chain_used);
      chain_used = NULL;
      chain_k_failed = -1;
      chain_k = 0;
      chain_explored = FALSE;
      chain_start = NULL;
      new_proof = new_proof_before;
      map = map_before;
      next_id = next_id_before;
      current = NULL;
      ac_para_verified = FALSE;
      j = c->justification;
      old_id_n = 0;
      goto retry_this_clause;
    }

    /* Last in-process chance: if explorer has not run yet for this
       primary (e.g. single-demod chain that still needs multi-alt
       search, or explorer was skipped), try it now from chain_start. */
    if (!chain_explored && chain_start != NULL) {
      Just sj;
      for (sj = c->justification; sj; sj = sj->next) {
	if (sj->type == DEMOD_JUST) {
	  I3list dp;
	  int nd = 0;
	  Topform demods_arr[32];
	  int dirs_arr[32];
	  int poss_arr[32];
	  for (dp = sj->u.demod; dp && nd < 32; dp = dp->next) {
	    Topform d = proof_id_to_clause(proof, dp->i);
	    if (d == NULL) continue;
	    demods_arr[nd] = d;
	    dirs_arr[nd] = dp->k;
	    poss_arr[nd] = dp->j;
	    nd++;
	  }
	  if (nd >= 1) {
	    Ilist ep = explore_ac_demod_chain(chain_start, demods_arr,
					     dirs_arr, poss_arr, nd,
					     c, Ac_axioms);
	    chain_explored = TRUE;
	    if (ep != NULL) {
	      zap_ilist(chain_plan);
	      chain_plan = ep;
	      zap_ilist(chain_used);
	      chain_used = NULL;
	      chain_k_failed = -1;
	      chain_k = 0;
	      if (ac_para_verified)
		ac_alt_start--;
	      new_proof = new_proof_before;
	      map = map_before;
	      next_id = next_id_before;
	      current = NULL;
	      ac_para_verified = FALSE;
	      j = c->justification;
	      old_id_n = 0;
	      if (dbg)
		fprintf(stderr, "AC_CHAIN_EXPLORE: old_id=%d late plan "
			"installed, retrying\n", old_id);
	      goto retry_this_clause;
	    }
	  }
	  break;
	}
      }
      chain_explored = TRUE;
    }

   expand_failed:
    /* This clause's expansion diverged from the recorded justification
       (or a replay operation failed -- most commonly an AC-mode
       PARA_JUST step, not yet expandable; see ac_expand.c).  A stderr
       diagnostic was already printed by whichever check got here.
       Per-clause fallback: discard this clause's partial expansion
       attempt (roll new_proof/map/next_id back to before it started --
       the abandoned partial steps are orphaned, not freed, matching
       this function's existing rare-failure-path convention) and keep
       the clause in its original, compact form instead of abandoning
       the WHOLE proof's expansion. */
    new_proof = new_proof_before;
    map = map_before;
    next_id = next_id_before;
    current = copy_clause_ija(c);
    current->id = c->id;
    new_proof = plist_prepend(new_proof, current);
  }  /* process proof step c */

  *pmap = map;  /* make available to caller */

  /* Restore the search's AC unification limits (lifted at entry). */
  set_ac_superset_limit(save_ss_limit);
  set_ac_walk_budget(save_walk_combos, save_walk_seconds);

  zap_ac_axiom_set(Ac_axioms);
  new_proof = reverse_plist(new_proof);
  check_parents_and_uplinks_in_proof(new_proof);

  /* Bridging steps (expand_ac_para_entry, ac_expand.c) deliberately
     leave apply()'s multiplier*MAX_VARS+VARNUM encoding on the
     instantiated into-clause and on any bridge para that copies from
     it -- required so those variables still term_ident-match the
     flattened AC groups while the bridge itself is being built (see
     the "Do NOT renumber here" comment in expand_ac_para_entry).
     That encoding routinely produces varnums >= MAX_VARS (100).  Once
     the expanded proof is committed here, every clause must go back
     to being an ordinary 0..n-1 clause like any search clause: the
     substitution-rider printers (sb_append_para_subst,
     sb_append_res_subst, sb_append_factor_subst,
     compute_post_primary_atoms in just.c) call plain unify() on these
     clauses, and unify()'s DEREFERENCE/BIND_TR index
     Context.terms[VARNUM] / Context.contexts[VARNUM], which are only
     sized MAX_VARS -- an out-of-range varnum reads/writes past the
     Context struct into whatever heap memory follows it. */
  {
    Plist q;
    for (q = new_proof; q; q = q->next)
      renumber_variables((Topform) q->v, MAX_VARS);
  }

  if (dbg)
    fprintf(stderr, "AC_PARA_STAT: SUMMARY para_just_total=%d para_just_ac_relevant=%d\n",
	    stat_para_total, stat_para_ac);
  return new_proof;
}  /* expand_proof */

/*************
 *
 *   renumber_proof()
 *
 *************/

/* DOCUMENTATION
We assume that every clause occurs after its parents.
*/

/* PUBLIC */
void renumber_proof(Plist proof, int start)
{
  I2list map = NULL;         /* map old IDs to new IDs */
  int n = start;            /* for numbering the steps */
  Plist p;

  for (p = proof; p; p = p->next) {
    Topform c = p->v;
    int old_id = c->id;
    c->id = n++;
    map_just(c->justification, map);
    map = alist_insert(map, old_id, c->id);
  }
  zap_i2list(map);

  check_parents_and_uplinks_in_proof(proof);
}  /* renumber_proof */

/*************
 *
 *   copy_and_renumber_proof()
 *
 *************/

/* DOCUMENTATION
We assume that every clause occurs after its parents.
*/

/* PUBLIC */
Plist copy_and_renumber_proof(Plist proof, int start)
{
  Plist workproof = copy_clauses_ija(proof);
  renumber_proof(workproof, start);
  return workproof;
}  /* copy_and_renumber_proof */

/*************
 *
 *   proof_to_xproof()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist proof_to_xproof(Plist proof)
{
  I3list map;
  Plist xproof = expand_proof(proof, &map);
  return xproof;
}  /* proof_to_xproof */

