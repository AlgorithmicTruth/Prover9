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

#ifndef TP_AC_EXPAND_H
#define TP_AC_EXPAND_H

#include "demod.h"

/* INTRODUCTION
AC-aware proof expansion.  expand_proof() (xproofs.c) unrolls compound
justifications into one-op-per-step form so external tools can replay a
proof step by step.  Its two replay primitives -- para_pos() (paramod.c)
and particular_demod()/part_recurse() (demod.c) -- only ever understood
ordinary (non-AC) match()/unify().  This file adds the AC-aware layer:

  1. Rediscovery: given a demodulator ID (the only trustworthy part of a
     recorded AC DEMOD_JUST triple -- the position/sequence is documented
     as advisory under AC canonicalization, see demod.c's demod_bt), find
     a candidate node+substitution in the current working clause where
     that demodulator's LHS AC-matches, via btm.c's match_bt_first/next.

  2. Bridging: given a found candidate, synthesize a sequence of ordinary,
     single-position "phantom axiom" (commutativity/associativity) steps
     that reshape the term into the exact shape the match needs, so the
     real rewrite becomes a plain step that particular_demod() already
     replays correctly, unmodified.

Phantom axioms are SYNTHESIZED (see build_ac_axiom_set()'s own comment
for why that's the right call, not forgery: assoc_comm(f) already
semantically entails them, and a verifier checks proof citations against
its OWN problem file -- which for a faithful TPTP rendering of an AC
theory already states comm/assoc explicitly -- not against whatever
Prover9's search happened to touch internally).  Deliberately NOT
injected into the actual search as real input clauses: their maximally
general shape would make every use a genuine, expensive AC-unification
problem for zero deductive gain over the built-in assoc_comm mechanism
(observed directly: adding them as real search clauses raised
ac_walk_budget abandonments from 3 to 20+ on the same problem).
*/

/* Public definitions */

typedef struct ac_axiom_set * Ac_axiom_set;

/* End of public definitions */

/* Public function prototypes from ac_expand.c */

/* Synthesizes one comm/assoc pair per AC-declared symbol found in
   `proof`.  Each gets an id from *next_id (so callers can use the axiom
   set immediately, before any clauses derived from it exist).  Does NOT
   touch a proof/new_proof list -- see ac_axiom_set_clauses(). */
Ac_axiom_set build_ac_axiom_set(Plist proof, int *next_id);

/* All synthesized axiom clauses in `set`, as a Plist (one entry per
   comm/assoc pair per symbol).  Caller should prepend this to
   *new_proof AFTER the main per-clause loop (so it ends up FIRST in
   printed order once new_proof is reversed, matching where axiom leaves
   conventionally appear). */
Plist ac_axiom_set_clauses(Ac_axiom_set set);

void zap_ac_axiom_set(Ac_axiom_set set);

BOOL ac_axiom_set_has(Ac_axiom_set set, int symbol_num);

BOOL find_ac_demod_candidate(Topform work, Topform demod, int direction,
			    int alt_index,
			    Ilist *out_tree_pos, Context *out_subst,
			    Term *out_matched_node, Btm_state *out_bt);

/* Does t contain an AC-declared symbol anywhere (not just at its
   head)?  expand_proof() uses this to decide whether a failed PLAIN
   replay is worth retrying through the AC-aware deep-bridging path. */
BOOL term_contains_ac(Term t);

/* alt_start (in/out): candidate resume point, advanced past each
   returned candidate -- same contract as expand_ac_para_entry's, used
   by expand_proof's chain-odometer to retry a compound chain with a
   different rewrite-position choice at one citation. */
Plist expand_ac_demod_entry(Topform work, Topform demod, int direction,
			   Ac_axiom_set axioms,
			   int *next_id, I3list *map,
			   int old_id, int *old_id_n,
			   int *alt_start,
			   Topform *out_result);

Topform ac_extension_of(Topform c);

/* Phase 2: PARA_JUST (paramodulation) bridging.  See the block comment
   above expand_ac_para_entry() in ac_expand.c for the design (into-side
   regrouping only; a candidate needing genuine into-side instantiation,
   not just permutation of its own existing pieces, is skipped in favor
   of the next alt_index).

   `alt_start` (in/out): the alt_index to resume candidate enumeration
   from; on success it is advanced past the returned candidate, so a
   caller that later decides the candidate was wrong (e.g. the recorded
   compound justification's rewrite suffix, replayed on top of it,
   doesn't reproduce the recorded clause) can call again to get the next
   one.  `expected` may be NULL: accept the first mechanically valid
   candidate without matching it against a recorded clause -- used when
   the caller judges the candidate only after replaying the rest of the
   compound justification (a bare paramodulant can never equal the
   post-rewrite recorded clause, so matching here would always fail). */

/* `into_pos` may be NULL (walk every subterm) or the recorded
   PARA_JUST into-position (literal + path).  When non-NULL it is
   preferred: para_into() records an unambiguous application site, so
   rediscovery should enumerate AC unifiers AT that site rather than
   any same-head node elsewhere in `into` (which produces mechanically
   valid but search-irrelevant paramodulants).  Falls back to a full
   walk only if the recorded site yields no unifier. */
BOOL find_ac_para_candidate(Topform from, Ilist from_pos, Topform into,
			   Ilist into_pos,
			   int alt_index,
			   Ilist *out_into_tree_pos, Context *out_from_subst,
			   Context *out_into_subst, Term *out_alpha,
			   Term *out_matched_node, Btu_state *out_bt);

Plist expand_ac_para_entry(Topform from, Ilist from_pos,
			  Topform into, Ilist into_pos,
			  Ac_axiom_set axioms,
			  int *next_id, I3list *map,
			  int old_id, int *old_id_n,
			  int *alt_start,
			  Topform expected,
			  Topform *out_result);

/* Is `result` an acceptable stand-in for the recorded proof clause
   `expected`?  AC-canonicalizes copies of both sides' literals, then
   compares via variant() rather than exact clause_ident() -- see the
   function's own comment in ac_expand.c for why exact identity is the
   wrong bar for an independently-rediscovered AC unifier's result. */
BOOL ac_result_matches_expected(Topform result, Topform expected);

/* Like particular_demod(), but if the preferred sequence number fails
   (common after AC reshaping earlier in a compound chain -- positions
   are advisory under AC), scan other sequence numbers.  Mutates `c` on
   success.  Used by expand_proof for non-AC-headed demods in mixed AC
   chains and by the in-process chain explorer. */
BOOL particular_demod_scan(Topform c, Topform demod, int preferred_pos,
			   int direction, Ilist *from_pos, Ilist *ipos);

/* Cheap probe: can `demod` (direction `dir`) apply to `work` at least
   once -- plain particular_demod (with position scan) and/or any AC
   rediscovery alt?  Used as one-step lookahead by expand_proof's chain
   odometer and by explore_ac_demod_chain().  Does not mutate `work`. */
BOOL ac_demod_step_viable(Topform work, Topform demod, int direction,
			  int position);

/* In-process multi-step search: find an ordered sequence of demod alt
   choices (same encoding as expand_proof's chain_plan: -1 = plain
   particular_demod first, >=0 = AC alt_start for expand_ac_demod_entry)
   that takes `start` to something ac_result_matches_expected against
   `expected` by applying demods[0..n-1] in order.  Returns the plan
   Ilist, or NULL if none found within the internal state budget.
   Does not mutate `start` and does not splice into a real proof -- the
   caller re-runs the plan through the ordinary expand path to emit
   justified steps.  Pure in-process; no subprocess/fork. */
Ilist explore_ac_demod_chain(Topform start,
			     Topform *demods, int *directions, int *positions,
			     int n,
			     Topform expected,
			     Ac_axiom_set axioms);

#endif  /* conditional compilation of whole file */
