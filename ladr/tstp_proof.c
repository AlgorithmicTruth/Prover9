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

#include "tstp_proof.h"
#include "tptp_trans.h"
#include "clauseid.h"
#include "just.h"
#include <string.h>

/* Private definitions and types */

/*
 * Name-to-ID mapping for TSTP clause names.
 * Prover9 uses "c_NNN" (parseable to integer).  External provers
 * (E, Vampire, etc.) use arbitrary names like "pel55_4", "c_0_18".
 * We assign sequential LADR IDs and maintain a mapping.
 */

#define NAME_MAP_SIZE 8192  /* hash table size */

struct name_entry {
  char *name;
  int   id;
  struct name_entry *next;
};

static struct name_entry *Name_map[NAME_MAP_SIZE];
static int Next_id = 1;

static
unsigned name_hash(const char *s)
{
  unsigned h = 0;
  while (*s)
    h = h * 31 + (unsigned char)*s++;
  return h % NAME_MAP_SIZE;
}  /* name_hash */

static
void name_map_init(void)
{
  int i;
  for (i = 0; i < NAME_MAP_SIZE; i++)
    Name_map[i] = NULL;
  Next_id = 1;
}  /* name_map_init */

static
int name_to_id(const char *name)
{
  unsigned h = name_hash(name);
  struct name_entry *e;
  for (e = Name_map[h]; e; e = e->next) {
    if (strcmp(e->name, name) == 0)
      return e->id;
  }
  return 0;  /* not found */
}  /* name_to_id */

static
int name_register(const char *name, int id)
{
  unsigned h = name_hash(name);
  struct name_entry *e;
  e = (struct name_entry *) safe_malloc(sizeof(struct name_entry));
  e->name = (char *) safe_malloc(strlen(name) + 1);
  strcpy(e->name, name);
  e->id = id;
  e->next = Name_map[h];
  Name_map[h] = e;
  return id;
}  /* name_register */

/*************
 *
 *   resolve_tstp_name()
 *
 *   Given a TSTP clause name string, return its integer LADR ID.
 *   Handles:
 *     "c_NNN"   -- Prover9 format, extract NNN directly
 *     bare int  -- use directly
 *     arbitrary -- look up in name map
 *   Returns 0 if name is unknown.
 *
 *************/

static
int resolve_tstp_name(const char *s)
{
  int id;

  /* Try "c_NNN" format */
  if (s[0] == 'c' && s[1] == '_') {
    if (str_to_int((char *)(s + 2), &id) && id > 0)
      return id;
  }
  /* Try bare integer */
  if (str_to_int((char *)s, &id) && id > 0)
    return id;

  /* Look up in name map */
  return name_to_id(s);
}  /* resolve_tstp_name */

/*************
 *
 *   parse_tstp_parent_ids()
 *
 *   Extract parent IDs from a TSTP parent list term.
 *   Handles:
 *     Prover9: [c_1, c_2, c_3]  -- flat list of c_NNN refs
 *     E prover: [c_0_18, inference(rw,...,[c_0_19, c_0_50]), c_0_51]
 *       -- nested inference() terms contain further parent refs
 *   Returns an Ilist of integer IDs.
 *
 *************/

static
Ilist parse_tstp_parent_ids(Term list_term)
{
  Ilist parents = NULL;

  /* Walk the list structure: $cons(head, tail) or $nil */
  while (cons_term(list_term)) {
    Term head = ARG(list_term, 0);
    char *s = sn_to_str(SYMNUM(head));

    if (str_ident(s, "inference") && ARITY(head) == 3) {
      /* Nested inference: extract parent refs from its parent list (arg 2) */
      Ilist nested = parse_tstp_parent_ids(ARG(head, 2));
      Ilist q;
      for (q = nested; q; q = q->next)
        parents = ilist_append(parents, q->i);
      zap_ilist(nested);
    }
    else {
      /* Direct reference: resolve name to ID */
      int id = resolve_tstp_name(s);
      if (id > 0)
        parents = ilist_append(parents, id);
    }
    list_term = ARG(list_term, 1);
  }
  return parents;
}  /* parse_tstp_parent_ids */

/*************
 *
 *   tptp_rule_name_to_just()
 *
 *   Reverse mapping from TSTP inference rule name to LADR Just_type.
 *
 *************/

/* PUBLIC */
Just_type tptp_rule_name_to_just(const char *name)
{
  /* Prover9 rule names */
  if (str_ident((char *) name, "resolve"))       return BINARY_RES_JUST;
  if (str_ident((char *) name, "hyper"))          return HYPER_RES_JUST;
  if (str_ident((char *) name, "ur"))             return UR_RES_JUST;
  if (str_ident((char *) name, "paramod"))        return PARA_JUST;
  if (str_ident((char *) name, "factor"))         return FACTOR_JUST;
  if (str_ident((char *) name, "xxres"))          return XXRES_JUST;
  if (str_ident((char *) name, "assume_negation"))return DENY_JUST;
  if (str_ident((char *) name, "clausify"))       return CLAUSIFY_JUST;
  if (str_ident((char *) name, "copy"))           return COPY_JUST;
  if (str_ident((char *) name, "back_demod"))     return BACK_DEMOD_JUST;
  if (str_ident((char *) name, "back_unit_del"))  return BACK_UNIT_DEL_JUST;
  if (str_ident((char *) name, "new_symbol"))     return NEW_SYMBOL_JUST;
  if (str_ident((char *) name, "expand_def"))     return EXPAND_DEF_JUST;
  if (str_ident((char *) name, "propositional"))  return PROPOSITIONAL_JUST;
  if (str_ident((char *) name, "instantiate"))    return INSTANCE_JUST;
  if (str_ident((char *) name, "rewrite"))        return DEMOD_JUST;
  if (str_ident((char *) name, "unit_del"))       return UNIT_DEL_JUST;
  if (str_ident((char *) name, "flip"))           return FLIP_JUST;
  if (str_ident((char *) name, "merge"))          return MERGE_JUST;
  if (str_ident((char *) name, "eval"))           return EVAL_JUST;

  /* E prover rule names */
  if (str_ident((char *) name, "spm"))            return PARA_JUST;
  if (str_ident((char *) name, "sr"))             return BINARY_RES_JUST;
  if (str_ident((char *) name, "rw"))             return DEMOD_JUST;
  if (str_ident((char *) name, "er"))             return BINARY_RES_JUST;
  if (str_ident((char *) name, "pm"))             return PARA_JUST;
  if (str_ident((char *) name, "ef"))             return FACTOR_JUST;
  if (str_ident((char *) name, "csr"))            return BINARY_RES_JUST;

  /* Vampire rule names */
  if (str_ident((char *) name, "resolution"))     return BINARY_RES_JUST;
  if (str_ident((char *) name, "superposition"))  return PARA_JUST;
  if (str_ident((char *) name, "cnf_transformation")) return CLAUSIFY_JUST;
  if (str_ident((char *) name, "skolemisation"))  return CLAUSIFY_JUST;
  if (str_ident((char *) name, "ennf_transformation")) return COPY_JUST;
  if (str_ident((char *) name, "flattening"))     return COPY_JUST;
  if (str_ident((char *) name, "rectify"))        return COPY_JUST;
  if (str_ident((char *) name, "negated_conjecture")) return DENY_JUST;
  if (str_ident((char *) name, "subsumption_resolution")) return BINARY_RES_JUST;
  if (str_ident((char *) name, "backward_demodulation")) return BACK_DEMOD_JUST;
  if (str_ident((char *) name, "forward_demodulation")) return DEMOD_JUST;
  if (str_ident((char *) name, "equality_resolution")) return BINARY_RES_JUST;
  if (str_ident((char *) name, "equality_factoring")) return FACTOR_JUST;
  if (str_ident((char *) name, "trivial_inequality_removal")) return COPY_JUST;
  if (str_ident((char *) name, "definition_unfolding")) return EXPAND_DEF_JUST;
  if (str_ident((char *) name, "definition_folding")) return COPY_JUST;
  if (str_ident((char *) name, "avatar_sat_refutation")) return PROPOSITIONAL_JUST;
  if (str_ident((char *) name, "avatar_split_clause")) return COPY_JUST;
  if (str_ident((char *) name, "avatar_contradiction_clause")) return COPY_JUST;
  if (str_ident((char *) name, "avatar_component_clause")) return COPY_JUST;
  if (str_ident((char *) name, "avatar_definition")) return COPY_JUST;
  if (str_ident((char *) name, "choice_axiom"))   return COPY_JUST;
  if (str_ident((char *) name, "predicate_definition_introduction")) return COPY_JUST;

  return COPY_JUST;  /* fallback for unknown/external prover rules */
}  /* tptp_rule_name_to_just */

/*************
 *
 *   build_just_from_source()
 *
 *   Build a LADR justification from a TSTP source annotation term.
 *   Handles:
 *     introduced(assumption,[])  --> INPUT_JUST
 *     introduced(conjecture,[])  --> GOAL_JUST
 *     file('/path/file.p', name) --> INPUT_JUST (E prover)
 *     inference(rule, info, parents) --> appropriate Just
 *
 *************/

static
Just build_just_from_source(Term source, char *role_str)
{
  char *top = sn_to_str(SYMNUM(source));

  if (str_ident(top, "introduced")) {
    /* introduced(assumption,[]) or introduced(conjecture,[]) */
    if (ARITY(source) >= 1) {
      char *kind = sn_to_str(SYMNUM(ARG(source, 0)));
      if (str_ident(kind, "conjecture"))
        return goal_just();
    }
    /* Default: treat as input (negated_conjecture is already negated) */
    return input_just();
  }

  if (str_ident(top, "file")) {
    /* file('/path/to/file.p', axiom_name) -- E prover input source */
    if (str_ident(role_str, "conjecture"))
      return goal_just();
    return input_just();  /* axiom, hypothesis, negated_conjecture */
  }

  if (str_ident(top, "inference") && ARITY(source) == 3) {
    /* inference(rule, [status(thm)], [c_1, c_2, ...]) */
    char *rule_name = sn_to_str(SYMNUM(ARG(source, 0)));
    Term parent_list = ARG(source, 2);
    Ilist parent_ids = parse_tstp_parent_ids(parent_list);
    Just_type jtype = tptp_rule_name_to_just(rule_name);
    Just j;

    /* Build justification based on type category */
    switch (jtype) {
    case DENY_JUST:
    case CLAUSIFY_JUST:
    case COPY_JUST:
    case BACK_DEMOD_JUST:
    case BACK_UNIT_DEL_JUST:
    case NEW_SYMBOL_JUST:
    case PROPOSITIONAL_JUST:
      /* Single-parent rules: use id-based justification */
      j = get_just();
      j->type = jtype;
      j->u.id = parent_ids ? parent_ids->i : 0;
      zap_ilist(parent_ids);
      return j;

    case BINARY_RES_JUST:
      /* Binary resolution: need (nuc_id, nuc_lit, sat_id, sat_lit) */
      /* TSTP loses literal positions; use placeholder 1 (='a') */
      j = get_just();
      j->type = BINARY_RES_JUST;
      if (parent_ids && parent_ids->next) {
        j->u.lst = ilist_append(
                     ilist_append(
                       ilist_append(
                         ilist_append(NULL, parent_ids->i), 1),
                       parent_ids->next->i), 1);
      }
      else {
        /* Fewer than 2 parents -- treat as copy */
        j->type = COPY_JUST;
        j->u.id = parent_ids ? parent_ids->i : 0;
      }
      zap_ilist(parent_ids);
      return j;

    case HYPER_RES_JUST:
    case UR_RES_JUST:
      /* Multi-parent resolution: (nuc_id, [nuc_lit, sat_id, sat_lit]...) */
      j = get_just();
      j->type = jtype;
      {
        Ilist lst = NULL;
        Ilist p;
        if (parent_ids) {
          lst = ilist_append(lst, parent_ids->i);  /* nucleus */
          for (p = parent_ids->next; p; p = p->next) {
            lst = ilist_append(lst, 1);    /* nuc_lit placeholder (='a') */
            lst = ilist_append(lst, p->i); /* satellite id */
            lst = ilist_append(lst, 1);    /* sat_lit placeholder (='a') */
          }
        }
        j->u.lst = lst;
      }
      zap_ilist(parent_ids);
      return j;

    case PARA_JUST:
    case PARA_FX_JUST:
    case PARA_IX_JUST:
    case PARA_FX_IX_JUST:
      /* Paramodulation: need from_id, into_id, positions */
      j = get_just();
      j->type = jtype;
      j->u.para = get_parajust();
      j->u.para->from_id = parent_ids ? parent_ids->i : 0;
      j->u.para->into_id = (parent_ids && parent_ids->next) ?
                            parent_ids->next->i : 0;
      j->u.para->from_pos = ilist_append(NULL, 1);  /* placeholder */
      j->u.para->into_pos = ilist_append(ilist_append(NULL, 1), 1);
      zap_ilist(parent_ids);
      return j;

    case FACTOR_JUST:
      /* Factor: (clause_id, lit1, lit2) */
      j = get_just();
      j->type = FACTOR_JUST;
      j->u.lst = ilist_append(
                   ilist_append(
                     ilist_append(NULL,
                       parent_ids ? parent_ids->i : 0), 1), 2);
      zap_ilist(parent_ids);
      return j;

    case XXRES_JUST:
      /* xxres: (clause_id, lit) */
      j = get_just();
      j->type = XXRES_JUST;
      j->u.lst = ilist_append(
                   ilist_append(NULL,
                     parent_ids ? parent_ids->i : 0), 1);
      zap_ilist(parent_ids);
      return j;

    case EXPAND_DEF_JUST:
      /* expand_def: (clause_id, def_id) */
      j = get_just();
      j->type = EXPAND_DEF_JUST;
      j->u.lst = ilist_append(
                   ilist_append(NULL,
                     parent_ids ? parent_ids->i : 0),
                   (parent_ids && parent_ids->next) ?
                     parent_ids->next->i : 0);
      zap_ilist(parent_ids);
      return j;

    case DEMOD_JUST:
      /* Demod: list of (demod_id, position, direction) triples.
         TSTP loses this detail; create one entry per parent. */
      {
        I3list steps = NULL;
        Ilist p;
        for (p = parent_ids; p; p = p->next)
          steps = i3list_append(steps, p->i, 0, 1);
        j = get_just();
        j->type = DEMOD_JUST;
        j->u.demod = steps;
      }
      zap_ilist(parent_ids);
      return j;

    case UNIT_DEL_JUST:
      /* unit_del: (lit_num, deleter_id) */
      j = get_just();
      j->type = UNIT_DEL_JUST;
      j->u.lst = ilist_append(
                   ilist_append(NULL, 1),  /* placeholder lit */
                   parent_ids ? parent_ids->i : 0);
      zap_ilist(parent_ids);
      return j;

    case FLIP_JUST:
      j = get_just();
      j->type = FLIP_JUST;
      j->u.id = 1;  /* placeholder literal number */
      zap_ilist(parent_ids);
      return j;

    case MERGE_JUST:
      j = get_just();
      j->type = MERGE_JUST;
      j->u.id = 1;  /* placeholder literal number */
      zap_ilist(parent_ids);
      return j;

    case EVAL_JUST:
      j = get_just();
      j->type = EVAL_JUST;
      j->u.id = 1;
      zap_ilist(parent_ids);
      return j;

    default:
      /* Unknown type: treat as copy of first parent */
      j = get_just();
      j->type = COPY_JUST;
      j->u.id = parent_ids ? parent_ids->i : 0;
      zap_ilist(parent_ids);
      return j;
    }
  }

  /* Fallback: use role to determine justification */
  if (str_ident(role_str, "conjecture"))
    return goal_just();
  return input_just();  /* axiom, hypothesis, negated_conjecture */
}  /* build_just_from_source */

/*************
 *
 *   is_clausal_term()
 *
 *   Check if a LADR term (output of tptp3_to_ladr_term) is clausal,
 *   i.e., contains only disjunction, negation, and atoms (no &, ->,
 *   <->, quantifiers).  Used to detect FOF entries that are really
 *   clauses (common in Vampire output where everything is fof(...)).
 *
 *************/

static
BOOL is_clausal_term(Term t)
{
  if (is_term(t, and_sym(), 2) ||
      is_term(t, imp_sym(), 2) ||
      is_term(t, iff_sym(), 2) ||
      is_term(t, impby_sym(), 2) ||
      is_term(t, quant_sym(), 3))
    return FALSE;
  if (is_term(t, or_sym(), 2))
    return is_clausal_term(ARG(t, 0)) && is_clausal_term(ARG(t, 1));
  if (is_term(t, not_sym(), 1))
    return is_clausal_term(ARG(t, 0));
  return TRUE;  /* atom, $true, $false, =, != */
}  /* is_clausal_term */

/*************
 *
 *   read_tstp_proof()
 *
 *   Read a TSTP-format proof from fin and return a Plist of Topform
 *   clauses with LADR justifications.  Clauses are registered in
 *   the clause ID table.
 *
 *   Expects parse types to be appropriately declared before calling.
 *
 *   Handles both Prover9 TSTP (c_NNN names) and external prover TSTP
 *   (arbitrary names like pel55_4, c_0_18, f501).  For external provers,
 *   sequential LADR IDs are assigned and a name-to-ID mapping is built.
 *
 *   Skips comment lines (%), SZS delimiter lines, and blank lines.
 *   Reads cnf(...), fof(...), and tff(...) annotated formulas.
 *
 *************/

/* PUBLIC */
Plist read_tstp_proof(FILE *fin, FILE *ferr)
{
  Plist proof = NULL;
  Plist terms = NULL;
  Plist p;
  Term t;
  BOOL use_name_map = FALSE;

  name_map_init();

  /* Pass 1: read all terms and pre-register step names.
     This handles forward references (e.g., Vampire outputs proofs
     in reverse order: conclusion first, premises last). */
  t = read_term(fin, ferr);
  while (t != NULL) {
    char *top = sn_to_str(SYMNUM(t));
    terms = plist_append(terms, t);

    if ((str_ident(top, "cnf") || str_ident(top, "fof") ||
         str_ident(top, "tff")) &&
        (ARITY(t) >= 3 && ARITY(t) <= 5)) {
      char *name_str = sn_to_str(SYMNUM(ARG(t, 0)));
      int id = resolve_tstp_name(name_str);
      if (id <= 0) {
        use_name_map = TRUE;
        id = Next_id++;
        name_register(name_str, id);
      }
      else if (!use_name_map) {
        if (id >= Next_id)
          Next_id = id + 1;
      }
    }
    t = read_term(fin, ferr);
  }

  /* Pass 2: build proof entries with all names now resolvable. */
  for (p = terms; p; p = p->next) {
    char *top;
    int id;
    char *name_str;
    Topform cl;
    char *role_str;
    Term body_term;
    Term ladr_body;
    Term source_term;
    BOOL is_cnf;

    t = (Term) p->v;
    top = sn_to_str(SYMNUM(t));

    /* Check for cnf/fof/tff with 3, 4, or 5 arguments.
       (5 args: E prover appends ['proof'] annotation as 5th arg.) */
    if ((str_ident(top, "cnf") || str_ident(top, "fof") ||
         str_ident(top, "tff")) &&
        (ARITY(t) >= 3 && ARITY(t) <= 5)) {

      is_cnf = str_ident(top, "cnf");

      /* Look up pre-registered name */
      name_str = sn_to_str(SYMNUM(ARG(t, 0)));
      id = resolve_tstp_name(name_str);
      if (id <= 0)
        id = 1;  /* should not happen after pass 1 */

      role_str = sn_to_str(SYMNUM(ARG(t, 1)));
      body_term = ARG(t, 2);
      source_term = (ARITY(t) >= 4) ? ARG(t, 3) : NULL;

      /* Convert body from TPTP to LADR term */
      ladr_body = tptp3_to_ladr_term(copy_term(body_term));

      if (is_cnf || is_clausal_term(ladr_body)) {
        /* CNF entry, or FOF entry with clausal body (e.g., Vampire
           wraps clauses in fof(...) after cnf_transformation) */
        cl = term_to_clause(ladr_body);
        zap_term(ladr_body);
        clause_set_variables(cl, MAX_VARS);
      }
      else {
        /* True FOF: convert term to formula, then to topform */
        Formula f = term_to_formula(ladr_body);
        zap_term(ladr_body);
        cl = get_topform();
        cl->is_formula = TRUE;
        cl->formula = f;
      }

      /* Set ID */
      cl->id = id;

      /* Build justification */
      if (source_term != NULL)
        cl->justification = build_just_from_source(source_term, role_str);
      else {
        /* No source annotation: determine from role */
        if (str_ident(role_str, "axiom") ||
            str_ident(role_str, "hypothesis"))
          cl->justification = input_just();
        else if (str_ident(role_str, "conjecture"))
          cl->justification = goal_just();
        else
          cl->justification = input_just();
      }

      /* Register in clause ID table */
      register_clause_with_id(cl);

      proof = plist_append(proof, cl);
    }
    /* else: skip non cnf/fof/tff terms (e.g., "end_of_list") */

    zap_term(t);
  }
  zap_plist(terms);

  return proof;
}  /* read_tstp_proof */
