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

#ifndef TP_TPTP_PARSE_H
#define TP_TPTP_PARSE_H

#include "formula.h"
#include "topform.h"
#include "glist.h"

/* INTRODUCTION
Native TPTP FOF/CNF parser for Prover9.  Self-contained lexer +
recursive-descent parser that reads TPTP files directly and produces
Formula structures, bypassing the LADR parser entirely.
*/

/* Public definitions */

typedef struct tptp_input * Tptp_input;

struct tptp_input {
  Plist assumptions;    /* Plist of Formula */
  Plist goals;          /* Plist of Formula (conjecture role) */
  Plist magic_commands; /* Plist of (char *) -- "% prover9:" option lines */
  BOOL  has_neg_conj;   /* TRUE if any cnf(negated_conjecture) was seen */
  Plist distinct_objects; /* Plist of (char *) -- unique distinct object names */
};

/* Scan-pass data structures for SInE-before-parse optimization.
   scan_entry holds one scanned fof/cnf formula's metadata + saved body text.
   scan_result holds the complete scan output. */

#define SCAN_ROLE_ASSUMPTION  0
#define SCAN_ROLE_GOAL        1
#define SCAN_ROLE_NEG_CONJ    2  /* cnf negated_conjecture: seeds SInE like goal */
#define SCAN_ROLE_HYPOTHESIS  3  /* hypothesis: seeds SInE like goal, goes to SOS */

struct scan_entry {
  char *body_text;   /* saved formula body token text (malloc'd) */
  int   body_len;    /* length of body_text */
  int  *syms;        /* array of temp symbol IDs (malloc'd) */
  int   nsyms;       /* count of unique symbols */
  int   role;        /* SCAN_ROLE_* */
  BOOL  is_fof;      /* TRUE for fof, FALSE for cnf */
  char  name[256];   /* formula name for diagnostics */
  int   eq_count;        /* occurrences of = in body */
  int   pipe_count;      /* occurrences of | in body */
  int   tilde_count;     /* occurrences of ~ in body */
  int   max_paren_depth; /* maximum parenthesis nesting depth */
};

typedef struct scan_result * Scan_result;

struct scan_result {
  struct scan_entry *entries;
  int    n_entries;
  int    n_axioms;       /* count of assumption-role entries */
  int    n_goals;        /* count of goal-role entries */
  int    n_symbols;      /* total unique symbol IDs assigned */
  Plist  magic_commands; /* collected "% prover9:" comments */
  BOOL   has_neg_conj;   /* any cnf(negated_conjecture) seen */
  Plist  distinct_objects; /* Plist of (char *) -- unique distinct object names */
};

/* End of public definitions */

/* Public function prototypes from tptp_parse.c */

Tptp_input read_tptp_file(const char *filename);

Tptp_input read_tptp_stream(FILE *fin, const char *source_name);

void zap_tptp_input(Tptp_input input);

Scan_result scan_tptp_formulas(const char *filename);

Scan_result scan_tptp_stream(FILE *fin, const char *source_name);

Tptp_input parse_scanned_formulas(Scan_result scan, BOOL *keep);

void free_scan_result(Scan_result scan);

Plist tptp_distinct_object_axioms(Plist distinct_names);

int get_tptp_name_attr(void);

#endif  /* conditional compilation of whole file */
