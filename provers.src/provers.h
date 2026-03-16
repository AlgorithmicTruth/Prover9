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

#ifndef TP_PROVERS_H
#define TP_PROVERS_H

#include "search.h"
#include "../ladr/tptp_parse.h"

/* INTRODUCTION
*/

/* Public definitions */

#define MAX_CORES 64   /* upper bound for -cores N validation */

/* Result of phase 1 (scan only) for TPTP mode.
   Used by strategy scheduler to fork before SInE/parse/clausify. */

typedef struct prover_scan_result * Prover_scan_result;

struct prover_scan_result {
  Scan_result scan;        /* raw scan data (formulas, symbols, roles) */
  Prover_options options;  /* initialized prover options */
  BOOL echo;               /* echo input? */
  int argc;
  char **argv;
  char *tptp_file;         /* .p filename or NULL (stdin) */
  BOOL tptp_out;           /* -tptp_out flag */
  BOOL ladr_out;           /* -ladr_out flag */
};

/* End of public definitions */

/* Public function prototypes from provers.c */

Prover_input std_prover_init_and_input(int argc, char **argv,
				       BOOL clausify,
				       BOOL echo,
				       int unknown_action);

/* Two-phase TPTP entry points for fork-before-SInE scheduling. */
Prover_scan_result std_prover_init_and_scan(int argc, char **argv);

Prover_input std_prover_from_scan(Prover_scan_result psr,
                                  int sine_tolerance,
                                  int sine_depth,
                                  int sine_max_axioms);

/* From provers.c: install SIGUSR2 handler once Opt/Glob are ready */
void enable_sigusr2_checkpoint(void);

/* From provers.c: check/clear checkpoint request flag */
BOOL checkpoint_requested(void);
void clear_checkpoint_request(void);

/* From provers.c: signal-based timeout and no_kill proof protection */
void setup_timeout_signal(int seconds);
void set_no_kill(void);
void clear_no_kill_and_check(void);
void set_tptp_mode_for_sig(void);

#endif  /* conditional compilation of whole file */
