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

#include "search.h"
#include "provers.h"
#include "../ladr/ac_redun.h"
#include "../ladr/memory.h"
#include "../ladr/string.h"
#include "../ladr/sine.h"
#include "../ladr/clash.h"
#include "../ladr/tptp_parse.h"
#include "../VERSION_DATE.h"

// system includes

#include <sys/types.h>
#include <sys/stat.h>
#ifndef __EMSCRIPTEN__
#include <sys/wait.h>
#endif
#include <unistd.h>
#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#endif
#include <float.h>
#include <math.h>
#include <setjmp.h>  /* Yikes! */
#include <errno.h>
#include <time.h>
#include <dirent.h>

// Private definitions and types

static jmp_buf Jump_env;                 // for setjmp/longjmp

static Prover_options Opt;               // Prover9 options
static struct prover_attributes Att;     // Prover9 accepted attributes
static struct prover_stats Stats;        // Prover9 statistics
static struct prover_clocks Clocks;      // Prover9 clocks

/* Progress callback for shared-memory IPC (set by -cores scheduler) */
static Search_progress_fn Progress_callback = NULL;

#ifdef __EMSCRIPTEN__
static double Wasm_deadline_ms = 0;
#endif

/* "% " prefix for diagnostic output in TPTP mode (makes it a TPTP comment) */
#define TPTP_PFX  (Opt && flag(Opt->tptp_output) ? "% " : "")

/* Saved selector state from checkpoint (used during resume) */
static char Resume_low_selector_name[32] = "";
static int  Resume_low_selector_count = 0;
static char Resume_high_selector_name[32] = "";
static int  Resume_high_selector_count = 0;

/* Saved hint_match data for restoring matching_hint pointers */
static struct clause_meta *Resume_meta = NULL;
static int Resume_meta_count = 0;

/* In-loop checkpoint loading state */
static BOOL Load_checkpoint = FALSE;  /* TRUE on first loop iteration during resume */
static const char *Resume_dir = NULL; /* checkpoint directory for in-loop loading */

/* Saved cac_clauses IDs from checkpoint (restored after clause loading) */
static unsigned long long *Resume_cac_ids = NULL;
static int Resume_cac_count = 0;

/* Saved desc_to_be_disabled IDs from checkpoint */
static unsigned long long *Resume_dtbd_ids = NULL;
static int Resume_dtbd_count = 0;

/* Hoisted from make_inferences() for checkpoint save/restore */
static int Bf_level = 0;             /* breadth-first level counter */
static int Bf_last_of_level = 0;     /* last clause ID of current level */
static int Nohints_count = 0;        /* consecutive givens without hint match */

/* Periodic automatic checkpoint state */
static time_t Last_auto_ckpt_time = 0;       // wall-clock of last auto checkpoint
static char **Auto_ckpt_dirs = NULL;          // circular buffer of dir names
static int    Auto_ckpt_capacity = 0;
static int    Auto_ckpt_head = 0;             // index of oldest entry
static int    Auto_ckpt_count = 0;            // number of entries in buffer

/* Clause tracing (cl_to_trace parameter) */
static unsigned long long To_trace_id = 0;
static Topform To_trace_cl = NULL;

/* Hitlist for print_derivations (Veroff feature) */
#define MAX_HSIZE 5000
static int HIT_LIST[MAX_HSIZE];
static int Hsize = 0;

// The following is a global structure for this file.

static struct {

  // basic clause lists

  Clist sos;
  Clist usable;
  Clist demods;
  Clist hints;

  // other lists

  Plist actions;
  Plist weights;
  Plist kbo_weights;
  Plist interps;
  Plist given_selection;
  Plist keep_rules;
  Plist delete_rules;

  // auxiliary clause lists

  Clist limbo;
  Clist disabled;
  Plist empties;

  // indexing

  Lindex clashable_idx;  // literal index for resolution rules
  BOOL use_clash_idx;    // GET RID OF THIS VARIABLE!!

  // basic properties of usable+sos

  BOOL horn, unit, equality;
  unsigned number_of_clauses, number_of_neg_clauses;

  // other stuff

  Plist desc_to_be_disabled;   // Descendents of these to be disabled
  Plist cac_clauses;           // Clauses that trigger back CAC check

  BOOL searching;      // set to TRUE when first given is selected
  BOOL initialized;    // has this structure been initialized?
  BOOL has_goals;      // goals/conjecture was present in input
  BOOL has_neg_conj;   // CNF negated_conjecture was present (refutation problem)
  char *problem_name;  // TPTP problem name for SZS lines (e.g., "PUZ001-2")
  double start_time;   // when was it initialized? 
  int start_ticks;     // quasi-clock that times the same for all machines

  int return_code;     // result of search
} Glob;

// How many statics are to be output?

/*************
 *
 *    init_prover_options()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Prover_options init_prover_options(void)
{
  Prover_options p = safe_calloc(1, sizeof(struct prover_options));
  // FLAGS:
  //   internal name                    external name            default

  // The following are now in ../ladr/std_options.c.
  // ?? = init_flag("prolog_style_variables", FALSE);
  // ?? = init_flag("clocks",                 FALSE);

  p->binary_resolution      = init_flag("binary_resolution",      FALSE);
  p->neg_binary_resolution  = init_flag("neg_binary_resolution",  FALSE);
  p->hyper_resolution       = init_flag("hyper_resolution",       FALSE);
  p->pos_hyper_resolution   = init_flag("pos_hyper_resolution",   FALSE);
  p->neg_hyper_resolution   = init_flag("neg_hyper_resolution",   FALSE);
  p->ur_resolution          = init_flag("ur_resolution",          FALSE);
  p->pos_ur_resolution      = init_flag("pos_ur_resolution",      FALSE);
  p->neg_ur_resolution      = init_flag("neg_ur_resolution",      FALSE);
  p->paramodulation         = init_flag("paramodulation",         FALSE);
  p->eval_rewrite           = init_flag("eval_rewrite",           FALSE);

  p->ordered_res            = init_flag("ordered_res",            TRUE);
  p->check_res_instances    = init_flag("check_res_instances",    FALSE);
  p->ordered_para           = init_flag("ordered_para",           TRUE);
  p->check_para_instances   = init_flag("check_para_instances",   FALSE);
  p->para_units_only        = init_flag("para_units_only",        FALSE);
  p->para_from_vars         = init_flag("para_from_vars",         TRUE);
  p->para_into_vars         = init_flag("para_into_vars",         FALSE);
  p->para_from_small        = init_flag("para_from_small",        FALSE);
  p->basic_paramodulation   = init_flag("basic_paramodulation",   FALSE);
  p->initial_nuclei         = init_flag("initial_nuclei",         FALSE);

  p->process_initial_sos    = init_flag("process_initial_sos",     TRUE);
  p->back_demod             = init_flag("back_demod",              TRUE);
  p->lex_dep_demod          = init_flag("lex_dep_demod",           TRUE);
  p->lex_dep_demod_sane     = init_flag("lex_dep_demod_sane",      TRUE);
  p->safe_unit_conflict     = init_flag("safe_unit_conflict",     FALSE);
  p->reuse_denials          = init_flag("reuse_denials",          FALSE);
  p->back_subsume           = init_flag("back_subsume",            TRUE);
  p->back_subsume_skip_used = init_flag("back_subsume_skip_used", FALSE);
  p->back_subsume_skip_limbo= init_flag("back_subsume_skip_limbo",FALSE);
  p->unit_deletion          = init_flag("unit_deletion",          FALSE);
  p->factor                 = init_flag("factor",                 FALSE);
  p->cac_redundancy         = init_flag("cac_redundancy",          TRUE);
  p->degrade_hints          = init_flag("degrade_hints",           TRUE);
  p->limit_hint_matchers    = init_flag("limit_hint_matchers",    FALSE);
  p->back_demod_hints       = init_flag("back_demod_hints",        TRUE);
  p->collect_hint_labels    = init_flag("collect_hint_labels",    FALSE);
  p->hint_match_stats       = init_flag("hint_match_stats",       FALSE);
  p->hint_match_once        = init_flag("hint_match_once",        FALSE);
  p->print_matched_hints    = init_flag("print_matched_hints",    FALSE);
  p->print_derivations      = init_flag("print_derivations",      FALSE);
  p->derivations_only       = init_flag("derivations_only",        TRUE);
  p->print_new_hints        = init_flag("print_new_hints",        FALSE);
  p->dont_flip_input        = init_flag("dont_flip_input",        FALSE);

  p->echo_input             = init_flag("echo_input",              TRUE);
  p->bell                   = init_flag("bell",                    TRUE);
  p->quiet                  = init_flag("quiet",                  FALSE);
  p->print_initial_clauses  = init_flag("print_initial_clauses",   TRUE);
  p->print_given            = init_flag("print_given",             TRUE);
  p->print_gen              = init_flag("print_gen",              FALSE);
  p->print_kept             = init_flag("print_kept",             FALSE);
  p->print_labeled          = init_flag("print_labeled",          FALSE);
  p->print_proofs           = init_flag("print_proofs",            TRUE);
  p->print_proof_goal       = init_flag("print_proof_goal",       FALSE);
  p->default_output         = init_flag("default_output",          TRUE);
  p->print_clause_properties= init_flag("print_clause_properties",FALSE);

  p->expand_relational_defs = init_flag("expand_relational_defs", FALSE);
  p->predicate_elim         = init_flag("predicate_elim",          TRUE);
  p->inverse_order          = init_flag("inverse_order",           TRUE);
  p->sort_initial_sos       = init_flag("sort_initial_sos",       FALSE);
  p->restrict_denials       = init_flag("restrict_denials",       FALSE);

  p->input_sos_first        = init_flag("input_sos_first",         TRUE);
  p->breadth_first          = init_flag("breadth_first",          FALSE);
  p->lightest_first         = init_flag("lightest_first",         FALSE);
  p->random_given           = init_flag("random_given",           FALSE);
  p->breadth_first_hints    = init_flag("breadth_first_hints",    FALSE);
  p->default_parts          = init_flag("default_parts",           TRUE);

  p->automatic              = init_flag("auto",                    TRUE);
  p->auto_setup             = init_flag("auto_setup",              TRUE);
  p->auto_limits            = init_flag("auto_limits",             TRUE);
  p->auto_denials           = init_flag("auto_denials",            TRUE);
  p->auto_inference         = init_flag("auto_inference",          TRUE);
  p->auto_process           = init_flag("auto_process",            TRUE);
  p->auto2                  = init_flag("auto2",                  FALSE);
  p->raw                    = init_flag("raw",                    FALSE);
  p->production             = init_flag("production",             FALSE);

  p->lex_order_vars         = init_flag("lex_order_vars",         FALSE);
  p->comma_stats            = init_flag("comma_stats",            FALSE);
  p->report_index_stats     = init_flag("report_index_stats",     FALSE);

  p->checkpoint_exit        = init_flag("checkpoint_exit",        FALSE);
  p->checkpoint_ancestors   = init_flag("checkpoint_ancestors",    TRUE);
  p->checkpoint_verify      = init_flag("checkpoint_verify",      FALSE);
  p->tptp_output            = init_flag("tptp_output",            FALSE);
  p->multi_order_trial      = init_flag("multi_order_trial",      FALSE);
  p->fast_pred_elim         = init_flag("fast_pred_elim",         FALSE);

  // PARMS:
  //  internal name               external name      default    min      max

  p->max_given =        init_parm("max_given",            -1,     -1,INT_MAX);
  p->max_kept =         init_parm("max_kept",             -1,     -1,INT_MAX);
  p->max_proofs =       init_parm("max_proofs",            1,     -1,INT_MAX);
#ifdef __EMSCRIPTEN__
  p->max_megs =         init_parm("max_megs",           2048,     -1,   4096);
#else
  p->max_megs =         init_parm("max_megs",          49152,     -1,INT_MAX);
#endif
  p->cnf_clause_limit = init_parm("cnf_clause_limit",      0,      0,INT_MAX);
  p->definitional_cnf = init_parm("definitional_cnf",      0,      0,INT_MAX);
  p->max_seconds =      init_parm("max_seconds",          -1,     -1,INT_MAX);
  p->max_minutes =      init_parm("max_minutes",          -1,     -1,INT_MAX);
  p->max_hours =        init_parm("max_hours",          -1,     -1,INT_MAX);
  p->max_days =         init_parm("max_days",          -1,     -1,INT_MAX);

  p->new_constants =    init_parm("new_constants",         0,     -1,INT_MAX);
  p->para_lit_limit =   init_parm("para_lit_limit",       -1,     -1,INT_MAX);
  p->ur_nucleus_limit = init_parm("ur_nucleus_limit",     -1,     -1,INT_MAX);

  p->fold_denial_max =  init_parm("fold_denial_max",       0,     -1,INT_MAX);

  p->pick_given_ratio  = init_parm("pick_given_ratio",    -1,     -1,INT_MAX);
  p->hints_part        = init_parm("hints_part",     INT_MAX,      0,INT_MAX);
  p->age_part          = init_parm("age_part",             1,      0,INT_MAX);
  p->weight_part       = init_parm("weight_part",          0,      0,INT_MAX);
  p->false_part        = init_parm("false_part",           4,      0,INT_MAX);
  p->true_part         = init_parm("true_part",            4,      0,INT_MAX);
  p->random_part       = init_parm("random_part",          0,      0,INT_MAX);
  p->random_seed       = init_parm("random_seed",          0,     -1,INT_MAX);
  p->eval_limit        = init_parm("eval_limit",        1024,     -1,INT_MAX);
  p->eval_var_limit    = init_parm("eval_var_limit",      -1,     -1,INT_MAX);

  p->max_depth =        init_parm("max_depth",            -1,     -1,INT_MAX);
  p->lex_dep_demod_lim =init_parm("lex_dep_demod_lim",    11,     -1,INT_MAX);
  p->max_literals =     init_parm("max_literals",         -1,     -1,INT_MAX);
  p->max_vars =         init_parm("max_vars",             -1,     -1,INT_MAX);
  p->demod_step_limit = init_parm("demod_step_limit",   1000,     -1,INT_MAX);
  p->demod_increase_limit = init_parm("demod_increase_limit",1000,-1,INT_MAX);
  p->max_nohints  = init_parm("max_nohints",   -1, -1, INT_MAX);
  p->degrade_limit = init_parm("degrade_limit",  0, -1, INT_MAX);
  p->para_restr_beg = init_parm("para_restr_beg", INT_MAX, -1, INT_MAX);
  p->para_restr_end = init_parm("para_restr_end",      -1, -1, INT_MAX);
  p->backsub_check    = init_parm("backsub_check",       500,     -1,INT_MAX);

  p->variable_weight =  init_floatparm("variable_weight",       1.0,-DBL_LARGE,DBL_LARGE);
  p->constant_weight =  init_floatparm("constant_weight",       1.0,-DBL_LARGE,DBL_LARGE);
  p->not_weight =       init_floatparm("not_weight",            0.0,-DBL_LARGE,DBL_LARGE);
  p->or_weight =        init_floatparm("or_weight",             0.0,-DBL_LARGE,DBL_LARGE);
  p->sk_constant_weight=init_floatparm("sk_constant_weight",    1.0,-DBL_LARGE,DBL_LARGE);
  p->prop_atom_weight = init_floatparm("prop_atom_weight",      1.0,-DBL_LARGE,DBL_LARGE);
  p->nest_penalty =     init_floatparm("nest_penalty",          0.0,     0.0,DBL_LARGE);
  p->depth_penalty =    init_floatparm("depth_penalty",         0.0,-DBL_LARGE,DBL_LARGE);
  p->var_penalty =      init_floatparm("var_penalty",           0.0,-DBL_LARGE,DBL_LARGE);
  p->default_weight =   init_floatparm("default_weight",  DBL_LARGE,-DBL_LARGE,DBL_LARGE);
  p->complexity =       init_floatparm("complexity",            0.0,-DBL_LARGE,DBL_LARGE);
  p->sine_weight =      init_parm("sine_weight",               0,      0,INT_MAX);

  p->sos_limit =        init_parm("sos_limit",         20000,     -1,INT_MAX);
  p->sos_keep_factor =  init_parm("sos_keep_factor",       3,      2,10);
  p->min_sos_limit =    init_parm("min_sos_limit",         0,      0,INT_MAX);
  p->lrs_interval =     init_parm("lrs_interval",         50,      1,INT_MAX);
  p->lrs_ticks =        init_parm("lrs_ticks",            -1,     -1,INT_MAX);

  p->report =           init_parm("report",               -1,     -1,INT_MAX);
  p->report_stderr =    init_parm("report_stderr",        -1,     -1,INT_MAX);
  p->report_given =     init_parm("report_given",         -1,     -1,INT_MAX);
  p->report_preprocessing = init_parm("report_preprocessing", -1, -1,INT_MAX);
  p->fpa_depth =        init_parm("fpa_depth",            10,      1,    100);
  p->candidate_warn_limit = init_parm("candidate_warn_limit", -1,   -1,INT_MAX);
  p->candidate_hard_limit = init_parm("candidate_hard_limit", -1,   -1,INT_MAX);
  p->checkpoint_minutes = init_parm("checkpoint_minutes",    -1,     -1,INT_MAX);
  p->checkpoint_keep =    init_parm("checkpoint_keep",        3,      1,INT_MAX);
  p->sine =               init_parm("sine",                  -1,     -1,INT_MAX);
  p->sine_depth =         init_parm("sine_depth",             0,      0,INT_MAX);
  p->sine_max_axioms =    init_parm("sine_max_axioms",        0,      0,INT_MAX);
  p->cl_to_trace =        init_parm("cl_to_trace",            0,      0,INT_MAX);
  p->hint_derivations =   init_parm("hint_derivations",       0,      0,INT_MAX);
  p->cores =              init_parm("cores",                  0,      0,     64);
  p->hint_expiry =        init_parm("hint_expiry",           -1,     -1,INT_MAX);
  p->hint_sweep_interval = init_parm("hint_sweep_interval", 1000,     1,INT_MAX);
  p->hint_expiry_min =    init_parm("hint_expiry_min",       1,      1,INT_MAX);
  p->hints_fpa_depth =    init_parm("hints_fpa_depth",      10,      1,    100);
  p->fpa_hash_threshold = init_parm("fpa_hash_threshold",   4,      0,   1000);
  p->discrim_hash_threshold = init_parm("discrim_hash_threshold", -1,  -1,  1000);

  // FLOATPARMS:
  //  internal name      external name           default    min      max )

  p->max_weight =   init_floatparm("max_weight",  100.0, -DBL_LARGE, DBL_LARGE);

  // STRINGPARMS:
  // (internal-name, external-name, number-of-strings, str1, str2, ... )
  // str1 is always the default

  p->order = init_stringparm("order", 3,
			     "lpo",
			     "rpo",
			     "kbo");

  p->eq_defs = init_stringparm("eq_defs", 3,
			       "unfold",
			       "fold",
			       "pass");

  p->literal_selection = init_stringparm("literal_selection", 3,
					 "max_negative",
					 "all_negative",
					 "none");

  p->stats = init_stringparm("stats", 4,
			     "lots",
			     "some",
			     "all",
			     "none");

  p->multiple_interps = init_stringparm("multiple_interps", 2,
					"false_in_all",
					"false_in_some");

  // Flag and parm Dependencies.  These cause other flags and parms
  // to be changed.  The changes happen immediately and can be undone
  // by later settings in the input.
  // DEPENDENCIES ARE NOT APPLIED TO DEFAULT SETTINGS!!!

  parm_parm_dependency(p->max_minutes, p->max_seconds,         60, TRUE);
  parm_parm_dependency(p->max_hours,   p->max_seconds,       3600, TRUE);
  parm_parm_dependency(p->max_days,    p->max_seconds,      86400, TRUE);

  flag_parm_dependency(p->para_units_only,    TRUE,  p->para_lit_limit,      1);
  flag_parm_dep_default(p->para_units_only,   FALSE, p->para_lit_limit);

  flag_flag_dependency(p->hyper_resolution, TRUE,  p->pos_hyper_resolution, TRUE);
  flag_flag_dependency(p->hyper_resolution, FALSE, p->pos_hyper_resolution, FALSE);

  flag_flag_dependency(p->ur_resolution, TRUE,  p->pos_ur_resolution, TRUE);
  flag_flag_dependency(p->ur_resolution, TRUE,  p->neg_ur_resolution, TRUE);
  flag_flag_dependency(p->ur_resolution, FALSE,  p->pos_ur_resolution, FALSE);
  flag_flag_dependency(p->ur_resolution, FALSE,  p->neg_ur_resolution, FALSE);

  flag_parm_dependency(p->lex_dep_demod, FALSE, p->lex_dep_demod_lim, 0);
  flag_parm_dependency(p->lex_dep_demod,  TRUE, p->lex_dep_demod_lim, 11);

  /***********************/

  parm_parm_dependency(p->pick_given_ratio, p->age_part,          1, FALSE);
  parm_parm_dependency(p->pick_given_ratio, p->weight_part,       1,  TRUE);
  parm_parm_dependency(p->pick_given_ratio, p->false_part,        0, FALSE);
  parm_parm_dependency(p->pick_given_ratio, p->true_part,         0, FALSE);
  parm_parm_dependency(p->pick_given_ratio, p->random_part,       0, FALSE);

  flag_parm_dependency(p->lightest_first,    TRUE,  p->weight_part,     1);
  flag_parm_dependency(p->lightest_first,    TRUE,  p->age_part,        0);
  flag_parm_dependency(p->lightest_first,    TRUE,  p->false_part,      0);
  flag_parm_dependency(p->lightest_first,    TRUE,  p->true_part,       0);
  flag_parm_dependency(p->lightest_first,    TRUE,  p->random_part,     0);
  flag_flag_dependency(p->lightest_first,   FALSE,  p->default_parts, TRUE);

  flag_parm_dependency(p->random_given,    TRUE,  p->weight_part,     0);
  flag_parm_dependency(p->random_given,    TRUE,  p->age_part,        0);
  flag_parm_dependency(p->random_given,    TRUE,  p->false_part,      0);
  flag_parm_dependency(p->random_given,    TRUE,  p->true_part,       0);
  flag_parm_dependency(p->random_given,    TRUE,  p->random_part,     1);
  flag_flag_dependency(p->random_given,   FALSE,  p->default_parts, TRUE);

  flag_parm_dependency(p->breadth_first,    TRUE,  p->age_part,        1);
  flag_parm_dependency(p->breadth_first,    TRUE,  p->weight_part,     0);
  flag_parm_dependency(p->breadth_first,    TRUE,  p->false_part,      0);
  flag_parm_dependency(p->breadth_first,    TRUE,  p->true_part,       0);
  flag_parm_dependency(p->breadth_first,    TRUE,  p->random_part,     0);
  flag_flag_dependency(p->breadth_first,    FALSE, p->default_parts, TRUE);

  /* flag_parm_dependency(p->default_parts, TRUE,  p->hints_part, INT_MAX); */
  flag_parm_dependency(p->default_parts,    TRUE,  p->age_part,          1);
  flag_parm_dependency(p->default_parts,    TRUE,  p->weight_part,       0);
  flag_parm_dependency(p->default_parts,    TRUE,  p->false_part,        4);
  flag_parm_dependency(p->default_parts,    TRUE,  p->true_part,         4);
  flag_parm_dependency(p->default_parts,    TRUE,  p->random_part,       0);

  /* flag_parm_dependency(p->default_parts,    FALSE,  p->hints_part,  0); */
  flag_parm_dependency(p->default_parts,    FALSE,  p->age_part,         0);
  flag_parm_dependency(p->default_parts,    FALSE,  p->weight_part,      0);
  flag_parm_dependency(p->default_parts,    FALSE,  p->false_part,       0);
  flag_parm_dependency(p->default_parts,    FALSE,  p->true_part,        0);
  flag_parm_dependency(p->default_parts,    FALSE,  p->random_part,      0);

  /***********************/

  flag_flag_dependency(p->default_output, TRUE, p->quiet,               FALSE);
  flag_flag_dependency(p->default_output, TRUE, p->echo_input,           TRUE);
  flag_flag_dependency(p->default_output, TRUE, p->print_initial_clauses,TRUE);
  flag_flag_dependency(p->default_output, TRUE, p->print_given,          TRUE);
  flag_flag_dependency(p->default_output, TRUE, p->print_proofs,         TRUE);
  flag_stringparm_dependency(p->default_output, TRUE, p->stats,        "lots");

  flag_flag_dependency(p->default_output, TRUE, p->print_kept,          FALSE);
  flag_flag_dependency(p->default_output, TRUE, p->print_gen,           FALSE);
  flag_flag_dependency(p->default_output, TRUE, p->print_matched_hints, FALSE);

  // auto_setup

  flag_flag_dependency(p->auto_setup,  TRUE, p->predicate_elim,    TRUE);
  flag_stringparm_dependency(p->auto_setup, TRUE, p->eq_defs,    "unfold");

  flag_flag_dependency(p->auto_setup,  FALSE, p->predicate_elim,    FALSE);
  flag_stringparm_dependency(p->auto_setup, FALSE, p->eq_defs,   "pass");

  // auto_limits

  flag_floatparm_dependency(p->auto_limits,  TRUE, p->max_weight,    100.0);
  flag_parm_dependency(p->auto_limits,       TRUE, p->sos_limit,        -1);

  flag_floatparm_dependency(p->auto_limits, FALSE, p->max_weight, DBL_LARGE);
  flag_parm_dependency(p->auto_limits,      FALSE, p->sos_limit,         -1);

  // automatic

  flag_flag_dependency(p->automatic,       TRUE, p->auto_inference,     TRUE);
  flag_flag_dependency(p->automatic,       TRUE, p->auto_setup,         TRUE);
  flag_flag_dependency(p->automatic,       TRUE, p->auto_limits,        TRUE);
  flag_flag_dependency(p->automatic,       TRUE, p->auto_denials,       TRUE);
  flag_flag_dependency(p->automatic,       TRUE, p->auto_process,       TRUE);

  flag_flag_dependency(p->automatic,       FALSE, p->auto_inference,    FALSE);
  flag_flag_dependency(p->automatic,       FALSE, p->auto_setup,        FALSE);
  flag_flag_dependency(p->automatic,       FALSE, p->auto_limits,       FALSE);
  flag_flag_dependency(p->automatic,       FALSE, p->auto_denials,      FALSE);
  flag_flag_dependency(p->automatic,       FALSE, p->auto_process,      FALSE);

  // auto2  (also triggered by -x on the command line)

  flag_flag_dependency(p->auto2, TRUE, p->automatic,                 TRUE);
  flag_parm_dependency(p->auto2, TRUE, p->new_constants,            1);
  flag_parm_dependency(p->auto2, TRUE, p->fold_denial_max,          3);
  flag_floatparm_dependency(p->auto2, TRUE, p->max_weight,      200.0);
  flag_parm_dependency(p->auto2, TRUE, p->nest_penalty,             1);
  flag_parm_dependency(p->auto2, TRUE, p->sk_constant_weight,       0);
  flag_parm_dependency(p->auto2, TRUE, p->prop_atom_weight,         5);
  flag_flag_dependency(p->auto2, TRUE, p->sort_initial_sos,       TRUE);
  flag_parm_dependency(p->auto2, TRUE, p->sos_limit,                -1);
  flag_parm_dependency(p->auto2, TRUE, p->lrs_ticks,              3000);
  flag_parm_dependency(p->auto2, TRUE, p->max_megs,                400);
  flag_stringparm_dependency(p->auto2, TRUE, p->stats,          "some");
  flag_flag_dependency(p->auto2, TRUE, p->echo_input,            FALSE);
  flag_flag_dependency(p->auto2, TRUE, p->quiet,                  TRUE);
  flag_flag_dependency(p->auto2, TRUE, p->print_initial_clauses, FALSE);
  flag_flag_dependency(p->auto2, TRUE, p->print_given,           FALSE);

  flag_flag_dep_default(p->auto2, FALSE, p->automatic);
  flag_parm_dep_default(p->auto2, FALSE, p->new_constants);
  flag_parm_dep_default(p->auto2, FALSE, p->fold_denial_max);
  flag_floatparm_dep_default(p->auto2, FALSE, p->max_weight);
  flag_parm_dep_default(p->auto2, FALSE, p->nest_penalty);
  flag_parm_dep_default(p->auto2, FALSE, p->sk_constant_weight);
  flag_parm_dep_default(p->auto2, FALSE, p->prop_atom_weight);
  flag_flag_dep_default(p->auto2, FALSE, p->sort_initial_sos);
  flag_parm_dep_default(p->auto2, FALSE, p->sos_limit);
  flag_parm_dep_default(p->auto2, FALSE, p->lrs_ticks);
  flag_parm_dep_default(p->auto2, FALSE, p->max_megs);
  flag_stringparm_dep_default(p->auto2, FALSE, p->stats);
  flag_flag_dep_default(p->auto2, FALSE, p->echo_input);
  flag_flag_dep_default(p->auto2, FALSE, p->quiet);
  flag_flag_dep_default(p->auto2, FALSE, p->print_initial_clauses);
  flag_flag_dep_default(p->auto2, FALSE, p->print_given);

  // tptp_output — suppress native output, TSTP proof is printed separately.

  flag_flag_dependency(p->tptp_output, TRUE, p->default_output,        FALSE);
  flag_flag_dependency(p->tptp_output, TRUE, p->quiet,                  TRUE);
  flag_flag_dependency(p->tptp_output, TRUE, p->echo_input,            FALSE);
  flag_flag_dependency(p->tptp_output, TRUE, p->print_initial_clauses, FALSE);
  flag_flag_dependency(p->tptp_output, TRUE, p->print_given,           FALSE);
  flag_flag_dependency(p->tptp_output, TRUE, p->bell,                  FALSE);
  flag_stringparm_dependency(p->tptp_output, TRUE, p->stats,         "none");

  flag_flag_dep_default(p->tptp_output, FALSE, p->quiet);
  flag_flag_dep_default(p->tptp_output, FALSE, p->echo_input);
  flag_flag_dep_default(p->tptp_output, FALSE, p->print_initial_clauses);
  flag_flag_dep_default(p->tptp_output, FALSE, p->print_given);
  flag_flag_dep_default(p->tptp_output, FALSE, p->bell);
  flag_stringparm_dep_default(p->tptp_output, FALSE, p->stats);

  // raw

  flag_flag_dependency(p->raw, TRUE, p->automatic,           FALSE);
  flag_flag_dependency(p->raw, TRUE, p->ordered_res,         FALSE);
  flag_flag_dependency(p->raw, TRUE, p->ordered_para,        FALSE);
  flag_flag_dependency(p->raw, TRUE, p->para_into_vars,      TRUE);
  flag_flag_dependency(p->raw, TRUE, p->para_from_small,     TRUE);
  flag_flag_dependency(p->raw, TRUE, p->ordered_para,        FALSE);
  flag_flag_dependency(p->raw, TRUE, p->back_demod,          FALSE);
  flag_flag_dependency(p->raw, TRUE, p->cac_redundancy,      FALSE);
  flag_parm_dependency(p->raw, TRUE, p->backsub_check,     INT_MAX);
  flag_flag_dependency(p->raw, TRUE, p->lightest_first,       TRUE);
  flag_stringparm_dependency(p->raw, TRUE, p->literal_selection, "none");
  
  flag_flag_dep_default(p->raw, FALSE, p->automatic);
  flag_flag_dep_default(p->raw, FALSE, p->ordered_res);
  flag_flag_dep_default(p->raw, FALSE, p->ordered_para);
  flag_flag_dep_default(p->raw, FALSE, p->para_into_vars);
  flag_flag_dep_default(p->raw, FALSE, p->para_from_small);
  flag_flag_dep_default(p->raw, FALSE, p->ordered_para);
  flag_flag_dep_default(p->raw, FALSE, p->back_demod);
  flag_flag_dep_default(p->raw, FALSE, p->cac_redundancy);
  flag_parm_dep_default(p->raw, FALSE, p->backsub_check);
  flag_flag_dep_default(p->raw, FALSE, p->lightest_first);
  flag_stringparm_dep_default(p->raw, FALSE, p->literal_selection);

  // production mode

  flag_flag_dependency(p->production,   TRUE,  p->raw,               TRUE);
  flag_flag_dependency(p->production,   TRUE,  p->eval_rewrite,      TRUE);
  flag_flag_dependency(p->production,   TRUE,  p->hyper_resolution,  TRUE);
  flag_flag_dependency(p->production,   TRUE,  p->back_subsume,     FALSE);
  
  return p;
  
}  // init_prover_options

/*************
 *
 *   init_prover_attributes()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_prover_attributes(void)
{
  Att.label            = register_attribute("label",        STRING_ATTRIBUTE);
  Att.bsub_hint_wt     = register_attribute("bsub_hint_wt",    INT_ATTRIBUTE);
  Att.answer           = register_attribute("answer",         TERM_ATTRIBUTE);
  Att.properties       = register_attribute("props",          TERM_ATTRIBUTE);

  Att.action           = register_attribute("action",         TERM_ATTRIBUTE);
  Att.action2          = register_attribute("action2",        TERM_ATTRIBUTE);

  declare_term_attribute_inheritable(Att.answer);
  declare_term_attribute_inheritable(Att.action2);
}  // Init_prover_attributes

/*************
 *
 *   get_attrib_id()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int get_attrib_id(char *str)
{
  if (str_ident(str, "label"))
    return Att.label;
  else if (str_ident(str, "bsub_hint_wt"))
    return Att.bsub_hint_wt;
  else if (str_ident(str, "answer"))
    return Att.answer;
  else if (str_ident(str, "action"))
    return Att.action;
  else if (str_ident(str, "action2"))
    return Att.action2;
  else {
    fatal_error("get_attrib_id, unknown attribute string");
    return -1;
  }
}  /* get_attrib_id */

/*************
 *
 *   update_stats()
 *
 *************/

static
void update_stats(void)
{
  Stats.demod_attempts = demod_attempts() + fdemod_attempts();
  Stats.demod_rewrites = demod_rewrites() + fdemod_rewrites();
  Stats.res_instance_prunes = res_instance_prunes();
  Stats.para_instance_prunes = para_instance_prunes();
  Stats.basic_para_prunes = basic_paramodulation_prunes();
  Stats.sos_removed = 0; // control_sos_removed();
  Stats.nonunit_fsub = nonunit_fsub_tests();
  Stats.nonunit_bsub = nonunit_bsub_tests();
  Stats.usable_size = Glob.usable ? Glob.usable->length : 0;
  Stats.sos_size = Glob.sos ? Glob.sos->length : 0;
  Stats.demodulators_size = Glob.demods ? Glob.demods->length : 0;
  Stats.limbo_size = Glob.limbo ? Glob.limbo->length : 0;
  Stats.disabled_size = Glob.disabled ? Glob.disabled->length : 0;
  Stats.hints_size = Glob.hints ? Glob.hints->length : 0;
  Stats.kbyte_usage = bytes_palloced() / 1000;
}  /* update_stats */

/*************
 *
 *   fprint_prover_stats()
 *
 *************/

static
void fprint_prover_stats(FILE *fp, struct prover_stats s, char *stats_level)
{
  fprintf(fp,"\nGiven=%s. Generated=%s. Kept=%s. proofs=%s.\n",
	  comma_num(s.given), comma_num(s.generated),
	  comma_num(s.kept), comma_num(s.proofs));
  fprintf(fp,"Usable=%s. Sos=%s. Demods=%s. Limbo=%s, "
	  "Disabled=%s. Hints=%s. Active_Hints=%s.\n",
	  comma_num(s.usable_size), comma_num(s.sos_size),
	  comma_num(s.demodulators_size), comma_num(s.limbo_size),
	  comma_num(s.disabled_size), comma_num(s.hints_size),
	  comma_num(active_hints()));

  if (str_ident(stats_level, "lots") || str_ident(stats_level, "all")) {

    fprintf(fp,"Kept_by_rule=%s, Deleted_by_rule=%s.\n",
	    comma_num(s.kept_by_rule), comma_num(s.deleted_by_rule));
    fprintf(fp,"Forward_subsumed=%s. Back_subsumed=%s.\n",
	    comma_num(s.subsumed), comma_num(s.back_subsumed));
    fprintf(fp,"Sos_limit_deleted=%s. Sos_displaced=%s. Sos_removed=%s.\n",
	    comma_num(s.sos_limit_deleted), comma_num(s.sos_displaced),
	    comma_num(s.sos_removed));
    fprintf(fp,"New_demodulators=%s (%s lex), Back_demodulated=%s. Back_unit_deleted=%s.\n",
	    comma_num(s.new_demodulators), comma_num(s.new_lex_demods),
	    comma_num(s.back_demodulated), comma_num(s.back_unit_deleted));
    fprintf(fp,"Demod_attempts=%s. Demod_rewrites=%s.\n",
	    comma_num(s.demod_attempts), comma_num(s.demod_rewrites));
    fprintf(fp,"Res_instance_prunes=%s. Para_instance_prunes=%s. Basic_paramod_prunes=%s.\n",
	    comma_num(s.res_instance_prunes), comma_num(s.para_instance_prunes),
	    comma_num(s.basic_para_prunes));
    fprintf(fp,"Nonunit_fsub_feature_tests=%s. ", comma_num(s.nonunit_fsub));
    fprintf(fp,"Nonunit_bsub_feature_tests=%s.\n", comma_num(s.nonunit_bsub));
    if (mindex_queries_skipped() > 0 || mindex_queries_warned() > 0) {
      fprintf(fp,"Candidate_limits: warned=%s, skipped=%s.\n",
              comma_num(mindex_queries_warned()),
              comma_num(mindex_queries_skipped()));
    }
  }

  fprintf(fp,"Max_Clause_ID=%s.\n", comma_num(clause_ids_assigned()));
  fprintf(fp,"Megabytes=%.2f.\n", s.kbyte_usage / 1000.0);

  fprintf(fp,"User_CPU=%.2f, System_CPU=%.2f, Wall_clock=%u.\n",
	  user_seconds(), system_seconds(), wallclock());
}  /* fprint_prover_stats */

/*************
 *
 *   fprint_prover_clocks()
 *
 *************/

/* DOCUMENTATION
Given an arroy of clock values (type double) indexed by
the ordinary clock indexes, print a report to a file.
*/

/* PUBLIC */
void fprint_prover_clocks(FILE *fp, struct prover_clocks clks)
{
  if (clocks_enabled()) {
    fprintf(fp, "\n");
    fprint_clock(fp, clks.pick_given);
    fprint_clock(fp, clks.infer);
    fprint_clock(fp, clks.preprocess);
    fprint_clock(fp, clks.demod);
    fprint_clock(fp, clks.unit_del);
    fprint_clock(fp, clks.redundancy);
    fprint_clock(fp, clks.conflict);
    fprint_clock(fp, clks.weigh);
    fprint_clock(fp, clks.hints);
    fprint_clock(fp, clks.subsume);
    fprint_clock(fp, clks.semantics);
    fprint_clock(fp, clks.back_subsume);
    fprint_clock(fp, clks.back_demod);
    fprint_clock(fp, clks.back_unit_del);
    fprint_clock(fp, clks.index);
    fprint_clock(fp, clks.disable);
  }
}  /* fprint_prover_clocks */

/*************
 *
 *   fprint_all_stats()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void fprint_all_stats(FILE *fp, char *stats_level)
{
  /* In TPTP output mode, suppress statistics on stdout */
  if (Opt && flag(Opt->tptp_output) && fp == stdout)
    return;

  update_stats();

  print_separator(fp, "STATISTICS", TRUE);

  fprint_prover_stats(fp, Stats, stats_level);

  fprint_prover_clocks(fp, Clocks);

  if (!clist_empty(Glob.hints))
    print_hint_match_stats(fp, Glob.hints);

  if (str_ident(stats_level, "all")) {
    print_memory_stats(fp);
    selector_report();
    /* p_sos_dist(); */
  }
  print_separator(fp, "end of statistics", TRUE);
  fflush(fp);
}  // fprint_all_stats

/*************
 *
 *   exit_string()
 *
 *************/

static
char *exit_string(int code)
{
  char *message;
  switch (code) {
  case MAX_PROOFS_EXIT:  message = "max_proofs";  break;
  case FATAL_EXIT:       message = "fatal_error"; break;
  case SOS_EMPTY_EXIT:   message = "sos_empty";   break;
  case MAX_MEGS_EXIT:    message = "max_megs";    break;
  case MAX_SECONDS_EXIT: message = "max_seconds"; break;
  case MAX_GIVEN_EXIT:   message = "max_given";   break;
  case MAX_KEPT_EXIT:    message = "max_kept";    break;
  case ACTION_EXIT:      message = "action";      break;
  case MAX_NOHINTS_EXIT: message = "max_nohints"; break;
  case SIGSEGV_EXIT:     message = "SIGSEGV";     break;
  case SIGINT_EXIT:      message = "SIGINT";      break;
  case SIGTERM_EXIT:     message = "SIGTERM";     break;
  case CHECKPOINT_EXIT:  message = "checkpoint";  break;
  default: message = "???";
  }
  return message;
}  /* exit_string */

/*************
 *
 *   szs_status_string()
 *
 *   Map Prover9 exit code to SZS status string.
 *
 *************/

static
char *szs_status_string(int code)
{
  switch (code) {
  case MAX_PROOFS_EXIT:
    return Glob.has_goals ? "Theorem" : "Unsatisfiable";
  case SOS_EMPTY_EXIT:
    return "GaveUp";
  case MAX_SECONDS_EXIT:
    return "Timeout";
  case MAX_MEGS_EXIT:
    return "MemoryOut";
  case MAX_GIVEN_EXIT:
  case MAX_KEPT_EXIT:
  case ACTION_EXIT:
  case MAX_NOHINTS_EXIT:
    return "GaveUp";
  case SIGSEGV_EXIT:
  case FATAL_EXIT:
    return "Error";
  case SIGINT_EXIT:
  case SIGTERM_EXIT:
    return "User";
  case CHECKPOINT_EXIT:
    return "Unknown";
  default:
    return "Unknown";
  }
}  /* szs_status_string */

/*************
 *
 *   fprint_clause_tptp()
 *
 *   Print one clause in TSTP annotated formula format.
 *   Format:  cnf(c_ID, role, (literals), source).
 *
 *************/

/*************
 *
 *   fwrite_term_tptp()
 *
 *   Write a term, but replace the LADR "-" (negation) symbol with
 *   TPTP "~" for TSTP compliance.  We use sb_write_term to get
 *   the string, then do the replacement.
 *
 *************/

static
void fwrite_term_tptp(FILE *fp, Term t)
{
  String_buf sb = get_string_buf();
  char *s;
  int i;

  sb_write_term(sb, t);
  s = sb_to_malloc_string(sb);
  zap_string_buf(sb);

  /* Replace "-" that acts as negation (prefix operator) with "~".
     In LADR clause output, negation is printed as "-atom" (no space).
     Negation appears at start of string or after " | " (disjunction).
     We detect it by position context: beginning or after a disjunction
     separator, followed by a letter (predicate) or "(". */
  for (i = 0; s[i] != '\0'; i++) {
    if (s[i] == '-') {
      /* Is this at a negation position? */
      BOOL at_neg_pos = (i == 0 ||
                         (i >= 2 && s[i-1] == ' ' && s[i-2] == '|') ||
                         s[i-1] == '(');
      /* Is the next char a letter or open-paren (i.e., start of an atom)? */
      BOOL before_atom = (s[i+1] != '\0' &&
                          (s[i+1] == '(' ||
                           (s[i+1] >= 'a' && s[i+1] <= 'z') ||
                           (s[i+1] >= 'A' && s[i+1] <= 'Z') ||
                           s[i+1] == '$'));
      if (at_neg_pos && before_atom)
        fputc('~', fp);
      else
        fputc('-', fp);
    }
    else
      fputc(s[i], fp);
  }
  safe_free(s);  /* safe_malloc'd by sb_to_malloc_string */
}

/*************
 *
 *   fwrite_formula_tptp()
 *
 *   Recursively print a Formula in TPTP syntax.
 *   Quantifiers: ! [X,Y,Z] : (body), ? [X] : (body)
 *   Connectives: ~, &, |, =>, <=>
 *   Atoms: printed via fwrite_term_tptp (handles - to ~ replacement).
 *
 *************/

static
void fwrite_formula_tptp(FILE *fp, Formula f)
{
  if (f->type == ATOM_FORM) {
    fwrite_term_tptp(fp, f->atom);
  }
  else if (f->type == NOT_FORM) {
    fprintf(fp, "~ (");
    fwrite_formula_tptp(fp, f->kids[0]);
    fprintf(fp, ")");
  }
  else if (f->type == AND_FORM) {
    if (f->arity == 0)
      fprintf(fp, "$true");
    else {
      int i;
      fprintf(fp, "(");
      for (i = 0; i < f->arity; i++) {
        if (i > 0) fprintf(fp, " & ");
        fwrite_formula_tptp(fp, f->kids[i]);
      }
      fprintf(fp, ")");
    }
  }
  else if (f->type == OR_FORM) {
    if (f->arity == 0)
      fprintf(fp, "$false");
    else {
      int i;
      fprintf(fp, "(");
      for (i = 0; i < f->arity; i++) {
        if (i > 0) fprintf(fp, " | ");
        fwrite_formula_tptp(fp, f->kids[i]);
      }
      fprintf(fp, ")");
    }
  }
  else if (f->type == IMP_FORM) {
    fprintf(fp, "(");
    fwrite_formula_tptp(fp, f->kids[0]);
    fprintf(fp, " => ");
    fwrite_formula_tptp(fp, f->kids[1]);
    fprintf(fp, ")");
  }
  else if (f->type == IMPBY_FORM) {
    fprintf(fp, "(");
    fwrite_formula_tptp(fp, f->kids[1]);
    fprintf(fp, " => ");
    fwrite_formula_tptp(fp, f->kids[0]);
    fprintf(fp, ")");
  }
  else if (f->type == IFF_FORM) {
    fprintf(fp, "(");
    fwrite_formula_tptp(fp, f->kids[0]);
    fprintf(fp, " <=> ");
    fwrite_formula_tptp(fp, f->kids[1]);
    fprintf(fp, ")");
  }
  else if (f->type == ALL_FORM) {
    /* Collect consecutive universal quantifiers */
    Formula body = f;
    BOOL first = TRUE;
    fprintf(fp, "! [");
    while (body->type == ALL_FORM) {
      if (!first) fprintf(fp, ",");
      fprintf(fp, "%s", body->qvar);
      first = FALSE;
      body = body->kids[0];
    }
    fprintf(fp, "] : (");
    fwrite_formula_tptp(fp, body);
    fprintf(fp, ")");
  }
  else if (f->type == EXISTS_FORM) {
    /* Collect consecutive existential quantifiers */
    Formula body = f;
    BOOL first = TRUE;
    fprintf(fp, "? [");
    while (body->type == EXISTS_FORM) {
      if (!first) fprintf(fp, ",");
      fprintf(fp, "%s", body->qvar);
      first = FALSE;
      body = body->kids[0];
    }
    fprintf(fp, "] : (");
    fwrite_formula_tptp(fp, body);
    fprintf(fp, ")");
  }
}

static
void fprint_clause_tptp(FILE *fp, Topform c, BOOL flatten_fof)
{
  Just just = c->justification;
  Just_type primary_type = just ? just->type : UNKNOWN_JUST;
  BOOL is_fof = c->is_formula;

  /* When flatten_fof is set, FOF axioms and conjectures are omitted
     from the proof and their CNF children become leaf nodes.  This
     avoids GDV equisatisfiability failures from Skolemization +
     multi-clause clausification / assume_negation steps. */

  if (flatten_fof && is_fof &&
      (primary_type == INPUT_JUST || primary_type == GOAL_JUST))
    return;  /* skip FOF entries — their CNF children become leaves */

  /* If this clause was clausified from a skipped FOF axiom, emit it
     as an axiom leaf instead of an inference step. */
  BOOL promote_to_axiom = FALSE;
  if (flatten_fof && primary_type == CLAUSIFY_JUST) {
    Ilist parents = get_parents(just, FALSE);  /* primary parent only */
    if (parents) {
      Topform parent = find_clause_by_id(parents->i);
      if (parent && parent->is_formula &&
	  parent->justification && parent->justification->type == INPUT_JUST)
	promote_to_axiom = TRUE;
      zap_ilist(parents);
    }
  }

  /* If this clause is a denial of a skipped FOF conjecture, emit it
     as a negated_conjecture leaf instead of an inference step. */
  BOOL promote_to_neg_conj = FALSE;
  if (flatten_fof && primary_type == DENY_JUST) {
    Ilist parents = get_parents(just, FALSE);
    if (parents) {
      Topform parent = find_clause_by_id(parents->i);
      if (parent && parent->is_formula &&
	  parent->justification && parent->justification->type == GOAL_JUST)
	promote_to_neg_conj = TRUE;
      zap_ilist(parents);
    }
  }

  /* Print: fof/cnf(c_ID, role, */
  fprintf(fp, "%s(c_%llu, ", is_fof ? "fof" : "cnf", c->id);

  /* Determine role */
  if (primary_type == INPUT_JUST || promote_to_axiom)
    fprintf(fp, "axiom, ");
  else if (primary_type == GOAL_JUST || promote_to_neg_conj)
    fprintf(fp, "negated_conjecture, ");
  else
    fprintf(fp, "plain, ");

  /* Print the formula/clause body */
  if (is_fof && c->formula != NULL) {
    /* FOF: use the recursive TPTP formula printer for proper syntax */
    fwrite_formula_tptp(fp, c->formula);
  }
  else {
    Term t = topform_to_term_without_attributes(c);
    if (c->literals == NULL)
      fprintf(fp, "$false");
    else
      fwrite_term_tptp(fp, t);
    if (t)
      zap_term(t);
  }

  /* Print the source/inference annotation.
     If the clause carries a tptp_name attribute (from TPTP input parsing),
     emit file() or inference(clausify) to preserve provenance. */
  {
    int tna = get_tptp_name_attr();
    char *tptp_name = get_string_attribute(c->attributes, tna, 1);

    if (tptp_name && (primary_type == INPUT_JUST ||
                       primary_type == GOAL_JUST)) {
      /* Direct input with known TPTP name */
      fprintf(fp, ", file('%s',%s)).\n", "tptp_input", tptp_name);
    }
    else if (tptp_name && (promote_to_axiom || promote_to_neg_conj)) {
      /* Clausified from a skipped FOF: use file() since the FOF parent
         is not in the proof output (flatten_fof omitted it). */
      fprintf(fp, ", file('%s',%s)).\n", "tptp_input", tptp_name);
    }
    else if (tptp_name && (primary_type == CLAUSIFY_JUST ||
                           primary_type == DENY_JUST)) {
      /* Clausified from a named FOF that IS in the proof output */
      fprintf(fp, ", inference(clausify, [status(esa)], [%s])).\n",
              tptp_name);
    }
    else if (primary_type == INPUT_JUST || promote_to_axiom ||
             promote_to_neg_conj) {
      fprintf(fp, ", introduced(assumption,[])).\n");
    }
    else if (primary_type == GOAL_JUST) {
      fprintf(fp, ", introduced(conjecture,[])).\n");
    }
    else {
    /* Inference step: inference(rule, [status(thm)], [parents]) */
    const char *rule = tptp_rule_name(primary_type);

    fprintf(fp, ",\n    inference(%s, [status(thm)], [", rule);

    /* Collect ALL parent IDs (primary + secondary justification nodes) */
    {
      Ilist parents = get_parents(just, TRUE);
      Ilist p;
      BOOL first = TRUE;
      for (p = parents; p; p = p->next) {
        if (!first)
          fprintf(fp, ", ");
        fprintf(fp, "c_%d", p->i);
        first = FALSE;
      }
      zap_ilist(parents);
    }

    fprintf(fp, "])).\n");
    }
  }
}  /* fprint_clause_tptp */

/*************
 *
 *   fprint_proof_tptp()
 *
 *   Print a complete proof in TSTP format with SZS output delimiters.
 *
 *************/

static
void fprint_proof_tptp(FILE *fp, Plist proof)
{
  Plist p;
  Variable_style orig_style = variable_style();

  if (Glob.problem_name)
    fprintf(fp, "%% SZS output start CNFRefutation for %s\n", Glob.problem_name);
  else
    fprintf(fp, "%% SZS output start CNFRefutation\n");

  /* Check if proof contains FOF entries (axioms or conjectures).
     If so, flatten the FOF layer: skip FOF entries and promote their
     CNF children (clausify, deny) to leaf nodes.  This avoids GDV
     verification failures from Skolemization + multi-clause
     clausification / assume_negation steps. */
  BOOL has_fof = FALSE;
  for (p = proof; p && !has_fof; p = p->next) {
    Topform c = (Topform) p->v;
    if (c->is_formula && c->justification &&
	(c->justification->type == INPUT_JUST ||
	 c->justification->type == GOAL_JUST))
      has_fof = TRUE;
  }

  for (p = proof; p; p = p->next) {
    Topform c = (Topform) p->v;
    if (c->is_formula) {
      set_variable_style(orig_style);
    }
    else {
      /* CNF: use PROLOG_STYLE for uppercase TPTP variables. */
      set_variable_style(PROLOG_STYLE);
    }
    fprint_clause_tptp(fp, c, has_fof);
  }

  set_variable_style(orig_style);
  if (Glob.problem_name)
    fprintf(fp, "%% SZS output end CNFRefutation for %s\n", Glob.problem_name);
  else
    fprintf(fp, "%% SZS output end CNFRefutation\n");
}  /* fprint_proof_tptp */

/*************
 *
 *   print_exit_message()
 *
 *   Print the exit/status message to fp and flush, but do NOT
 *   call exit().  Used by child_exit() in fork children.
 *
 *************/

/* PUBLIC */
void print_exit_message(FILE *fp, int code)
{
  int proofs = Glob.initialized ? Stats.proofs : -1;

  if (Opt && flag(Opt->tptp_output)) {
    /* TPTP/SZS output mode */
    if (Glob.problem_name)
      fprintf(fp, "\n%% SZS status %s for %s\n",
	      szs_status_string(code), Glob.problem_name);
    else
      fprintf(fp, "\n%% SZS status %s\n", szs_status_string(code));

    if (!Opt || !flag(Opt->quiet)) {
      fflush(stdout);
      fprintf(stderr, "\n------ process %d exit (%s) ------\n",
	      my_process_id(), exit_string(code));
      if (!Opt || flag(Opt->bell))
        bell(stderr);
    }

    if (Opt && parm(Opt->report_stderr) > 0)
      report(stderr, "some");

    /* Print memory logging summary if logging was enabled */
    if (!flag(Opt->quiet))
      memory_logging_summary(stderr);

    fflush(fp);
    fflush(stderr);
    return;
  }

  /* Native Prover9 output mode */
  if (proofs == -1)
    fprintf(fp, "\nExiting.\n");
  else if (proofs == 0)
    fprintf(fp, "\nExiting with failure.\n");
  else
    fprintf(fp, "\nExiting with %d proof%s.\n",
	    proofs, proofs == 1 ? "" : "s");

  if (!Opt || !flag(Opt->quiet)) {
    fflush(stdout);
    fprintf(stderr, "\n------ process %d exit (%s) ------\n",
	    my_process_id(), exit_string(code));
    if (!Opt || flag(Opt->bell))
      bell(stderr);
  }

  if (Opt && parm(Opt->report_stderr) > 0)
    report(stderr, "some");

  fprintf(fp, "\nProcess %d exit (%s) %s",
	  my_process_id(), exit_string(code), get_date());

  /* Print memory logging summary if logging was enabled */
  if (!Opt || !flag(Opt->quiet))
    memory_logging_summary(stderr);

  fflush(fp);
  fflush(stderr);
}  /* print_exit_message */

/*************
 *
 *   exit_with_message()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void exit_with_message(FILE *fp, int code)
{
  set_no_kill();  /* protect exit output from signal truncation */
  print_exit_message(fp, code);
  exit(code);
}  /* exit_with_message */

/*************
 *
 *   report()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void report(FILE *fp, char *level)
{
  double seconds = user_seconds();
  static unsigned long long prev_query_special = 0;
  static unsigned long long prev_intersect_merge = 0;
  static unsigned long long prev_given = 0;

  if (fp != stderr)
    fprintf(fp, "\nNOTE: Report at %.2f seconds, %s", seconds, get_date());

  if (str_ident(level, ""))
    level = (Opt ? stringparm1(Opt->stats) : "lots");

  fprint_all_stats(fp, level);

  /* Print FPA index statistics if requested */
  if (flag(Opt->report_index_stats)) {
    unsigned long long qs = fpa_query_special_calls();
    unsigned long long im = fpa_intersect_merge_ops();
    unsigned long long g = Stats.given;
    unsigned long long delta_qs = qs - prev_query_special;
    unsigned long long delta_im = im - prev_intersect_merge;
    unsigned long long delta_g = g - prev_given;

    fprintf(fp, "\nFPA index stats: query_special=%s", comma_num(qs));
    fprintf(fp, " (+%s)", comma_num(delta_qs));
    fprintf(fp, ", intersect_merge=%s", comma_num(im));
    fprintf(fp, " (+%s)", comma_num(delta_im));
    if (delta_g > 0) {
      fprintf(fp, ", per_given: qs=%.1f, im=%.1f",
              (double)delta_qs / delta_g, (double)delta_im / delta_g);
    }
    fprintf(fp, "\n");

    prev_query_special = qs;
    prev_intersect_merge = im;
    prev_given = g;
  }

  if (!flag(Opt->quiet) && fp != stderr) {
    fflush(stdout);
  }
  fflush(fp);
  fflush(stderr);
}  /* report */

/*************
 *
 *   possible_report()
 *
 *************/

static
void possible_report(void)
{
  static int Next_report, Next_report_stderr;
  static unsigned long long Next_report_given;
  int runtime;

  runtime = user_time() / 1000;

  if (parm(Opt->report) > 0) {
    if (Next_report == 0)
      Next_report = parm(Opt->report);
    if (runtime >= Next_report) {
      report(stdout, stringparm1(Opt->stats));
      while (runtime >= Next_report)
	Next_report += parm(Opt->report);
    }
  }

  if (parm(Opt->report_stderr) > 0) {
    if (Next_report_stderr == 0)
      Next_report_stderr = parm(Opt->report_stderr);
    if (runtime >= Next_report_stderr) {
      report(stderr, "some");
      while (runtime >= Next_report_stderr)
	Next_report_stderr += parm(Opt->report_stderr);
    }
  }

  if (parm(Opt->report_given) > 0) {
    if (Next_report_given == 0)
      Next_report_given = parm(Opt->report_given);
    if (Stats.given >= Next_report_given) {
      report(stdout, stringparm1(Opt->stats));
      while (Stats.given >= Next_report_given)
	Next_report_given += parm(Opt->report_given);
    }
  }
}  /* possible_report */

/*************
 *
 *   done_with_search()
 *
 *************/

static
void done_with_search(int return_code)
{
  fprint_all_stats(stdout, Opt ? stringparm1(Opt->stats) : "lots");
  /* If we need to return 0, we have to encode it as something else. */
  longjmp(Jump_env, return_code == 0 ? INT_MAX : return_code);
}  /* done_with_search */

/*************
 *
 *   exit_if_over_limit()
 *
 *************/

static
void exit_if_over_limit(void)
{
  /* max_megs is handled elsewhere */
  /* max_seconds is handled by SIGALRM (setup_timeout_signal) */

  if (over_parm_limit(Stats.kept, Opt->max_kept))
    done_with_search(MAX_KEPT_EXIT);
  else if (over_parm_limit(Stats.given, Opt->max_given))
    done_with_search(MAX_GIVEN_EXIT);
}  /* exit_if_over_limit */

/*************
 *
 *   inferences_to_make()
 *
 *************/

static
BOOL inferences_to_make(void)
{
  return givens_available();
}  // inferences_to_make

/*************
 *
 *   index_clashable()
 *
 *   Insert/delete a clause into/from resolution index.
 *
 *************/

static
void index_clashable(Topform c, Indexop operation)
{
  if (Glob.use_clash_idx) {
    clock_start(Clocks.index);
    lindex_update(Glob.clashable_idx, c, operation);
    clock_stop(Clocks.index);
  }
}  /* index_clashable */

/*************
 *
 *   restricted_denial()
 *
 *************/

static
BOOL restricted_denial(Topform c)
{
  /* At one time we also required all clauses to be Horn. */
  return
    flag(Opt->restrict_denials) &&
    negative_clause(c->literals);
}  /* restricted_denial */

/*************
 *
 *   disable_clause()
 *
 *************/

static
void disable_clause(Topform c)
{
  // Assume c is in Usable, Sos, Denials, or none of those.
  // Also, c may be in Demodulators.
  //
  // Unindex c according to which lists it is on and
  // the flags that are set, remove c from the lists,
  // and append c to Disabled.  Make sure you don't
  // have a Clist_pos for c during the call, because
  // it will be freed during the call.

  clock_start(Clocks.disable);

  if (clist_member(c, Glob.demods)) {
    index_demodulator(c, demodulator_type(c,
					  parm(Opt->lex_dep_demod_lim),
					  flag(Opt->lex_dep_demod_sane)),
		      DELETE, Clocks.index);
    clist_remove(c, Glob.demods);
  }

  if (clist_member(c, Glob.usable)) {
    index_literals(c, DELETE, Clocks.index, FALSE);
    index_back_demod(c, DELETE, Clocks.index, flag(Opt->back_demod));
    if (!restricted_denial(c))
      index_clashable(c, DELETE);
    clist_remove(c, Glob.usable);
  }
  else if (clist_member(c, Glob.sos)) {
    index_literals(c, DELETE, Clocks.index, FALSE);
    index_back_demod(c, DELETE, Clocks.index, flag(Opt->back_demod));
    remove_from_sos2(c, Glob.sos);
  }
  else if (clist_member(c, Glob.limbo)) {
    index_literals(c, DELETE, Clocks.index, FALSE);
    clist_remove(c, Glob.limbo);
  }

  clist_append(c, Glob.disabled);
  clock_stop(Clocks.disable);
}  // disable_clause

/*************
 *
 *   free_search_memory()
 *
 *   This frees memory so that we can check for memory leaks.
 *
 *************/

/* DOCUMENTATION
This is intended for debugging only.
*/

/* PUBLIC */
void free_search_memory(void)
{
  // Demodulators

  while (Glob.demods->first) {
    Topform c = Glob.demods->first->c;
    index_demodulator(c, demodulator_type(c,
					  parm(Opt->lex_dep_demod_lim),
					  flag(Opt->lex_dep_demod_sane)),
		      DELETE, Clocks.index);
    clist_remove(c, Glob.demods);
    if (c->containers == NULL)
      delete_clause(c);
  }
  clist_free(Glob.demods);
  
  destroy_demodulation_index();

  // Usable, Sos, Limbo

  while (Glob.usable->first)
    disable_clause(Glob.usable->first->c);
  clist_free(Glob.usable);
  Glob.usable = NULL;

  while (Glob.sos->first)
    disable_clause(Glob.sos->first->c);
  clist_free(Glob.sos);
  Glob.sos = NULL;

  while (Glob.limbo->first)
    disable_clause(Glob.limbo->first->c);
  clist_free(Glob.limbo);
  Glob.limbo = NULL;

  destroy_literals_index();
  destroy_back_demod_index();
  lindex_destroy(Glob.clashable_idx);
  Glob.clashable_idx = NULL;

  delete_clist(Glob.disabled);
  Glob.disabled = NULL;

  if (Glob.hints->first) {
    Clist_pos p;
    for(p = Glob.hints->first; p; p = p->next)
      unindex_hint(p->c);
    done_with_hints();
  }
  delete_clist(Glob.hints);
  Glob.hints = NULL;

}  // free_search_memory

/*************
 *
 *   handle_proof_and_maybe_exit()
 *
 *************/

static
void handle_proof_and_maybe_exit(Topform empty_clause)
{
  Term answers;
  Plist proof, p;

  assign_clause_id(empty_clause);
  proof = get_clause_ancestors(empty_clause);
  uncompress_clauses(proof);

  if (!flag(Opt->reuse_denials) && Glob.horn) {
    Topform c = first_negative_clause(proof);
    if (clause_member_plist(Glob.desc_to_be_disabled, c)) {
      if (!flag(Opt->quiet)) {
	printf("%% Redundant proof: ");
	f_clause(empty_clause);
      }
      return;
    }
    else
      /* Descendants of c will be disabled when it is safe to do so. */
      Glob.desc_to_be_disabled = plist_prepend(Glob.desc_to_be_disabled, c);
  }

  /* Mark parents as used only for non-redundant proofs.  If done earlier,
     parents could be marked as used but then escape forward subsumption
     (which skips used clauses), leading to back subsumption finding them
     in limbo. */
  mark_parents_as_used(empty_clause);

  Glob.empties = plist_append(Glob.empties, empty_clause);
  Stats.proofs++;

  answers = get_term_attributes(empty_clause->attributes, Att.answer);

  /* message to stderr */

  if (!flag(Opt->quiet)) {
    fflush(stdout);
    if (flag(Opt->bell))
      bell(stderr);
    fprintf(stderr, "-------- Proof %s -------- ", comma_num(Stats.proofs));
    if (answers != NULL)
      fwrite_term_nl(stderr, answers);
    else if (flag(Opt->print_proof_goal)) {
      /* Find and print goal clause(s) from the proof */
      Plist q;
      BOOL printed_any = FALSE;
      for (q = proof; q; q = q->next) {
        Topform c = q->v;
        if (c->justification && c->justification->type == GOAL_JUST) {
          /* Find a meaningful label (skip "non_clause" and "goal") */
          char *label = NULL;
          int i;
          for (i = 1; ; i++) {
            char *l = get_string_attribute(c->attributes, Att.label, i);
            if (l == NULL)
              break;
            if (!str_ident(l, "non_clause") && !str_ident(l, "goal")) {
              label = l;
              break;
            }
          }
          if (printed_any)
            fprintf(stderr, ", ");
          if (label)
            fprintf(stderr, "\"%s\"", label);
          else {
            /* Print the goal formula without attributes */
            Term t = topform_to_term_without_attributes(c);
            fwrite_term(stderr, t);
            zap_term(t);
          }
          printed_any = TRUE;
        }
      }
      fprintf(stderr, "\n");
    }
    else
      fprintf(stderr, "\n");
  }

  /* print proof to stdout -- protect from signal truncation */

  set_no_kill();
  fflush(stderr);
  if (flag(Opt->tptp_output)) {
    /* TSTP format proof output — always printed in TPTP mode */
    printf("\n%% Proof %s at %.2f (+ %.2f) seconds.\n",
	   comma_num(Stats.proofs), user_seconds(), system_seconds());
    printf("%% Length of proof is %d.\n", proof_length(proof));
    printf("%% Level of proof is %d.\n", clause_level(empty_clause));
    printf("%% Maximum clause weight is %.3f.\n", max_clause_weight(proof));
    printf("%% Given clauses %s.\n\n", comma_num(Stats.given));
    fprint_proof_tptp(stdout, proof);
  }
  else if (flag(Opt->print_proofs)) {
    /* Native Prover9 proof output */
    print_separator(stdout, "PROOF", TRUE);
    printf("\n%% Proof %s at %.2f (+ %.2f) seconds",
	   comma_num(Stats.proofs), user_seconds(), system_seconds());
    if (answers != NULL) {
      printf(": ");
      fwrite_term(stdout, answers);
    }
    printf(".\n");

    {
      int pf_level;
      double max_pf_wt;
      Topform proof_cl;
      int pf_nothint_ct = 0;
      int pf_total_given = 0;
      int pf_nothint_given = 0;

      for (p = proof; p; p = p->next) {
	proof_cl = (Topform) p->v;
	if (proof_cl->was_given)
	  pf_total_given++;
	if (proof_cl->matching_hint == NULL
	    && !has_input_just(proof_cl)
	    && !has_goal_just(proof_cl)
	    && !proof_cl->initial
	    && !has_deny_just(proof_cl)
	    && number_of_literals(proof_cl->literals) != 0) {
	  pf_nothint_ct++;
	  if (proof_cl->was_given)
	    pf_nothint_given++;
	}
      }

      printf("%% Length of proof: %d (%d new hints)\n",
	     proof_length(proof), pf_nothint_ct);

      pf_level = clause_level(empty_clause);
      printf("%% Level of proof: %d\n", pf_level);

      max_pf_wt = max_clause_weight(proof);
      if (max_pf_wt > 500.00)
	printf("%% Maximum clause weight: %.3f (%d w/o degradation)\n",
	       max_pf_wt, imax_clause_weight(proof));
      else
	printf("%% Maximum clause weight: %.3f\n", max_pf_wt);

      printf("%% Given clauses in run: %s\n", comma_num(Stats.given));
      printf("%% Given clauses in proof: %d (%d new hints)\n\n",
	     pf_total_given, pf_nothint_given);
    }
    for (p = proof; p; p = p->next)
      fwrite_clause(stdout, p->v, CL_FORM_STD);
    print_separator(stdout, "end of proof", TRUE);
  }
  else {
    printf("\n-------- Proof %s at (%.2f + %.2f seconds) ",
	   comma_num(Stats.proofs), user_seconds(), system_seconds());
    if (answers != NULL)
      fwrite_term_nl(stdout, answers);
    else
      fprintf(stdout, "\n");
  }
  /* print_matched_hints: three lists per proof (Veroff feature) */
  if (flag(Opt->print_matched_hints)) {
    int pmh_count = 0;
    print_separator(stdout, "MATCHED HINTS", TRUE);
    fprintf(stdout,
	    "\nformulas(hints).  %% Hints matched by proof clauses.\n");
    for (p = proof; p; p = p->next) {
      Topform h = ((Topform) p->v)->matching_hint;
      if (h != NULL) {
	if (true_clause(h->literals))
	  pmh_count++;
	else
	  fwrite_clause(stdout, h, CL_FORM_BARE);
      }
    }
    printf("%% *** Not including %d hints that were back demodulated. ***\n",
	   pmh_count);
    fprintf(stdout, "end_of_list.\n");
    print_separator(stdout, "end of matched hints", TRUE);

    print_separator(stdout, "HINT MATCHERS", TRUE);
    fprintf(stdout,
	    "\nformulas(hints).  %% Proof clauses that match a hint.\n");
    for (p = proof; p; p = p->next) {
      if (((Topform) p->v)->matching_hint != NULL)
	fwrite_clause(stdout, p->v, CL_FORM_BARE);
    }
    fprintf(stdout, "end_of_list.\n");
    print_separator(stdout, "end of hint matchers", TRUE);

    print_separator(stdout, "NON HINT MATCHERS", TRUE);
    fprintf(stdout,
	    "\nformulas(hints).  %% Proof clauses that do not match any hints.\n");
    for (p = proof; p; p = p->next) {
      if (((Topform) p->v)->matching_hint == NULL)
	fwrite_clause(stdout, p->v, CL_FORM_BARE);
    }
    fprintf(stdout, "end_of_list.\n");
    print_separator(stdout, "end of non hint matchers", TRUE);
  }

  if (flag(Opt->print_new_hints)) {
    Topform proof_cl;
    print_separator(stdout, "NEW HINTS", TRUE);
    fprintf(stdout, "\nGiven clauses:\n\n");
    for (p = proof; p; p = p->next) {
      proof_cl = (Topform) p->v;
      if (proof_cl->matching_hint == NULL
	  && !has_input_just(proof_cl)
	  && !has_goal_just(proof_cl)
	  && !proof_cl->initial
	  && !has_deny_just(proof_cl)
	  && number_of_literals(proof_cl->literals) != 0) {
	if (proof_cl->was_given)
	  fwrite_clause(stdout, p->v, CL_FORM_STD);
      }
    }
    print_separator(stdout, "end of proof", TRUE);
    fprintf(stdout, "\nProof clauses not given:\n\n");
    for (p = proof; p; p = p->next) {
      proof_cl = (Topform) p->v;
      if (proof_cl->matching_hint == NULL
	  && !has_input_just(proof_cl)
	  && !has_goal_just(proof_cl)
	  && !proof_cl->initial
	  && !has_deny_just(proof_cl)
	  && number_of_literals(proof_cl->literals) != 0) {
	if (!proof_cl->was_given)
	  fwrite_clause(stdout, p->v, CL_FORM_STD);
      }
    }
    print_separator(stdout, "end of proof", TRUE);
  }

  fflush(stdout);
  clear_no_kill_and_check();
  if (answers)
    zap_term(answers);

  actions_in_proof(proof, &Att);  /* this can exit */

  if (at_parm_limit(Stats.proofs, Opt->max_proofs))
    done_with_search(MAX_PROOFS_EXIT);  /* does not return */

  zap_plist(proof);
}  // handle_proof_and_maybe_exit

/*************
 *
 *   clause_wt_with_adjustments()
 *
 *************/

static
void clause_wt_with_adjustments(Topform c)
{
  clock_start(Clocks.weigh);
  c->weight = clause_weight(c->literals);
  clock_stop(Clocks.weigh);

  if (!clist_empty(Glob.hints)) {
    clock_start(Clocks.hints);
    if (!c->normal_vars)
      renumber_variables(c, MAX_VARS);
    adjust_weight_with_hints(c,
			     flag(Opt->degrade_hints),
			     flag(Opt->breadth_first_hints));
    clock_stop(Clocks.hints);
  }

  {
    int sw = parm(Opt->sine_weight);
    if (sw > 0) {
      int sd = get_int_attribute(c->attributes, sine_depth_attr(), 1);
      if (sd != INT_MAX && sd > 1)
        c->weight += sw * (sd - 1);
    }
  }

  if (c->weight > floatparm(Opt->default_weight) &&
      c->weight <= floatparm(Opt->max_weight))
    c->weight = floatparm(Opt->default_weight);
}  /* clause_wt_with_adjustments */

/*************
 *
 *   cl_process()
 *
 *   Process a newly inferred (or input) clause.
 *
 *   It is likely that a pointer to this routine was passed to
 *   an inference rule, and that inference rule called this routine
 *   with a new clause.
 *
 *   If this routine decides to keep the clause, it is appended
 *   to the Limbo list rather than to Sos.  Clauses in Limbo have been
 *   kept, but operations that can delete clauses (back subsumption,
 *   back demoulation) have not yet been applied.  The Limbo list
 *   is processed after the inference rule is finished.
 *
 *   Why use the Limbo list?  Because we're not allowed to delete
 *   clauses (back subsumption, back demodulation, back unit deletion)
 *   while inferring clauses.
 *
 *   Why not infer the whole batch of clauses, and then process them?
 *   Because there can be too many.  We have to do demodulation and
 *   subsumption right away, and get kept clauses indexed for
 *   forward demodulation and forward subsumption right away,
 *   so they can be used on the next inferred clause.
 *
 *************/

/* First, some helper routines. */

static
void cl_process_simplify(Topform c)
{
  if (flag(Opt->eval_rewrite)) {
    int count = 0;
    clock_start(Clocks.demod);
    rewrite_with_eval(c);
    if (flag(Opt->print_gen)) {
      printf("%srewrites %d:     ", TPTP_PFX, count);
      fwrite_clause(stdout, c, CL_FORM_STD);
    }
    clock_stop(Clocks.demod);
  }
  else if (!clist_empty(Glob.demods)) {
    if (flag(Opt->lex_order_vars)) {
      renumber_variables(c, MAX_VARS);
      c->normal_vars = FALSE;  // demodulation can make vars non-normal
    }
    clock_start(Clocks.demod);
      demodulate_clause(c,
			parm(Opt->demod_step_limit),
			parm(Opt->demod_increase_limit),
			!flag(Opt->quiet),
			flag(Opt->lex_order_vars));
    if (flag(Opt->print_gen)) {
      printf("%srewrite:     ", TPTP_PFX);
      fwrite_clause(stdout, c, CL_FORM_STD);
    }
    clock_stop(Clocks.demod);
  }

  orient_equalities(c, TRUE);
  simplify_literals2(c);  // with x=x, and simplify tautologies to $T
  merge_literals(c);

  if (flag(Opt->unit_deletion)) {
    clock_start(Clocks.unit_del);
    unit_deletion(c);
    clock_stop(Clocks.unit_del);
  }

  if (flag(Opt->cac_redundancy)) {
    clock_start(Clocks.redundancy);
    // If comm or assoc, make a note of it.
    // Also simplify C or AC redundant literals to $T.
    if (cac_redundancy(c, !flag(Opt->quiet)))
      Glob.cac_clauses = plist_prepend(Glob.cac_clauses, c);
    clock_stop(Clocks.redundancy);
  }
}  // cl_process_simplify

/*************
 *
 *   get_hit_list() -- read "hitlist" file of clause IDs (Veroff feature)
 *
 *************/

static
void get_hit_list(void)
{
  FILE *fp;
  int n;
  fp = fopen("hitlist", "r");
  if (fp == NULL)
    fatal_error("get_hit_list: cannot open file \"hitlist\"");
  Hsize = 0;
  while (fscanf(fp, "%d", &n) == 1) {
    if (Hsize >= MAX_HSIZE) {
      printf("WARNING: hitlist truncated at %d entries.\n", MAX_HSIZE);
      break;
    }
    /* insertion sort to keep list sorted */
    {
      int i, j;
      for (i = 0; i < Hsize && HIT_LIST[i] < n; i++)
	;
      for (j = Hsize; j > i; j--)
	HIT_LIST[j] = HIT_LIST[j-1];
      HIT_LIST[i] = n;
      Hsize++;
    }
  }
  fclose(fp);
  printf("\n%% Hit list (%d entries):", Hsize);
  {
    int i;
    for (i = 0; i < Hsize; i++)
      printf(" %d", HIT_LIST[i]);
  }
  printf("\n");
}  /* get_hit_list */

/*************
 *
 *   on_hit_list() -- check if clause ID is next on the sorted hitlist
 *
 *************/

static
BOOL on_hit_list(int x)
{
  static int next_cl_pos = 0;
  while (next_cl_pos < Hsize && HIT_LIST[next_cl_pos] < x)
    next_cl_pos++;
  if (next_cl_pos < Hsize && HIT_LIST[next_cl_pos] == x) {
    next_cl_pos++;
    /* skip duplicates */
    while (next_cl_pos < Hsize && HIT_LIST[next_cl_pos] == x)
      next_cl_pos++;
    return TRUE;
  }
  return FALSE;
}  /* on_hit_list */

/*************
 *
 *   print_derivation() -- print derivation for a hitlist clause (Veroff feature)
 *
 *************/

static
void print_derivation(Topform cl)
{
  Plist proof, p;
  static int pfcount = 0;
  proof = get_clause_ancestors(cl);
  uncompress_clauses(proof);
  pfcount++;
  print_separator(stdout, "PROOF", TRUE);
  printf("\n%% Derivation (Proof) %d (Clause #%llu): ", pfcount, cl->id);
  fwrite_clause(stdout, cl, CL_FORM_BARE);
  printf("\n%% Length of derivation is %d.\n\n", proof_length(proof));
  for (p = proof; p; p = p->next)
    fwrite_clause(stdout, p->v, CL_FORM_STD);
  print_separator(stdout, "end of proof", TRUE);

  if (flag(Opt->derivations_only) && Hsize > 0
      && cl->id >= (unsigned) HIT_LIST[Hsize - 1]) {
    printf("\n%% %d derivations completed.  Terminating execution.\n", Hsize);
    done_with_search(ACTION_EXIT);  /* clean exit via longjmp */
  }
}  /* print_derivation */

static
void hint_derivation(Topform cl)
{
  Plist proof, p;
  static int pfcount = 0;
  proof = get_clause_ancestors(cl);
  uncompress_clauses(proof);
  pfcount++;
  print_separator(stdout, "PROOF", TRUE);
  printf("\n%% Hint derivation (Proof) %d: ", pfcount);
  fwrite_clause(stdout, cl, CL_FORM_BARE);
  printf("\n%% Length of derivation is %d.\n\n", proof_length(proof));
  for (p = proof; p; p = p->next)
    fwrite_clause(stdout, p->v, CL_FORM_STD);
  print_separator(stdout, "end of proof", TRUE);
}  /* hint_derivation */

static
void cl_process_keep(Topform c)
{
  Stats.kept++;
  if (!c->normal_vars)
    renumber_variables(c, MAX_VARS);
  if (c->id == 0)
    assign_clause_id(c);  // unit conflict or input: already has ID
  if (flag(Opt->print_derivations) && on_hit_list(c->id))
    print_derivation(c);
  if (To_trace_id != 0 && c->id == To_trace_id) {
    To_trace_cl = c;
    printf("\n*** Trace: clause %llu kept.\n", c->id);
  }
  mark_parents_as_used(c);
  mark_maximal_literals(c->literals);
  mark_selected_literals(c->literals, stringparm1(Opt->literal_selection));
  if (c->matching_hint != NULL) {
    keep_hint_matcher(c);
    if (parm(Opt->hint_derivations) > 0
	&& c->matching_hint->id < (unsigned) parm(Opt->hint_derivations))
      hint_derivation(c);
  }

  if (flag(Opt->print_clause_properties))
      c->attributes = set_term_attribute(c->attributes,
					 Att.properties,
					 topform_properties(c));
  if (flag(Opt->print_kept) || flag(Opt->print_gen) ||
      (!Glob.searching && flag(Opt->print_initial_clauses))) {
    printf("%skept:      ", TPTP_PFX);
    fwrite_clause(stdout, c, CL_FORM_STD);
  }
  else if (flag(Opt->print_labeled) &&
	   get_string_attribute(c->attributes, Att.label, 1)) {
    printf("\n%skept:      ", TPTP_PFX);
    fwrite_clause(stdout, c, CL_FORM_STD);
  }
  statistic_actions("kept", clause_ids_assigned());  /* Note different stat */
}  // cl_process_keep

static
void cl_process_conflict(Topform c, BOOL denial)
{
  if (number_of_literals(c->literals) == 1) {
    if (!c->normal_vars)
      renumber_variables(c, MAX_VARS);
    clock_start(Clocks.conflict);
    unit_conflict(c, handle_proof_and_maybe_exit);
    clock_stop(Clocks.conflict);
  }
}  // cl_process_conflict

static
void cl_process_new_demod(Topform c)
{
  // If the clause should be a demodulator, make it so.
  if (flag(Opt->back_demod)) {
    int type = demodulator_type(c,
				parm(Opt->lex_dep_demod_lim),
				flag(Opt->lex_dep_demod_sane));
    if (type != NOT_DEMODULATOR) {
      if (flag(Opt->print_kept)) {
	char *s;
	switch(type) {
	case ORIENTED:     s = ""; break;
	case LEX_DEP_LR:   s = " (lex_dep_lr)"; break;
	case LEX_DEP_RL:   s = " (lex_dep_rl)"; break;
	case LEX_DEP_BOTH: s = " (lex_dep_both)"; break;
	default:           s = " (?)";
	}
	printf("%s    new demodulator%s: %llu.\n", TPTP_PFX, s, c->id);
      }
      clist_append(c, Glob.demods);
      index_demodulator(c, type, INSERT, Clocks.index);
      Stats.new_demodulators++;
      if (type != ORIENTED)
	Stats.new_lex_demods++;
      back_demod_hints(c, type, flag(Opt->lex_order_vars));
    }
  }
}  // cl_process_new_demod

static
BOOL skip_black_white_tests(Topform c)
{
  return (!Glob.searching ||
	  c->used ||
	  restricted_denial(c) ||
	  (c->matching_hint  != NULL && !flag(Opt->limit_hint_matchers)));
}  /* skip_black_white_tests */

static
BOOL cl_process_delete(Topform c)
{
  // Should the clause be deleted (tautology, limits, subsumption)?

  if (true_clause(c->literals)) {  // tautology
    if (flag(Opt->print_gen))
      printf("%stautology\n", TPTP_PFX);
    Stats.subsumed++;
    return TRUE;  // delete
  }

  clause_wt_with_adjustments(c);  // possibly sets c->matching_hint

  // White-black tests

  if (!skip_black_white_tests(c)) {
    if (white_tests(c)) {
      if (flag(Opt->print_gen))
	printf("%skeep_rule applied.\n", TPTP_PFX);
      Stats.kept_by_rule++;
    }
    else {
      if (black_tests(c)) {
	if (flag(Opt->print_gen))
	  printf("%sdelete_rule applied.\n", TPTP_PFX);
	Stats.deleted_by_rule++;
	return TRUE;  //delete
      }
      else if (!sos_keep2(c, Glob.sos, Opt)) {
	if (flag(Opt->print_gen))
	  printf("%ssos_limit applied.\n", TPTP_PFX);
	Stats.sos_limit_deleted++;
	return TRUE;  // delete
      }
    }
  }
      
  // Forward subsumption

  {
    Topform subsumer;
    clock_start(Clocks.subsume);
    subsumer = forward_subsumption(c);
    clock_stop(Clocks.subsume);
    if (subsumer != NULL && !c->used) {
      if (flag(Opt->print_gen))
	printf("%ssubsumed by %llu.\n", TPTP_PFX, subsumer->id);
      Stats.subsumed++;
      return TRUE;  // delete
    }
    else
      return FALSE;  // keep the clause
  }
}  // cl_process_delete

static
void cl_process(Topform c)
{
  // If the infer_clock is running, stop it and restart it when done.

  BOOL infer_clock_stopped = FALSE;
  if (clock_running(Clocks.infer)) {
    clock_stop(Clocks.infer);
    infer_clock_stopped = TRUE;
  }
  clock_start(Clocks.preprocess);

  exit_if_over_limit();
  if (parm(Opt->report) > 0 || parm(Opt->report_stderr) > 0 || parm(Opt->report_given) > 0)
    possible_report();

  Stats.generated++;
  statistic_actions("generated", Stats.generated);
  if (flag(Opt->print_gen)) {
    printf("\n%sgenerated: ", TPTP_PFX);
    fwrite_clause(stdout, c, CL_FORM_STD);
  }

  cl_process_simplify(c);            // all simplification

  if (number_of_literals(c->literals) == 0)    // empty clause
    handle_proof_and_maybe_exit(c);
  else {
    // Do safe unit conflict before any deletion checks.
    if (flag(Opt->safe_unit_conflict))
      cl_process_conflict(c, FALSE);  // marked as used if conflict

    if (cl_process_delete(c))
      delete_clause(c);
    else {
      cl_process_keep(c);
      // Ordinary unit conflict.
      if (!flag(Opt->safe_unit_conflict))
	cl_process_conflict(c, FALSE);
      cl_process_new_demod(c);
      // We insert c into the literal index now so that it will be
      // available for unit conflict and forward subsumption while
      // it's in limbo.  (It should not be back subsumed while in limbo.
      // See fatal error in limbo_process).
      index_literals(c, INSERT, Clocks.index, FALSE);
      clist_append(c, Glob.limbo);
    }  // not deleted
  }  // not empty clause
  
  clock_stop(Clocks.preprocess);
  if (infer_clock_stopped)
    clock_start(Clocks.infer);
}  // cl_process

/*************
 *
 *   back_demod()
 *
 *   For each clause that can be back demodulated, make a copy,
 *   disable the original, cl_process the copy (as if it
 *   had just been inferred).
 *
 *************/

static
void back_demod(Topform demod)
{
  Plist results, p, prev;

  clock_start(Clocks.back_demod);
  results = back_demodulatable(demod,
			       demodulator_type(demod,
						parm(Opt->lex_dep_demod_lim),
						flag(Opt->lex_dep_demod_sane)),
			       flag(Opt->lex_order_vars));
  clock_stop(Clocks.back_demod);
  p = results;
  while(p != NULL) {
    Topform old = p->v;
    if (!clist_member(old, Glob.disabled)) {
      Topform new;
      if (flag(Opt->basic_paramodulation))
	new = copy_clause_with_flag(old, nonbasic_flag());
      else
	new = copy_clause(old);
      Stats.back_demodulated++;
      if (flag(Opt->print_kept))
	printf("%s        %llu back demodulating %llu.\n", TPTP_PFX, demod->id, old->id);
      if (To_trace_cl == old) {
	printf("\n*** Trace: clause %llu back demodulated by %llu.\n",
	       old->id, demod->id);
	To_trace_cl = NULL;
      }
      new->justification = back_demod_just(old);
      new->attributes = inheritable_att_instances(old->attributes, NULL);
      disable_clause(old);
      cl_process(new);
    }
    prev = p;
    p = p->next;
    free_plist(prev);
  }
}  // back_demod

/*************
 *
 *   back_unit_deletion()
 *
 *   For each clause that can be back unit deleted, make a copy,
 *   disable the original, cl_process the copy (as if it
 *   had just been inferred).
 *
 *************/

static
void back_unit_deletion(Topform unit)
{
  Plist results, p, prev;

  clock_start(Clocks.back_unit_del);
  results = back_unit_deletable(unit);
  clock_stop(Clocks.back_unit_del);
  p = results;
  while(p != NULL) {
    Topform old = p->v;
    if (!clist_member(old, Glob.disabled)) {
      Topform new;
      if (flag(Opt->basic_paramodulation))
	new = copy_clause_with_flag(old, nonbasic_flag());
      else
	new = copy_clause(old);
      Stats.back_unit_deleted++;
      if (flag(Opt->print_kept))
	printf("%s        %llu back unit deleting %llu.\n", TPTP_PFX, unit->id, old->id);
      new->justification = back_unit_deletion_just(old);
      new->attributes = inheritable_att_instances(old->attributes, NULL);
      disable_clause(old);
      cl_process(new);
    }
    prev = p;
    p = p->next;
    free_plist(prev);
  }
}  // back_unit_deletion

/*************
 *
 *   back_cac_simplify()
 *
 *   For each clause that can be back unit deleted, make a copy,
 *   disable the original, cl_process the copy (as if it
 *   had just been inferred).
 *
 *************/

static
void back_cac_simplify(void)
{
  Plist to_delete = NULL;
  Plist a;
  Clist_pos p;
  for (p = Glob.sos->first; p; p = p->next) {
    if (cac_tautology(p->c->literals))
      to_delete = plist_prepend(to_delete, p->c);
  }
  for (p = Glob.usable->first; p; p = p->next) {
    if (cac_tautology(p->c->literals))
      to_delete = plist_prepend(to_delete, p->c);
  }
  for (p = Glob.limbo->first; p; p = p->next) {
    if (cac_tautology(p->c->literals))
      to_delete = plist_prepend(to_delete, p->c);
  }
  for (a = to_delete; a; a = a->next) {
    if (!flag(Opt->quiet)) {
      printf("%% back CAC tautology: "); f_clause(a->v);
    }
    disable_clause(a->v);
  }
  zap_plist(to_delete);  /* shallow */
}  // back_cac_simplify

/*************
 *
 *   disable_to_be_disabled()
 *
 *************/

static
void disable_to_be_disabled(void)
{
  if (Glob.desc_to_be_disabled) {

    Plist descendants = NULL;
    Plist p;

    sort_clist_by_id(Glob.disabled);

    for (p = Glob.desc_to_be_disabled; p; p = p->next) {
      Topform c = p->v;
      Plist x = neg_descendants(c,Glob.usable,Glob.sos,Glob.disabled);
      descendants = plist_cat(descendants, x);
    }
    
    if (!flag(Opt->quiet)) {
      int n = 0;
      printf("\n%% Disable descendants (x means already disabled):\n");
      for (p = descendants; p; p = p->next) {
	Topform d = p->v;
	printf(" %llu%s", d->id, clist_member(d, Glob.disabled) ? "x" : "");
	if (++n % 10 == 0)
	  printf("\n");
      }
      printf("\n");
    }

    for (p = descendants; p; p = p->next) {
      Topform d = p->v;
      if (!clist_member(d, Glob.disabled))
	disable_clause(d);
    }

    zap_plist(descendants);
    zap_plist(Glob.desc_to_be_disabled);
    Glob.desc_to_be_disabled = NULL;
  }
}  /* disable_to_be_disabled */

/*************
 *
 *   degradation_count() -- BV(2016-feb-02)
 *
 *   Degraded weight of c is weight(c) + degradation_count * 1000.
 *
 *************/

static int degradation_count(Topform c)
{
  return (int)(c->weight) / 1000;
}  /* degradation_count */

/*************
 *
 *   limbo_process()
 *
 *   Apply back subsumption and back demodulation to the Limbo
 *   list.  Since back demodulated clauses are cl_processed,
 *   the Limbo list can grow while it is being processed.
 *
 *   If this prover had a hot-list, or any other feature that
 *   generates clauses from newly kept clauses, it probably would
 *   be done here.
 *
 *   The Limbo list operates as a queue.  An important property
 *   of the Limbo list is that if A is ahead of B, then A does
 *   not simplify or subsume B.  However, B can simplify or subsume A.
 *
 *************/

static
void limbo_process(BOOL pre_search)
{
  int lp_count = 0;
  double lp_next = preprocessing_report_starting();

  while (Glob.limbo->first) {
    Topform c = Glob.limbo->first->c;
    double iter_start = (lp_next > 0) ? user_seconds() : 0;

    /* Timeout is handled by SIGALRM (setup_timeout_signal) */

    lp_count++;
    if (lp_next > 0) {
      double now = iter_start;
      if (now >= lp_next) {
	fprintf(stderr,
		"NOTE: preprocessing limbo processed %d, remaining %d"
		" (%.1f sec, %lld MB)\n",
		lp_count, clist_length(Glob.limbo), now, megs_malloced());
	fflush(stderr);
	lp_next = now + parm(Opt->report_preprocessing);
      }
    }

    // factoring

    if (flag(Opt->factor))
      binary_factors(c, cl_process);

    // Try to apply new_constant rule.

    if (!at_parm_limit(Stats.new_constants, Opt->new_constants)) {
      Topform new = new_constant(c, INT_MAX);
      if (new) {
	Stats.new_constants++;
	if (!flag(Opt->quiet)) {
	  printf("\nNOTE: New constant: ");
	  f_clause(new);
	  printf("NOTE: New ");
	  print_fsym_precedence(stdout);
	}
	if (Glob.interps)
	  update_semantics_new_constant(new);
	cl_process(new);
      }
    }

    // fold denial (for input clauses only)

    if (parm(Opt->fold_denial_max) > 1 &&
	(has_input_just(c) || has_copy_just(c))) {
      Topform new = fold_denial(c, parm(Opt->fold_denial_max));
      if (new) {
	if (!flag(Opt->quiet)) {
	  printf("\nNOTE: Fold denial: ");
	  f_clause(new);
	}
	cl_process(new);
      }
    }

    // Disable clauses subsumed by c (back subsumption).

    if (flag(Opt->back_subsume)) {
      Plist subsumees;
      /* BV(2016-feb-02): degradation count tracking for weight reset */
      int Dcount_c = degradation_count(c);
      int Dcount_min_sos = Dcount_c;
      int Dcount_min_not_sos = Dcount_c;

      clock_start(Clocks.back_subsume);
      subsumees = back_subsumption(c);
      if (subsumees != NULL)
	c->subsumer = TRUE;
      while (subsumees != NULL) {
	Topform d = subsumees->v;
	/* Skip used clauses for consistency with forward subsumption, which
	   also skips used clauses.  This prevents a clause from escaping
	   forward subsumption (due to being marked used) but then being
	   caught by back subsumption. */
	if (flag(Opt->back_subsume_skip_used) && d->used) {
	  subsumees = plist_pop(subsumees);
	  continue;
	}
	/* Skip limbo clauses: they are in the literal index (for forward
	   subsumption and unit conflict) but have not yet been fully
	   processed.  This can happen when cl_process() adds a new clause
	   to limbo (e.g., via back_demod, back_unit_deletion, factoring,
	   or new_constant) and that clause is then found by
	   back_subsumption of a different limbo clause being processed
	   in the same limbo_process() loop.  The limbo clause will be
	   handled in its own iteration of the loop. */
	if (flag(Opt->back_subsume_skip_limbo) && clist_member(d, Glob.limbo)) {
	  subsumees = plist_pop(subsumees);
	  continue;
	}
	Stats.back_subsumed++;

	/* BV(2016-feb-02): when degraded hint matcher c subsumes
	   hint matcher d, track the minimum degradation counts. */
	if (c->matching_hint != NULL
	    && d->matching_hint != NULL
	    && Dcount_c > 0) {
	  int Dcount_d = degradation_count(d);
	  if (clist_member(d, Glob.sos)) {
	    if (Dcount_d < Dcount_min_sos)
	      Dcount_min_sos = Dcount_d;
	  }
	  else {
	    if (Dcount_d < Dcount_min_not_sos)
	      Dcount_min_not_sos = Dcount_d;
	  }
	}

	if (flag(Opt->print_kept)) {
	  if (d->matching_hint != NULL)
	    printf("%s    %llu back subsumes hint matcher %llu.\n",
		   TPTP_PFX, c->id, d->id);
	  else
	    printf("%s    %llu back subsumes %llu.\n", TPTP_PFX, c->id, d->id);
	}
	if (To_trace_cl == d) {
	  printf("\n*** Trace: clause %llu back subsumed by %llu.\n",
		 d->id, c->id);
	  To_trace_cl = NULL;
	}
	disable_clause(d);
	subsumees = plist_pop(subsumees);
      }

      /* BV(2016-feb-02): adjust degradation of c if a subsumed hint
	 matcher has a lower degradation count. */
      if (Dcount_min_sos < Dcount_c || Dcount_min_not_sos < Dcount_c) {
	c->weight = (int)(c->weight) % 1000;  /* original computed weight */
	if (Dcount_min_sos <= Dcount_min_not_sos) {
	  c->weight = c->weight + Dcount_min_sos * 1000;
	  if (flag(Opt->print_given))
	    printf("%s => %llu back subsumes a hint matcher on Sos."
		   "  Reset weight to %.3f.\n", TPTP_PFX, c->id, c->weight);
	}
	else {
	  c->weight = c->weight + Dcount_min_not_sos * 1000 + 500;
	  if (flag(Opt->print_given))
	    printf("%s => %llu back subsumes hint matchers not on Sos."
		   "  Reset weight to %.3f.\n", TPTP_PFX, c->id, c->weight);
	}
      }

      clock_stop(Clocks.back_subsume);
    }

    // If demodulator, rewrite other clauses (back demodulation).

    if (clist_member(c, Glob.demods)) {
      if (flag(Opt->print_kept))
	printf("%s    starting back demodulation with %llu.\n", TPTP_PFX, c->id);
      back_demod(c);  // This calls cl_process on rewritable clauses.
    }

    // If unit, use it to simplify other clauses (back unit_deletion)

    if (flag(Opt->unit_deletion) && unit_clause(c->literals)) {
      back_unit_deletion(c);  // This calls cl_process on rewritable clauses.
    }

    // Check if we should do back CAC simplification.

    if (plist_member(Glob.cac_clauses, c)) {
      back_cac_simplify();
    }

    // Remove from limbo

    clist_remove(c, Glob.limbo);

    // If restricted_denial, append to usable, else append to sos.

    if (restricted_denial(c)) {
      // do not index_clashable!  disable_clause should not unindex_clashable!
      clist_append(c, Glob.usable);
      index_back_demod(c, INSERT, Clocks.index, flag(Opt->back_demod));
    }
    else {
      // Move to Sos and index to be found for back demodulation.
      if (parm(Opt->sos_limit) != -1 &&
	  clist_length(Glob.sos) >= parm(Opt->sos_limit)) {
	sos_displace2(disable_clause, flag(Opt->quiet));
	Stats.sos_displaced++;
      }
      if (pre_search)
	c->initial = TRUE;
      else
	c->initial = FALSE;
      insert_into_sos2(c, Glob.sos);
      index_back_demod(c, INSERT, Clocks.index, flag(Opt->back_demod));
    }

    // Report if this single iteration took a long time
    if (lp_next > 0) {
      double iter_elapsed = user_seconds() - iter_start;
      if (iter_elapsed >= parm(Opt->report_preprocessing)) {
	fprintf(stderr,
		"NOTE: preprocessing limbo clause %llu took %.1f sec"
		" (remaining %d, %.1f sec, %lld MB)\n",
		c->id, iter_elapsed, clist_length(Glob.limbo),
		user_seconds(), megs_malloced());
	fflush(stderr);
	lp_next = user_seconds() + parm(Opt->report_preprocessing);
      }
    }
  }
  // Now it is safe to disable descendants of desc_to_be_disabled clauses.
  disable_to_be_disabled();

  if (pre_search && lp_count > 0) {
#ifdef DEBUG
    fprintf(stderr, "%% limbo_process done: %d clauses (%.2f sec, %lld MB)\n",
	    lp_count, user_seconds(), megs_malloced());
    fflush(stderr);
#endif
  }
}  // limbo_process

/*************
 *
 *   infer_outside_loop()
 *
 *************/

static
void infer_outside_loop(Topform c)
{
  /* If simplification changes the clause, we want to do a "copy"
   inference first, so that a proof does not contain a justification
   like  [assumption,rewrite[...],...]. */
  Topform copy = copy_inference(c);  /* Note: c has no ID yet. */
  cl_process_simplify(copy);
  if (copy->justification->next == NULL) {
    /* Simplification does nothing, so we can just process the original. */
    delete_clause(copy);
    cl_process(c);
  }
  else {
    assign_clause_id(c);
    copy->justification->u.id = c->id;
    clist_append(c, Glob.disabled);
    cl_process(copy);  /* This re-simplifies, but that's ok. */
  }

  limbo_process(FALSE);
}  /* infer_outside_loop */

/*************
 *
 *   given_infer()
 *
 *   Make given_clause inferences according to the flags that are set.
 *   Inferred clauses are sent to cl_process().
 *
 *   We could process the Limbo list after each inference rule,
 *   and this might improve performance in some cases.  But it seems
 *   conceptually simplier if we process the Limbo clauses after
 *   all of the inferences have been made.
 *
 *************/

static
void given_infer(Topform given)
{
  clock_start(Clocks.infer);

  if (flag(Opt->binary_resolution))
    binary_resolution(given,
		      ANY_RES,
		      Glob.clashable_idx,
		      cl_process);

  if (flag(Opt->neg_binary_resolution))
    binary_resolution(given,
		      NEG_RES,
		      Glob.clashable_idx,
		      cl_process);

  if (flag(Opt->pos_hyper_resolution))
    hyper_resolution(given, POS_RES, Glob.clashable_idx, cl_process);

  if (flag(Opt->neg_hyper_resolution))
    hyper_resolution(given, NEG_RES, Glob.clashable_idx, cl_process);

  if (flag(Opt->pos_ur_resolution))
    ur_resolution(given, POS_RES, Glob.clashable_idx, cl_process);

  if (flag(Opt->neg_ur_resolution))
    ur_resolution(given, NEG_RES, Glob.clashable_idx, cl_process);

  if (flag(Opt->paramodulation) &&
      !over_parm_limit(number_of_literals(given->literals),
		       Opt->para_lit_limit)) {
    /* This paramodulation does not use indexing. */
    Context cf = get_context();
    Context ci = get_context();
    Clist_pos p;
    BOOL good_given = (given->id < (unsigned) parm(Opt->para_restr_beg)
		       || given->id > (unsigned) parm(Opt->para_restr_end));
    for (p = Glob.usable->first; p; p = p->next) {
      if (!restricted_denial(p->c) &&
	  !over_parm_limit(number_of_literals(p->c->literals),
			   Opt->para_lit_limit)) {
	BOOL good_pair = (good_given
			  || p->c->id < (unsigned) parm(Opt->para_restr_beg)
			  || p->c->id > (unsigned) parm(Opt->para_restr_end));
	if (good_pair) {
	  para_from_into(given, cf, p->c, ci, FALSE, cl_process);
	  para_from_into(p->c, cf, given, ci, TRUE, cl_process);
	}
      }
    }
    free_context(cf);
    free_context(ci);
  }

  clock_stop(Clocks.infer);
}  // given_infer

/*************
 *
 *   rebuild_sos_index()
 *
 *************/

static
void rebuild_sos_index(void)
{
  fatal_error("rebuild_sos_index not implemented for given_selection");
#if 0
  Clist_pos p;
  printf("\nNOTE: Reweighing all SOS clauses and rebuilding SOS indexes.\n");
  zap_picker_indexes();
  update_picker_ratios(Opt);  /* in case they've been changed */
  for (p = Glob.sos->first; p; p = p->next) {
    Topform c = p->c;
    clause_wt_with_adjustments(c); /* weigh the clause (wt stored in c) */
    update_pickers(c, TRUE); /* insert (lower-level) into picker indexes */
#endif
}  /* rebuild_sos_index */

/*************
 *
 *   make_inferences()
 *
 *   Assume that there are inferences to make.
 *
 *   If we had the option of using the pair algorithm instead of
 *   the given algorithm, we could make that decision here.
 *
 *************/

static
void make_inferences(void)
{
  Topform given_clause;
  char *selection_type;

  clock_start(Clocks.pick_given);
  given_clause = get_given_clause2(Glob.sos,Stats.given, Opt, &selection_type);
  clock_stop(Clocks.pick_given);

  if (given_clause != NULL) {

    // Print "level" message for breadth-first; also "level" actions.

    if (flag(Opt->breadth_first) &&
	parm(Opt->true_part) == 0 &&
	parm(Opt->false_part) == 0 &&
	parm(Opt->weight_part) == 0 &&
	parm(Opt->random_part) == 0 &&
	str_ident(selection_type, "A") &&
	given_clause->id > Bf_last_of_level) {
      Bf_level++;
      Bf_last_of_level = clause_ids_assigned();
      if (!flag(Opt->quiet)) {
	printf("\nNOTE: Starting on level %d, last clause "
	       "of level %d is %d.\n",
	       Bf_level, Bf_level-1, Bf_last_of_level);
	fflush(stdout);
	fprintf(stderr, "\nStarting on level %d, last clause "
		"of level %d is %d.\n",
		Bf_level, Bf_level-1, Bf_last_of_level);
	fflush(stderr);
      }
      statistic_actions("level", Bf_level);
    }

    Stats.given++;
    given_clause->was_given = TRUE;
    set_hints_given_count(Stats.given);

    /* max_nohints: exit after N consecutive givens w/o hint match (Veroff) */
    {
      BOOL hint_matcher = given_clause->matching_hint != NULL
	&& (parm(Opt->degrade_limit) == -1
	    || (int)(given_clause->weight / 1000) <= parm(Opt->degrade_limit));
      if (given_clause->initial || hint_matcher)
	Nohints_count = 0;
      else
	Nohints_count++;
      if (parm(Opt->max_nohints) > 0
	  && Nohints_count > parm(Opt->max_nohints)) {
	printf("\n%% %d givens in a row w/o an input clause or a hint matcher "
	       "(max_nohints).\n", parm(Opt->max_nohints));
	done_with_search(MAX_NOHINTS_EXIT);
      }
    }

    // Clause-count-based reporting
    if (parm(Opt->report_given) > 0)
      possible_report();

    // Maybe disable back subsumption.

    if (over_parm_limit(Stats.given, Opt->max_given))
      done_with_search(MAX_GIVEN_EXIT);

    if (Stats.given == parm(Opt->backsub_check)) {
      int ratio = (Stats.back_subsumed == 0 ?
		   INT_MAX :
		   Stats.kept / Stats.back_subsumed);
      if (ratio > 20) {
	clear_flag(Opt->back_subsume, !flag(Opt->quiet));
	if (!flag(Opt->quiet)) {
	  printf("\nNOTE: Back_subsumption disabled, ratio of kept"
		 " to back_subsumed is %d (%.2f of %.2f sec).\n",
		 ratio, clock_seconds(Clocks.back_subsume), user_seconds());
	  fflush(stdout);
	}
      }
    }
    
    if (flag(Opt->print_given) || Stats.given % 500 == 0) {
      if (given_clause->weight == round(given_clause->weight))
	printf("\n%sgiven #%s (%s,wt=%d): ",
	       TPTP_PFX, comma_num(Stats.given), selection_type, (int) given_clause->weight);
      else
	printf("\n%sgiven #%s (%s,wt=%.3f): ",
	       TPTP_PFX, comma_num(Stats.given), selection_type, given_clause->weight);
      fwrite_clause(stdout, given_clause, CL_FORM_STD);
    }

    statistic_actions("given", Stats.given);

    if (To_trace_cl != NULL &&
	!clist_member(To_trace_cl, Glob.sos) &&
	!clist_member(To_trace_cl, Glob.usable) &&
	!clist_member(To_trace_cl, Glob.limbo)) {
      printf("\n*** Trace: clause %llu has disappeared.\n", To_trace_cl->id);
      To_trace_cl = NULL;
    }

    clist_append(given_clause, Glob.usable);
    index_clashable(given_clause, INSERT);
    given_infer(given_clause);
  }
}  // make_inferences

/*************
 *
 *   orient_input_eq()
 *
 *   This is designed for input clauses, and it's a bit tricky.  If any
 *   equalities are flipped, we make the flip operations info inferences
 *   so that proofs are complete.  This involves replacing and hiding
 *   (disabling) the original clause.
 *
 *************/

static
Topform orient_input_eq(Topform c)
{
  Topform new = copy_inference(c);
  orient_equalities(new, TRUE);
  if (clause_ident(c->literals, new->literals)) {
    delete_clause(new);
    /* the following puts "oriented" marks on c */
    orient_equalities(c, TRUE);
    return c;
  }
  else {
    /* Replace c with new in Usable. */
    assign_clause_id(new);
    mark_parents_as_used(new);
    clist_swap(c, new);
    clist_append(c, Glob.disabled);
    return new;
  }
}  /* orient_input_eq */

/*************
 *
 *   auto_inference()
 *
 *   This looks at the clauses and decides which inference rules to use.
 *
 *************/

static
void auto_inference(Clist sos, Clist usable, Prover_options opt)
{
  BOOL print = !flag(opt->quiet);
  if (print)
    printf("\nAuto_inference settings:\n");

  if (Glob.equality) {
    if (print)
      printf("  %% set(paramodulation).  %% (positive equality literals)\n");
    set_flag(opt->paramodulation, print);
  }

  if (!Glob.equality || !Glob.unit) {
    if (Glob.horn) {
      Plist clauses = NULL;
      clauses = prepend_clist_to_plist(clauses, sos);
      clauses = prepend_clist_to_plist(clauses, usable);

      if (Glob.equality) {
	if (print)
	  printf("  %% set(hyper_resolution)."
		 "  %% (nonunit Horn with equality)\n");
	set_flag(opt->hyper_resolution, print);
	if (print)
	  printf("  %% set(neg_ur_resolution)."
		 "  %% (nonunit Horn with equality)\n");
	set_flag(opt->neg_ur_resolution, print);

	if (parm(opt->para_lit_limit) == -1) {
	  int para_lit_limit = most_literals(clauses);
	  if (print)
	    printf("  %% assign(para_lit_limit, %d)."
		   "  %% (nonunit Horn with equality)\n",
		   para_lit_limit);
	  assign_parm(opt->para_lit_limit, para_lit_limit, print);
	}
      }
      else {
	int diff = neg_pos_depth_difference(clauses);
	if (diff > 0) {
	  if (print)
	    printf("  %% set(hyper_resolution)."
		   "  %% (HNE depth_diff=%d)\n", diff);
	  set_flag(opt->hyper_resolution, print);
	}
	else {
	  if (print)
	    printf("  %% set(neg_binary_resolution)."
		   "  %% (HNE depth_diff=%d)\n", diff);
	  set_flag(opt->neg_binary_resolution, print);
	  if (print)
	    printf("  %% clear(ordered_res)."
		   "  %% (HNE depth_diff=%d)\n", diff);
	  clear_flag(opt->ordered_res, print);
	  if (print)
	    printf("  %% set(ur_resolution)."
		   "  %% (HNE depth_diff=%d)\n", diff);
	  set_flag(opt->ur_resolution, print);
	}
      }
      zap_plist(clauses);
    }
    else {
      // there are nonhorn clauses
      if (print) {
	printf("  %% set(binary_resolution).  %% (non-Horn)\n");
      }
      set_flag(opt->binary_resolution, print);
      if (Glob.number_of_clauses < 100) {
	if (print)
	  printf("  %% set(neg_ur_resolution)."
		 "  %% (non-Horn, less than 100 clauses)\n");
	set_flag(opt->neg_ur_resolution, print);
      }
    }
  }
}  /* auto_inference */

/*************
 *
 *   auto_process()
 *
 *   This looks at the clauses and decides some processing options.
 *
 *************/

static
void auto_process(Clist sos, Clist usable, Prover_options opt)
{
  BOOL print = !flag(opt->quiet);
  Plist clauses;
  BOOL horn;

  clauses = prepend_clist_to_plist(NULL, sos);
  clauses = prepend_clist_to_plist(clauses, usable);

  horn  = all_clauses_horn(clauses);

  if (print)
    printf("\nAuto_process settings:");

  if (horn) {
    if (neg_nonunit_clauses(clauses) > 0) {
      if (print)
	printf("\n  %% set(unit_deletion)."
	       "  %% (Horn set with negative nonunits)\n");
      set_flag(opt->unit_deletion, print);
    }
    else {
      if (print)
	printf("  (no changes).\n");
    }
  }

  else {
    // there are nonhorn clauses
    if (print)
      printf("\n  %% set(factor).  %% (non-Horn)\n");
    set_flag(opt->factor, print);
    if (print)
      printf("  %% set(unit_deletion).  %% (non-Horn)\n");
    set_flag(opt->unit_deletion, print);
  }
  zap_plist(clauses);
}  /* auto_process */

/*************
 *
 *   auto_denials()
 *
 *************/

static
void auto_denials(Clist sos, Clist usable, Prover_options opt)
{
  int changes = 0;
  int echo_id = str_to_flag_id("echo_input");
  BOOL echo = (echo_id == -1 ? TRUE : flag(echo_id));
  BOOL quiet = flag(opt->quiet);

  if (!quiet)
    printf("\nAuto_denials:");

  if (Glob.horn) {
    Plist neg_clauses = plist_cat(neg_clauses_in_clist(sos),
				  neg_clauses_in_clist(usable));
    Plist p;
    for (p = neg_clauses; p; p = p->next) {
      Topform c = p->v;
      char *label = get_string_attribute(c->attributes, Att.label, 1);
      Term answer = get_term_attribute(c->attributes, Att.answer, 1);
      if (label && !answer) {
	Term t = get_rigid_term(label, 0);
	c->attributes = set_term_attribute(c->attributes, Att.answer, t);
	if (echo && !quiet) {
	  printf("%s", changes == 0 ? "\n" : "");
	  printf("  %% copying label %s to answer in negative clause\n", label);
	}
	changes++;
      }
    }

    if (!quiet && changes > 0 && !echo)
      printf("\n  %% copied labels to answers in %d negative clauses (not echoed)\n",
	     changes);

    if (Glob.number_of_neg_clauses > 1 && parm(opt->max_proofs) == 1
        && !flag(opt->tptp_output)) {
      /* In TPTP mode, max_proofs stays at 1 (standard ATP behavior). */
      if (!quiet) {
        printf("%s", changes == 0 ? "\n" : "");
        printf("  %% assign(max_proofs, %d)."
	       "  %% (Horn set with more than one neg. clause)\n",
	       Glob.number_of_neg_clauses);
      }
      assign_parm(opt->max_proofs, Glob.number_of_neg_clauses, TRUE);
      check_constant_sharing(neg_clauses);
      changes++;
    }
    zap_plist(neg_clauses);
  }

  if (!quiet && changes == 0)
    printf("  (%sno changes).\n", Glob.horn ? "" : "non-Horn, ");
}  /* auto_denials */

/*************
 *
 *   init_search()
 *
 *************/

static
void init_search_early(void)
{
  // Phase 1: Initialize clocks, weights, given-clause selection,
  // delete rules, actions, and term ordering MODE.
  // These do NOT depend on clauses being loaded.

  // Initialize clocks.

  Clocks.pick_given    = clock_init("pick_given");
  Clocks.infer         = clock_init("infer");
  Clocks.preprocess    = clock_init("preprocess");
  Clocks.demod         = clock_init("demod");
  Clocks.unit_del      = clock_init("unit_deletion");
  Clocks.redundancy    = clock_init("redundancy");
  Clocks.conflict      = clock_init("conflict");
  Clocks.weigh         = clock_init("weigh");
  Clocks.hints         = clock_init("hints");
  Clocks.subsume       = clock_init("subsume");
  Clocks.semantics     = clock_init("semantics");
  Clocks.back_subsume  = clock_init("back_subsume");
  Clocks.back_demod    = clock_init("back_demod");
  Clocks.back_unit_del = clock_init("back_unit_del");
  Clocks.index         = clock_init("index");
  Clocks.disable       = clock_init("disable");

  init_actions(Glob.actions,
	       rebuild_sos_index, done_with_search, infer_outside_loop);
  init_weight(Glob.weights,
	      floatparm(Opt->variable_weight),
	      floatparm(Opt->constant_weight),
	      floatparm(Opt->not_weight),
	      floatparm(Opt->or_weight),
	      floatparm(Opt->sk_constant_weight),
	      floatparm(Opt->prop_atom_weight),
	      floatparm(Opt->nest_penalty),
	      floatparm(Opt->depth_penalty),
	      floatparm(Opt->var_penalty),
	      floatparm(Opt->complexity));

  if (Glob.given_selection == NULL)
    Glob.given_selection = selector_rules_from_options(Opt);
  else if (Resume_dir == NULL && flag(Opt->input_sos_first))
    /* Skip on resume: saved_input.txt already has the complete
       given_selection list including the "I" rule from the original run.
       Re-prepending would duplicate it, corrupting the picker cycle. */
    Glob.given_selection = plist_prepend(Glob.given_selection,
					 selector_rule_term("I", "high", "age",
							    "initial",
							    INT_MAX));
  init_giv_select(Glob.given_selection);

  /* On resume, saved_input.txt already has the complete delete_rules.
     Skip merging defaults to avoid duplication. */
  if (Resume_dir == NULL)
    Glob.delete_rules = plist_cat(delete_rules_from_options(Opt),
				  Glob.delete_rules);
  else if (Glob.delete_rules == NULL)
    Glob.delete_rules = delete_rules_from_options(Opt);

  init_white_black(Glob.keep_rules, Glob.delete_rules);

  // Term ordering mode (LPO/RPO/KBO assignment).
  // symbol_order and KBO weight computation are deferred to
  // init_search_late() because they examine clause lists.

  if (!flag(Opt->quiet))
    printf("\nTerm ordering decisions:\n");

  if (stringparm(Opt->order, "lpo")) {
    assign_order_method(LPO_METHOD);
    all_symbols_lrpo_status(LRPO_LR_STATUS);
    set_lrpo_status(str_to_sn(eq_sym(), 2), LRPO_MULTISET_STATUS);
  }
  else if (stringparm(Opt->order, "rpo")) {
    assign_order_method(RPO_METHOD);
    all_symbols_lrpo_status(LRPO_MULTISET_STATUS);
  }
  else if (stringparm(Opt->order, "kbo")) {
    assign_order_method(KBO_METHOD);
  }

}  /* init_search_early */

/*************
 *
 *   init_search_late()
 *
 *   Phase 2 of search initialization.  These steps depend on
 *   Glob.sos/usable/demods being populated and on Glob.equality/horn/unit
 *   being set by basic_clause_properties().
 *
 *************/

static
void init_search_late(void)
{
  /* On resume, skip all clause-dependent initialization.  The checkpoint
     captures the final state of precedence, KBO weights, unfold symbols,
     and inference/process flags.  load_checkpoint_into_loop() calls
     symbol_order() on the loaded clauses.  Only the package option calls
     (resolution_options, paramodulation_options) are needed here. */
  if (Resume_dir != NULL)
    goto package_options;

  // Symbol precedence (examines clauses)

  symbol_order(Glob.usable, Glob.sos, Glob.demods, !flag(Opt->quiet));

  if (flag(Opt->multi_order_trial))
    multi_order_trial(Glob.usable, Glob.sos, !flag(Opt->quiet));

  if (Glob.kbo_weights) {
    if (!stringparm(Opt->order, "kbo")) {
      assign_stringparm(Opt->order, "kbo", TRUE);
      if (!flag(Opt->quiet))
        printf("assign(order, kbo), because KB weights were given.\n");
    }
    init_kbo_weights(Glob.kbo_weights);
    if (!flag(Opt->quiet))
      print_kbo_weights(stdout);
  }
  else if (stringparm(Opt->order, "kbo")) {
    auto_kbo_weights(Glob.usable, Glob.sos);
    if (!flag(Opt->quiet))
      print_kbo_weights(stdout);
  }

  if (!flag(Opt->quiet)) {
    print_rsym_precedence(stdout);
    print_fsym_precedence(stdout);
  }

  if (flag(Opt->inverse_order)) {
    if (exists_preliminary_precedence(FUNCTION_SYMBOL)) {  // lex command
      if (!flag(Opt->quiet))
	printf("Skipping inverse_order, because there is a function_order (lex) command.\n");
    }
    else if (stringparm(Opt->order, "kbo")) {
      if (!flag(Opt->quiet))
	printf("Skipping inverse_order, because term ordering is KBO.\n");
    }
    else {
      BOOL change = inverse_order(Glob.sos);
      if (!flag(Opt->quiet)) {
	printf("After inverse_order: ");
	if (change)
	  print_fsym_precedence(stdout);
	else
	  printf(" (no changes).\n");
      }
    }
  }

  if (stringparm(Opt->eq_defs, "unfold")) {
    if (exists_preliminary_precedence(FUNCTION_SYMBOL)) {  // lex command
      if (!flag(Opt->quiet))
	printf("Skipping unfold_eq, because there is a function_order (lex) command.\n");
    }
    else
      unfold_eq_defs(Glob.sos, INT_MAX, 3, !flag(Opt->quiet));
  }
  else if (stringparm(Opt->eq_defs, "fold")) {
    if (exists_preliminary_precedence(FUNCTION_SYMBOL)) {  // lex command
      if (!flag(Opt->quiet))
	printf("Skipping fold_eq, because there is a function_order (lex) command.\n");
    }
    else {
      BOOL change = fold_eq_defs(Glob.sos, stringparm(Opt->order, "kbo"));
      if (!flag(Opt->quiet)) {
	printf("After fold_eq: ");
	if (change)
	  print_fsym_precedence(stdout);
	else
	  printf(" (no changes).\n");
      }
    }
  }

  // Automatic inference and processing settings

  if (flag(Opt->auto_inference))
    auto_inference(Glob.sos, Glob.usable, Opt);

  if (flag(Opt->auto_process))
    auto_process(Glob.sos, Glob.usable, Opt);

  // Tell packages about options and other things.

package_options:
  resolution_options(flag(Opt->ordered_res),
		     flag(Opt->check_res_instances),
		     flag(Opt->initial_nuclei),
		     parm(Opt->ur_nucleus_limit),
		     flag(Opt->eval_rewrite));

  paramodulation_options(flag(Opt->ordered_para),
			 flag(Opt->check_para_instances),
			 FALSE,
			 flag(Opt->basic_paramodulation),
			 flag(Opt->para_from_vars),
			 flag(Opt->para_into_vars),
			 flag(Opt->para_from_small));

}  /* init_search_late */

/*************
 *
 *   init_search()
 *
 *   Full search initialization (both phases).
 *   Used by the normal (non-resume) path where clauses are already loaded.
 *
 *************/

static
void init_search(void)
{
  init_search_early();
  init_search_late();
}  /* init_search */

/*************
 *
 *   index_and_process_initial_clauses()
 *
 *************/

static
void index_and_process_initial_clauses(void)
{
  Clist_pos p;
  Clist temp_sos;

  // Index Usable clauses if hyper, UR, or binary-res are set.

  Glob.use_clash_idx = (flag(Opt->binary_resolution) ||
			flag(Opt->neg_binary_resolution) ||
			flag(Opt->pos_hyper_resolution) ||
			flag(Opt->neg_hyper_resolution) ||
			flag(Opt->pos_ur_resolution) ||
			flag(Opt->neg_ur_resolution));

  // Allocate and initialize indexes (even if they won't be used).

  set_fpa_hash_threshold(parm(Opt->fpa_hash_threshold));
  set_discrim_hash_threshold(parm(Opt->discrim_hash_threshold));

  int fpa_depth = parm(Opt->fpa_depth);
  init_literals_index(fpa_depth);  // fsub, bsub, fudel, budel, ucon

  init_demodulator_index(DISCRIM_BIND, ORDINARY_UNIF, 0);

  init_back_demod_index(FPA, ORDINARY_UNIF, fpa_depth);

  Glob.clashable_idx = lindex_init(FPA, ORDINARY_UNIF, fpa_depth,
				   FPA, ORDINARY_UNIF, fpa_depth);

  init_hints(ORDINARY_UNIF, Att.bsub_hint_wt,
	     flag(Opt->collect_hint_labels),
	     flag(Opt->back_demod_hints),
	     parm(Opt->hints_fpa_depth),
	     demodulate_clause);
  set_hint_match_stats(flag(Opt->hint_match_stats));
  set_hint_match_once(flag(Opt->hint_match_once));
  init_semantics(Glob.interps, Clocks.semantics,
		 stringparm1(Opt->multiple_interps),
		 parm(Opt->eval_limit),
		 parm(Opt->eval_var_limit));

  // Do Sos and Denials last, in case we PROCESS_INITIAL_SOS.

  ////////////////////////////////////////////////////////////////////////////
  // Usable

  for (p = Glob.usable->first; p != NULL; p = p->next) {
    Topform c = p->c;
    assign_clause_id(c);
    mark_maximal_literals(c->literals);
    mark_selected_literals(c->literals, stringparm1(Opt->literal_selection));
    if (flag(Opt->dont_flip_input))
      orient_equalities(c, FALSE);  // mark, but don't allow flips
    else
      c = orient_input_eq(c);  /* this replaces c if any flipping occurs */
    index_literals(c, INSERT, Clocks.index, FALSE);
    index_back_demod(c, INSERT, Clocks.index, flag(Opt->back_demod));
    index_clashable(c, INSERT);
  }

  ////////////////////////////////////////////////////////////////////////////
  // Demodulators

  if (!clist_empty(Glob.demods) && !flag(Opt->eval_rewrite)) {
    fflush(stdout);
    bell(stderr);
    fprintf(stderr,
	    "\nWARNING: The use of input demodulators is not well tested\n"
	    "and discouraged.  You might need to clear(process_initial_sos)\n"
	    "so that sos clauses are not rewritten and deleted.\n");
    fflush(stderr);
  }

  for (p = Glob.demods->first; p != NULL; p = p->next) {
    Topform c = p->c;
    assign_clause_id(c);
    if (flag(Opt->eval_rewrite)) {
      if (c->is_formula) {
	/* make it into a pseudo-clause */
	c->literals = new_literal(TRUE, formula_to_term(c->formula));
	upward_clause_links(c);
	zap_formula(c->formula);
	c->formula = NULL;
	c->is_formula = FALSE;
	clause_set_variables(c, MAX_VARS);
	mark_oriented_eq(c->literals->atom);
      }
    }
    else {
      if (!pos_eq_unit(c->literals))
	fatal_error("input demodulator is not equation");
      else {
	int type;
	if (flag(Opt->dont_flip_input))
	  orient_equalities(c, FALSE);  /* don't allow flips */
	else
	  c = orient_input_eq(c);  /* this replaces c if any flipping occurs */
	if (c->justification->next != NULL) {
	  if (!flag(Opt->quiet)) {
	    printf("\nNOTE: input demodulator %llu has been flipped.\n", c->id);
	    fflush(stdout);
	  }
	  fprintf(stderr, "\nNOTE: input demodulator %llu has been flipped.\n",
		  c->id);
	  if (flag(Opt->bell))
	    bell(stderr);
	  fflush(stderr);
	}
	type = demodulator_type(c,
				parm(Opt->lex_dep_demod_lim),
				flag(Opt->lex_dep_demod_sane));
	if (flag(Opt->dont_flip_input) &&
	    type != ORIENTED &&
	    !renamable_flip_eq(c->literals->atom)) {
	  type = ORIENTED;  /* let the user beware */
	  mark_oriented_eq(c->literals->atom);
	  bell(stderr);
	  fprintf(stderr,"\nWARNING: demodulator does not satisfy term order\n");
	  fflush(stderr);
	  if (!flag(Opt->quiet)) {
	    printf("\nWARNING: demodulator does not satisfy term order: ");
	    f_clause(c);
	    fflush(stdout);
	  }
	}
	else if (type == NOT_DEMODULATOR) {
	  Term a = ARG(c->literals->atom,0);
	  Term b = ARG(c->literals->atom,1);
	  if (!flag(Opt->quiet)) {
	    printf("bad input demodulator: "); f_clause(c);
	  }
	  if (term_ident(a, b))
	    fatal_error("input demodulator is instance of x=x");
	  else if (!variables_subset(a, b) && !variables_subset(b, a))
	    fatal_error("input demoulator does not have var-subset property");
	  else
	    fatal_error("input demoulator not allowed");
	}
	index_demodulator(c, type, INSERT, Clocks.index);
      }
    }
  }

  if (flag(Opt->eval_rewrite))
    init_dollar_eval(Glob.demods);

  ////////////////////////////////////////////////////////////////////////////
  // Hints
  
  if (Glob.hints->first) {
    int hint_id_number = 1;
    for (p = Glob.hints->first; p != NULL; p = p->next) {
      Topform h = p->c;
      h->id = hint_id_number++;
      orient_equalities(h, TRUE);
      renumber_variables(h, MAX_VARS);
      index_hint(h);
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  // Sos

  // Move Sos to a temporary list, then process that temporary list,
  // putting the clauses back into Sos in the "correct" way, either
  // by calling cl_process() or doing it here.

  temp_sos = Glob.sos;                    // move Sos to a temporary list
  name_clist(temp_sos, "temp_sos");       // not really necessary
  Glob.sos = clist_init("sos");           // get a new (empty) Sos list

  if (flag(Opt->process_initial_sos)) {

    int rp_interval = parm(Opt->report_preprocessing);
    int rp_total = temp_sos->length;
    int rp_count = 0;
    double rp_next = (rp_interval > 0) ? user_seconds() + rp_interval : -1;

    if (flag(Opt->print_initial_clauses))
      printf("\n");

    while (temp_sos->first) {
      Topform c = temp_sos->first->c;
      Topform new;
      clist_remove(c, temp_sos);
      clist_append(c, Glob.disabled);

      new = copy_inference(c);  // c has no ID, so this is tricky
      cl_process_simplify(new);
      if (new->justification->next == NULL) {
	// No simplification occurred, so make it a clone of the parent.
	zap_just(new->justification);
	new->justification = copy_justification(c->justification);
	// Get all attributes, not just inheritable ones.
	zap_attributes(new->attributes);
	new->attributes = copy_attributes(c->attributes);
      }
      else {
	// Simplification occurs, so make it a child of the parent.
	assign_clause_id(c);
	new->justification->u.id = c->id;
	// Copy SInE depth attribute from parent (not inheritable).
	new->attributes = copy_int_attribute(c->attributes,
					     new->attributes,
					     sine_depth_attr());
	if (flag(Opt->print_initial_clauses)) {
	  printf("%s           ", TPTP_PFX);
	  fwrite_clause(stdout, c, CL_FORM_STD);
	}
      }
      cl_process(new);  // This re-simplifies, but that's ok.

      rp_count++;
      if (rp_next > 0 && (rp_count % 1000) == 0) {
	double now = user_seconds();
	if (now >= rp_next) {
	  fprintf(stderr,
		  "NOTE: preprocessing processed %d of %d sos clauses, "
		  "kept %llu (%.1f sec, %lld MB)\n",
		  rp_count, rp_total, Stats.kept, now, megs_malloced());
	  fflush(stderr);
	  rp_next = now + rp_interval;
	}
      }
    }
    // This will put processed clauses back into Sos.
    limbo_process(TRUE);  // back subsumption and back demodulation.

  }
  else {
    /* not processing initial sos */
    fflush(stdout);
    bell(stderr);
    fprintf(stderr,
	    "\nWARNING: clear(process_initial_sos) is not well tested.\n"
	    "We usually recommend against using it.\n");
    fflush(stderr);
    
    /* not applying full processing to initial sos */
    while (temp_sos->first) {
      Topform c = temp_sos->first->c;
      clist_remove(c, temp_sos);

      if (number_of_literals(c->literals) == 0)
	/* in case $F is in input, or if predicate elimination finds proof */
	handle_proof_and_maybe_exit(c);
      else {
	assign_clause_id(c);
	if (flag(Opt->dont_flip_input))
	  orient_equalities(c, FALSE);
	else
	  c = orient_input_eq(c);
	mark_maximal_literals(c->literals);
	mark_selected_literals(c->literals,
			       stringparm1(Opt->literal_selection));
	c->weight = clause_weight(c->literals);
	if (!clist_empty(Glob.hints)) {
	  clock_start(Clocks.hints);
	  adjust_weight_with_hints(c,
				   flag(Opt->degrade_hints),
				   flag(Opt->breadth_first_hints));
	  clock_stop(Clocks.hints);
	}

	c->initial = TRUE;
	insert_into_sos2(c, Glob.sos);
	index_literals(c, INSERT, Clocks.index, FALSE);
	index_back_demod(c, INSERT, Clocks.index, flag(Opt->back_demod));
      }
    }
  }

  clist_zap(temp_sos);  // free the temporary list

  {
    int rp_interval = parm(Opt->report_preprocessing);
    if (rp_interval > 0) {
      fprintf(stderr,
	      "NOTE: preprocessing writing initial clauses to output"
	      " (%.1f sec, %lld MB)\n",
	      user_seconds(), megs_malloced());
      fflush(stderr);
    }
  }

  ////////////////////////////////////////////////////////////////////////////
  // Print

  if (!flag(Opt->quiet)) {
    print_separator(stdout, "end of process initial clauses", TRUE);
    print_separator(stdout, "CLAUSES FOR SEARCH", TRUE);
  }

  if (flag(Opt->print_initial_clauses)) {
    printf("\n%% Clauses after input processing:\n");
    fwrite_clause_clist(stdout,Glob.usable,  CL_FORM_STD);
    fwrite_clause_clist(stdout,Glob.sos,     CL_FORM_STD);
    fwrite_demod_clist(stdout,Glob.demods,   CL_FORM_STD);
  }
  if (!flag(Opt->quiet) && Glob.hints->length > 0) {
      int redundant = redundant_hints();
      printf("\n%% %d hints (%d processed, %d redundant).\n",
	     Glob.hints->length - redundant, Glob.hints->length, redundant);
    }

  if (!flag(Opt->quiet))
    print_separator(stdout, "end of clauses for search", TRUE);

  {
    int rp_interval = parm(Opt->report_preprocessing);
    if (rp_interval > 0) {
      fprintf(stderr,
	      "NOTE: preprocessing finished, entering search"
	      " (%.1f sec, %lld MB)\n",
	      user_seconds(), megs_malloced());
      fflush(stderr);
    }
  }

}  // index_and_process_initial_clauses

/*************
 *
 *   fatal_setjmp()
 *
 *************/

static
void fatal_setjmp(void)
{
  int return_code = setjmp(Jump_env);
  if (return_code != 0)
    fatal_error("longjmp called outside of search");
}  /* fatal_setjmp */

/*************
 *
 *   collect_prover_results()
 *
 *************/

static
Prover_results collect_prover_results(BOOL xproofs)
{
  Plist p;
  Prover_results results = safe_calloc(1, sizeof(struct prover_results));

  for (p = Glob.empties; p; p = p->next) {
    Plist proof = get_clause_ancestors(p->v);
    uncompress_clauses(proof);
    results->proofs = plist_append(results->proofs, proof);
    if (xproofs) {
      Plist xproof = proof_to_xproof(proof);
      results->xproofs = plist_append(results->xproofs, xproof);
    }
  }
  update_stats();  /* puts package stats into Stats */
  results->stats = Stats;  /* structure copy */
  results->user_seconds = user_seconds();
  results->system_seconds = system_seconds();
  results->return_code = Glob.return_code;
  return results;
}  /* collect_prover_results */

/*************
 *
 *   zap_prover_results()
 *
 *************/

/* DOCUMENTATION
Free the dynamically allocated memory associated with a Prover_result.
*/

/* PUBLIC */
void zap_prover_results(Prover_results results)
{
  Plist a, b;  /* results->proofs is a Plist of Plist of clauses */
  for (a = results->proofs; a; a = a->next) {
    for (b = a->v; b; b = b->next) {
      Topform c = b->v;
      /* There is a tricky thing going on with the ID.  If you try
	 to delete a clause with an ID not in the clause ID table,
	 a fatal error occurs.  If IDs in these clauses came from
	 a child process, they will not be in the table.  Setting
	 the ID to 0 gets around that problem.
       */
      c->id = 0;
      delete_clause(c);  /* zaps justification, attributes */
    }
  }
  safe_free(results);
}  /* zap_prover_results */

/*************
 *
 *   basic_clause_properties()
 *
 *************/

static
void basic_clause_properties(Clist sos, Clist usable)
{
  Plist sos_temp    = copy_clist_to_plist_shallow(sos);
  Plist usable_temp = copy_clist_to_plist_shallow(usable);

  Glob.equality = 
    pos_equality_in_clauses(sos_temp) || pos_equality_in_clauses(usable_temp);
    
  Glob.unit =
    all_clauses_unit(sos_temp) && all_clauses_unit(usable_temp);

  Glob.horn =
    all_clauses_horn(sos_temp) && all_clauses_horn(usable_temp);

  Glob.number_of_clauses =
    plist_count(sos_temp) + plist_count(usable_temp);

  Glob.number_of_neg_clauses =
    negative_clauses(sos_temp) + negative_clauses(usable_temp);

  zap_plist(sos_temp);
  zap_plist(usable_temp);
}  /* basic_clause_properties */

/*************
 *
 *   write_clist_bare()
 *
 *   Write clauses from a Clist in CL_FORM_BARE format.
 *   Also writes clause_data lines to data_fp.
 *
 *************/

static
int write_clist_bare(FILE *clause_fp, FILE *data_fp,
                     Clist lst, const char *list_name,
                     Plist *seen_tab, int seen_tab_size)
{
  Clist_pos p;
  int file_pos = 0;  /* position in .clauses file (non-shared only) */
  int list_pos = 0;  /* position in original list (all entries) */
  for (p = lst->first; p != NULL; p = p->next) {
    Topform c = p->c;
    if (c->id == 0)
      continue;  /* skip clauses without IDs (e.g. unprocessed disabled) */
    /* Write-side dedup: if clause was already written to another list,
       mark as shared in clause_data and skip the clause text. */
    {
      int is_shared = (seen_tab != NULL && clause_plist_member(
              seen_tab[c->id % seen_tab_size], c, TRUE));
      if (!is_shared) {
        if (seen_tab != NULL)
          seen_tab[c->id % seen_tab_size] =
              insert_clause_into_plist(
                  seen_tab[c->id % seen_tab_size], c, TRUE);
        fwrite_clause(clause_fp, c, CL_FORM_BARE);
      }
      /* Position field: file_pos for non-shared (matches .clauses file),
         list_pos for shared (used by interleaving logic on restore). */
      fprintf(data_fp, "%s %d %llu %.17g %d", list_name,
              is_shared ? list_pos : file_pos,
              c->id, c->weight, (int)c->initial);
      if (is_shared)
        fprintf(data_fp, " shared");
      if (c->matching_hint != NULL)
        fprintf(data_fp, " hint_match %d", (int)c->matching_hint->id);
      if (c->used)
        fprintf(data_fp, " used");
      if (c->was_given)
        fprintf(data_fp, " was_given");
      if (c->last_matched_given > 0)
        fprintf(data_fp, " last_matched %llu", c->last_matched_given);
      if (strcmp(list_name, "hints") == 0 && hint_is_redundant(c))
        fprintf(data_fp, " redundant_hint");
      /* Save atom private_flags for each literal (carries oriented_eq,
         renamable_flip, maximal, selected marks — lost in text round-trip) */
      {
        Literals lit;
        for (lit = c->literals; lit != NULL; lit = lit->next)
          fprintf(data_fp, " aflags %u", (unsigned)lit->atom->private_flags);
      }
      fprintf(data_fp, "\n");
      if (!is_shared)
        file_pos++;
    }
    list_pos++;
  }
  fprintf(clause_fp, "end_of_list.\n");
  return list_pos;
}  /* write_clist_bare */

/*************
 *
 *   Checkpoint verification hashes.
 *
 *   XOR-rotate hash of clause IDs in list order.  Two lists with the
 *   same clauses in the same order produce the same hash.  Used by
 *   set(checkpoint_verify) to detect restore divergence.
 *
 *************/

static
unsigned long long hash_clist_ids(Clist lst)
{
  unsigned long long h = 0;
  Clist_pos p;
  for (p = lst->first; p != NULL; p = p->next) {
    h ^= p->c->id;
    h = (h << 7) | (h >> 57);  /* rotate left 7 */
  }
  return h;
}

static
unsigned long long hash_clist_fpa_ids(Clist lst)
{
  unsigned long long h = 0;
  Clist_pos p;
  for (p = lst->first; p != NULL; p = p->next) {
    Literals lit;
    for (lit = p->c->literals; lit; lit = lit->next) {
      /* Walk atom DFS, hash FPA_IDs (skip variables -- shared objects) */
      Term stack[1000];
      int top = 0;
      stack[top++] = lit->atom;
      while (top > 0) {
        Term t = stack[--top];
        int i;
        /* Only hash non-zero FPA_IDs (root atoms that were FPA-indexed).
           Variables and subterms keep FPA_ID=0 and may change due to
           shared variable replacement during hint renumbering. */
        if (FPA_ID(t) != 0)
          h ^= (unsigned long long) FPA_ID(t);
        h = (h << 5) | (h >> 59);
        for (i = ARITY(t) - 1; i >= 0; i--)
          stack[top++] = ARG(t, i);
      }
    }
  }
  return h;
}

static
unsigned long long hash_clist_hint_matches(Clist lst)
{
  unsigned long long h = 0;
  Clist_pos p;
  for (p = lst->first; p != NULL; p = p->next) {
    unsigned long long hint_id = p->c->matching_hint
        ? p->c->matching_hint->id : 0;
    h ^= (p->c->id * 2654435761ULL) ^ hint_id;
    h = (h << 11) | (h >> 53);
  }
  return h;
}

static
void write_checkpoint_hashes(const char *dir)
{
  char path[600];
  FILE *fp;

  snprintf(path, sizeof(path), "%s/verify.txt", dir);
  fp = fopen(path, "w");
  if (!fp) return;

  fprintf(fp, "sos_ids %llu\n",       hash_clist_ids(Glob.sos));
  fprintf(fp, "usable_ids %llu\n",    hash_clist_ids(Glob.usable));
  fprintf(fp, "demods_ids %llu\n",    hash_clist_ids(Glob.demods));
  fprintf(fp, "hints_ids %llu\n",     hash_clist_ids(Glob.hints));
  fprintf(fp, "limbo_ids %llu\n",     hash_clist_ids(Glob.limbo));
  fprintf(fp, "sos_fpa %llu\n",       hash_clist_fpa_ids(Glob.sos));
  fprintf(fp, "usable_fpa %llu\n",    hash_clist_fpa_ids(Glob.usable));
  fprintf(fp, "hints_fpa %llu\n",     hash_clist_fpa_ids(Glob.hints));
  fprintf(fp, "limbo_fpa %llu\n",     hash_clist_fpa_ids(Glob.limbo));
  fprintf(fp, "sos_hints %llu\n",     hash_clist_hint_matches(Glob.sos));
  fprintf(fp, "usable_hints %llu\n",  hash_clist_hint_matches(Glob.usable));
  fprintf(fp, "sos_count %d\n",       Glob.sos->length);
  fprintf(fp, "usable_count %d\n",    Glob.usable->length);
  fprintf(fp, "demods_count %d\n",    Glob.demods->length);
  fprintf(fp, "hints_count %d\n",     Glob.hints->length);
  fprintf(fp, "limbo_count %d\n",     Glob.limbo->length);

  fclose(fp);
}

static
void verify_checkpoint_hashes(const char *dir)
{
  char path[600], key[64];
  unsigned long long val;
  FILE *fp;
  int pass = 0, fail = 0;

  snprintf(path, sizeof(path), "%s/verify.txt", dir);
  fp = fopen(path, "r");
  if (!fp) {
    printf("%% checkpoint_verify: no verify.txt in checkpoint.\n");
    return;
  }

  printf("\n%% Checkpoint verification:\n");
  while (fscanf(fp, " %63s %llu", key, &val) == 2) {
    unsigned long long actual = 0;
    const char *status;

    if (strcmp(key, "sos_ids") == 0)
      actual = hash_clist_ids(Glob.sos);
    else if (strcmp(key, "usable_ids") == 0)
      actual = hash_clist_ids(Glob.usable);
    else if (strcmp(key, "demods_ids") == 0)
      actual = hash_clist_ids(Glob.demods);
    else if (strcmp(key, "hints_ids") == 0)
      actual = hash_clist_ids(Glob.hints);
    else if (strcmp(key, "limbo_ids") == 0)
      actual = hash_clist_ids(Glob.limbo);
    else if (strcmp(key, "sos_fpa") == 0)
      actual = hash_clist_fpa_ids(Glob.sos);
    else if (strcmp(key, "usable_fpa") == 0)
      actual = hash_clist_fpa_ids(Glob.usable);
    else if (strcmp(key, "hints_fpa") == 0)
      actual = hash_clist_fpa_ids(Glob.hints);
    else if (strcmp(key, "limbo_fpa") == 0)
      actual = hash_clist_fpa_ids(Glob.limbo);
    else if (strcmp(key, "sos_hints") == 0)
      actual = hash_clist_hint_matches(Glob.sos);
    else if (strcmp(key, "usable_hints") == 0)
      actual = hash_clist_hint_matches(Glob.usable);
    else if (strcmp(key, "sos_count") == 0)
      actual = (unsigned long long) Glob.sos->length;
    else if (strcmp(key, "usable_count") == 0)
      actual = (unsigned long long) Glob.usable->length;
    else if (strcmp(key, "demods_count") == 0)
      actual = (unsigned long long) Glob.demods->length;
    else if (strcmp(key, "hints_count") == 0)
      actual = (unsigned long long) Glob.hints->length;
    else if (strcmp(key, "limbo_count") == 0)
      actual = (unsigned long long) Glob.limbo->length;
    else
      continue;

    status = (actual == val) ? "OK" : "MISMATCH";
    if (actual != val) {
      printf("%%   %s: %s (expected %llu, got %llu)\n",
             key, status, val, actual);
      fail++;
    }
    else {
      printf("%%   %s: %s\n", key, status);
      pass++;
    }
  }
  fclose(fp);

  printf("%%   Verification: %d passed, %d failed.\n", pass, fail);
  fflush(stdout);
  if (fail > 0) {
    fprintf(stderr, "FATAL: checkpoint verification failed (%d mismatches).\n"
            "The checkpoint data does not match the restored state.\n", fail);
    fatal_error("checkpoint_verify: verification failed");
  }
}

/*************
 *
 *   write_term_fpa_ids()
 *
 *   Write FPA_ID for a term and all subterms (pre-order DFS).
 *   Returns the number of IDs written.
 *
 *************/

static
int write_term_fpa_ids(FILE *fp, Term t)
{
  int i, count = 1;
  /* Skip variables: they are shared objects whose FPA_ID depends on
     indexing order, not on individual clause state.  Write 0 for vars. */
  fprintf(fp, " %u", VARIABLE(t) ? 0 : (unsigned) FPA_ID(t));
  for (i = 0; i < ARITY(t); i++)
    count += write_term_fpa_ids(fp, ARG(t, i));
  return count;
}  /* write_term_fpa_ids */

/*************
 *
 *   write_fpa_ids()
 *
 *   Write FPA_IDs for all terms in the given clause lists to a file.
 *   Section-based format keyed by list position (not clause ID):
 *     fpa_id_count <N>
 *     LIST <name> <count>
 *     <term_count> <id1> <id2> ... <idN>
 *     ...
 *
 *************/

static
void write_fpa_ids(const char *dir)
{
  char path[600];
  FILE *fp;
  Clist_pos p;

  snprintf(path, sizeof(path), "%s/fpa_ids.txt", dir);
  fp = fopen(path, "w");
  if (!fp) {
    fprintf(stderr, "WARNING: cannot write %s\n", path);
    return;
  }

  fprintf(fp, "fpa_id_count %u\n", get_fpa_id_count());

  /* Save shared variable FPA_IDs.  Variables are shared across all
     clauses, so their FPA_IDs must be saved/restored separately. */
  {
    int i, nvar = 0;
    for (i = 0; i < MAX_VNUM; i++)
      if (get_variable_term_if_exists(i) != NULL)
        nvar = i + 1;
    fprintf(fp, "VARS %d\n", nvar);
    for (i = 0; i < nvar; i++) {
      Term v = get_variable_term_if_exists(i);
      fprintf(fp, " %u", v != NULL ? (unsigned) FPA_ID(v) : 0);
    }
    fprintf(fp, "\n");
  }

  /* Save FPA_IDs for all FPA-indexed clause lists:
     usable, sos, hints, limbo (demods use DISCRIM, not FPA).
     Section-based: reader iterates by list position, not clause ID. */
  {
    const char *names[] = {"usable", "sos", "hints", "limbo"};
    Clist lists[] = {Glob.usable, Glob.sos, Glob.hints, Glob.limbo};
    int nlist = 4, i;
    for (i = 0; i < nlist; i++) {
      fprintf(fp, "LIST %s %d\n", names[i], lists[i]->length);
      for (p = lists[i]->first; p != NULL; p = p->next) {
        Topform c = p->c;
        Literals lit;
        int term_count = 0;
        for (lit = c->literals; lit; lit = lit->next)
          term_count += symbol_count(lit->atom);
        fprintf(fp, "%d", term_count);
        for (lit = c->literals; lit; lit = lit->next)
          write_term_fpa_ids(fp, lit->atom);
        fprintf(fp, "\n");
      }
    }
  }

  fclose(fp);
}  /* write_fpa_ids */

/*************
 *
 *   read_term_fpa_ids()
 *
 *   Read FPA_IDs for a term and all subterms (pre-order DFS).
 *   Returns the number of IDs read.
 *
 *************/

static
int read_term_fpa_ids(FILE *fp, Term t)
{
  unsigned id;
  int i, count = 1;
  if (fscanf(fp, " %u", &id) != 1)
    fatal_error("restore_fpa_ids: unexpected end of data");
  /* Skip variables: they are shared objects.  Don't write to them. */
  if (!VARIABLE(t))
    FPA_ID(t) = id;
  for (i = 0; i < ARITY(t); i++)
    count += read_term_fpa_ids(fp, ARG(t, i));
  return count;
}  /* read_term_fpa_ids */

/*************
 *
 *   restore_fpa_ids()
 *
 *   Read FPA_IDs from checkpoint directory and assign them to terms.
 *   Section-based format: iterates by list position, not clause ID.
 *   Must be called after resume_load_clauses() but before resume_index_clauses().
 *
 *************/

static
void restore_fpa_ids(const char *dir)
{
  char path[600], buf[64], list_name[32];
  FILE *fp;
  unsigned saved_count;
  int section_count, restored = 0, skipped = 0;

  snprintf(path, sizeof(path), "%s/fpa_ids.txt", dir);
  fp = fopen(path, "r");
  if (!fp) {
    fprintf(stderr, "NOTE: no fpa_ids.txt in checkpoint; "
            "FPA ordering may differ.\n");
    return;
  }

  /* Read the fpa_id_count header */
  if (fscanf(fp, " %63s %u", buf, &saved_count) != 2 ||
      strcmp(buf, "fpa_id_count") != 0)
    fatal_error("restore_fpa_ids: bad header in fpa_ids.txt");
  set_fpa_id_count(saved_count);

  /* Read sections (VARS or LIST) */
  while (fscanf(fp, " %63s", buf) == 1) {
    Clist lst;
    Clist_pos cp;
    int i;

    /* Restore shared variable FPA_IDs */
    if (strcmp(buf, "VARS") == 0) {
      int nvar;
      if (fscanf(fp, " %d", &nvar) != 1) break;
      for (i = 0; i < nvar; i++) {
        unsigned id;
        if (fscanf(fp, " %u", &id) != 1) break;
        if (id != 0) {
          Term v = get_variable_term(i);
          FPA_ID(v) = id;
        }
      }
      continue;
    }

    if (strcmp(buf, "LIST") != 0)
      break;  /* not a section header -- old format or corruption */
    if (fscanf(fp, " %31s %d", list_name, &section_count) != 2)
      break;

    /* Match list name to Glob list */
    lst = NULL;
    if (strcmp(list_name, "usable") == 0) lst = Glob.usable;
    else if (strcmp(list_name, "sos") == 0) lst = Glob.sos;
    else if (strcmp(list_name, "hints") == 0) lst = Glob.hints;
    else if (strcmp(list_name, "limbo") == 0) lst = Glob.limbo;

    if (lst == NULL || lst->length != section_count) {
      /* List mismatch -- skip this section's data */
      for (i = 0; i < section_count; i++) {
        int term_count, j;
        unsigned dummy;
        if (fscanf(fp, " %d", &term_count) != 1) break;
        for (j = 0; j < term_count; j++)
          fscanf(fp, " %u", &dummy);
      }
      skipped += section_count;
      continue;
    }

    /* Walk list by position, read FPA IDs for each clause */
    cp = lst->first;
    for (i = 0; i < section_count && cp != NULL; i++, cp = cp->next) {
      Topform c = cp->c;
      Literals lit;
      int term_count, actual_count;

      if (fscanf(fp, " %d", &term_count) != 1) break;

      /* Verify DFS node count matches */
      actual_count = 0;
      for (lit = c->literals; lit; lit = lit->next)
        actual_count += symbol_count(lit->atom);

      if (actual_count != term_count) {
        /* Term structure mismatch -- skip this clause's FPA IDs */
        int j;
        unsigned dummy;
        for (j = 0; j < term_count; j++)
          fscanf(fp, " %u", &dummy);
        skipped++;
        continue;
      }

      for (lit = c->literals; lit; lit = lit->next)
        read_term_fpa_ids(fp, lit->atom);
      restored++;
    }
  }

  fclose(fp);

  if (restored > 0)
    printf("%% Restored FPA_IDs for %d clauses (fpa_id_count=%u).\n",
           restored, saved_count);
  if (skipped > 0)
    printf("%% WARNING: skipped FPA_IDs for %d clauses (list mismatch).\n",
           skipped);
  fflush(stdout);
}  /* restore_fpa_ids */

/*************
 *
 *   remove_checkpoint_dir()
 *
 *   Safely remove a checkpoint directory (contains only regular files).
 *
 *************/

static void remove_checkpoint_dir(const char *path)
{
  DIR *d = opendir(path);
  if (!d) return;
  struct dirent *ent;
  char filepath[1024];
  while ((ent = readdir(d)) != NULL) {
    if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0)
      continue;
    snprintf(filepath, sizeof(filepath), "%s/%s", path, ent->d_name);
    unlink(filepath);
  }
  closedir(d);
  rmdir(path);
}  /* remove_checkpoint_dir */

#ifndef PRIMITIVE_ENVIRONMENT

/*************
 *
 *   record_auto_checkpoint()
 *
 *   Track an automatic checkpoint directory name in a circular buffer
 *   and rotate (delete) the oldest when the buffer is full.
 *
 *************/

static void record_auto_checkpoint(const char *dirname)
{
  int keep = parm(Opt->checkpoint_keep);

  /* Initialize or resize circular buffer if needed */
  if (Auto_ckpt_dirs == NULL || Auto_ckpt_capacity < keep) {
    int new_cap = keep;
    char **new_buf = safe_calloc(new_cap, sizeof(char *));
    /* Copy existing entries if any */
    int i;
    for (i = 0; i < Auto_ckpt_count && i < new_cap; i++) {
      int idx = (Auto_ckpt_head + i) % Auto_ckpt_capacity;
      new_buf[i] = Auto_ckpt_dirs[idx];
    }
    safe_free(Auto_ckpt_dirs);
    Auto_ckpt_dirs = new_buf;
    Auto_ckpt_head = 0;
    Auto_ckpt_capacity = new_cap;
    if (Auto_ckpt_count > new_cap)
      Auto_ckpt_count = new_cap;
  }

  /* If buffer is full, delete the oldest checkpoint directory */
  if (Auto_ckpt_count == keep) {
    int oldest = Auto_ckpt_head;
    if (Auto_ckpt_dirs[oldest]) {
      fprintf(stderr, "  Removing old checkpoint: %s\n", Auto_ckpt_dirs[oldest]);
      remove_checkpoint_dir(Auto_ckpt_dirs[oldest]);
      safe_free(Auto_ckpt_dirs[oldest]);
      Auto_ckpt_dirs[oldest] = NULL;
    }
    Auto_ckpt_head = (Auto_ckpt_head + 1) % Auto_ckpt_capacity;
    Auto_ckpt_count--;
  }

  /* Add new entry */
  int slot = (Auto_ckpt_head + Auto_ckpt_count) % Auto_ckpt_capacity;
  Auto_ckpt_dirs[slot] = strdup(dirname);
  Auto_ckpt_count++;
}  /* record_auto_checkpoint */

/*************
 *
 *   write_checkpoint_formulas()
 *
 *   Write non-clause formulas (e.g., goal formulas) from the clause ID
 *   hash table to the checkpoint directory.  These are needed for proof
 *   reconstruction because denial clauses reference goal formula IDs
 *   via [deny(N)] justifications.
 *
 *   Format: one entry per formula:
 *     <id>\n<formula_term>.\n<justification>.\n
 *
 *************/

static
void write_checkpoint_formulas(const char *dir)
{
  char path[600];
  FILE *fp;
  Plist formulas, p;

  formulas = collect_formulas_from_id_tab();
  if (formulas == NULL)
    return;

  snprintf(path, sizeof(path), "%s/formulas.txt", dir);
  fp = fopen(path, "w");
  if (!fp) {
    fprintf(stderr, "WARNING: cannot write %s\n", path);
    zap_plist(formulas);
    return;
  }

  for (p = formulas; p; p = p->next) {
    Topform c = p->v;
    Term t = topform_to_term(c);
    String_buf sb;

    /* Write ID on its own line */
    fprintf(fp, "%llu\n", c->id);

    /* Write formula term (with attributes) terminated by '.' */
    sb = get_string_buf();
    sb_write_term(sb, t);
    sb_append(sb, ".");
    fprint_sb(fp, sb);
    fprintf(fp, "\n");
    zap_string_buf(sb);
    zap_term(t);

    /* Write justification terminated by '.' */
    sb = get_string_buf();
    sb_write_just(sb, c->justification, NULL);  /* appends "]." */
    fprint_sb(fp, sb);
    fprintf(fp, "\n");
    zap_string_buf(sb);

  }

  fclose(fp);
  zap_plist(formulas);
}  /* write_checkpoint_formulas */

/*************
 *
 *   restore_checkpoint_formulas()
 *
 *   Read non-clause formulas (goals) from checkpoint and register them
 *   in the clause ID hash table.  Must be called before restore_justifications().
 *
 *************/

static
void restore_checkpoint_formulas(const char *dir)
{
  char path[600];
  FILE *fp;
  unsigned long long id;
  int count = 0;

  snprintf(path, sizeof(path), "%s/formulas.txt", dir);
  fp = fopen(path, "r");
  if (!fp) {
    /* Old checkpoint without formulas.txt — justification restore will
       still work but proofs may show [assumption] for goal-derived clauses. */
    return;
  }

  while (fscanf(fp, " %llu", &id) == 1) {
    Term formula_t = read_term(fp, stderr);  /* reads formula up to '.' */
    Term just_t    = read_term(fp, stderr);  /* reads justification up to '.' */
    Topform c;

    if (formula_t == NULL || just_t == NULL) {
      if (formula_t) zap_term(formula_t);
      if (just_t)    zap_term(just_t);
      break;
    }

    c = term_to_topform(formula_t, TRUE);  /* is_formula = TRUE */
    zap_term(formula_t);

    c->id = id;
    c->justification = term_to_just(just_t);
    zap_term(just_t);

    register_clause_with_id(c);
    count++;
  }

  fclose(fp);

  printf("%% Restored %d formulas from checkpoint.\n", count);
  fflush(stdout);
}  /* restore_checkpoint_formulas */

/*************
 *
 *   write_clist_justifications()
 *
 *   Write justifications for all clauses in a Clist to a file.
 *   Format: "<clause_id> <justification_term>\n"
 *   e.g., "17 [hyper(1,a,2,a)].\n"
 *
 *************/

static
void write_clist_justifications(FILE *fp, Clist lst)
{
  Clist_pos p;
  for (p = lst->first; p != NULL; p = p->next) {
    Topform c = p->c;
    if (c->id == 0 || c->justification == NULL)
      continue;
    {
      String_buf sb = get_string_buf();
      sb_write_just(sb, c->justification, NULL);
      fprintf(fp, "%llu ", c->id);
      fprint_sb(fp, sb);
      fprintf(fp, "\n");
      zap_string_buf(sb);
    }
  }
}  /* write_clist_justifications */

/*************
 *
 *   write_justifications()
 *
 *   Write justifications for all checkpoint clause lists to a file.
 *   Called from write_checkpoint().
 *
 *************/

static
void write_justifications(const char *dir)
{
  char path[600];
  FILE *fp;

  snprintf(path, sizeof(path), "%s/justifications.txt", dir);
  fp = fopen(path, "w");
  if (!fp) {
    fprintf(stderr, "WARNING: cannot write %s\n", path);
    return;
  }

  write_clist_justifications(fp, Glob.sos);
  write_clist_justifications(fp, Glob.usable);
  write_clist_justifications(fp, Glob.demods);
  if (Glob.hints->length > 0)
    write_clist_justifications(fp, Glob.hints);
  if (Glob.limbo->length > 0)
    write_clist_justifications(fp, Glob.limbo);
  if (flag(Opt->checkpoint_ancestors) && Glob.disabled->length > 0)
    write_clist_justifications(fp, Glob.disabled);

  fclose(fp);
}  /* write_justifications */

/*************
 *
 *   restore_justifications()
 *
 *   Read justifications from checkpoint directory and replace the
 *   input_just() placeholders assigned during clause loading.
 *   Must be called after resume_load_clauses().
 *
 *************/

static
void restore_justifications(const char *dir)
{
  char path[600];
  FILE *fp;
  unsigned long long id;
  int count = 0;

  snprintf(path, sizeof(path), "%s/justifications.txt", dir);
  fp = fopen(path, "r");
  if (!fp) {
    fprintf(stderr, "NOTE: no justifications.txt in checkpoint (old format); "
            "proof output will show [assumption] for checkpoint clauses.\n");
    return;
  }

  while (fscanf(fp, " %llu", &id) == 1) {
    Term t = read_term(fp, stderr);
    if (t == NULL)
      break;
    {
      Topform c = find_clause_by_id(id);
      if (c) {
        Just new_just = term_to_just(t);
        zap_term(t);
        zap_just(c->justification);
        c->justification = new_just;
        count++;
      }
      else {
        zap_term(t);
      }
    }
  }

  fclose(fp);

  printf("%% Restored justifications for %d clauses from checkpoint.\n", count);
  fflush(stdout);
}  /* restore_justifications */

/*************
 *
 *   write_checkpoint_input()
 *
 *   Write a synthetic LADR input file (saved_input.txt) into the checkpoint
 *   directory, capturing the current runtime options and configuration lists.
 *   This makes the checkpoint self-contained: resume works without the
 *   original input file.
 *
 *************/

static
void write_checkpoint_input(const char *dir)
{
  char path[600];
  FILE *fp;

  snprintf(path, sizeof(path), "%s/saved_input.txt", dir);
  fp = fopen(path, "w");
  if (!fp) return;

  fprintf(fp, "%% Saved input from checkpoint (auto-generated)\n");
  fprintf(fp, "%% Runtime state including auto-mode changes\n\n");

  /* Disable option dependencies during read-back.  The saved options
     represent the final runtime state (post-dependency-resolution), so
     re-triggering dependencies would produce incorrect cascading values
     (e.g. assign(max_minutes, -1) -> max_seconds = -60, fatal). */
  fprintf(fp, "set(ignore_option_dependencies).\n\n");

  /* Options — current runtime state (includes auto-mode changes).
     fwrite_options_input writes parseable set()/clear()/assign() commands
     without the banner line (which would confuse the LADR parser). */
  fwrite_options_input(fp);
  /* Auto-mode flags have already been resolved at checkpoint time.
     Prevent re-running auto_inference/auto_process on resume, which
     would make incorrect decisions with different (empty) clause lists. */
  fprintf(fp, "clear(auto_inference).\n");
  fprintf(fp, "clear(auto_process).\n");
  fprintf(fp, "\n");

  /* Configuration lists — only write non-empty ones.
     fwrite_term_list writes list(name). term. ... end_of_list. format. */
  if (Glob.weights)
    fwrite_term_list(fp, Glob.weights, "weights");
  if (Glob.kbo_weights)
    fwrite_term_list(fp, Glob.kbo_weights, "kbo_weights");
  else if (stringparm(Opt->order, "kbo")) {
    /* KBO with auto-generated weights: reconstruct list(kbo_weights) from
       current symbol table so the resume process gets the exact weights
       instead of re-running auto_kbo_weights on empty clause lists. */
    Ilist fsyms = current_fsym_precedence();
    Ilist p;
    BOOL any_nondefault = FALSE;
    for (p = fsyms; p; p = p->next) {
      if (sn_to_kb_wt(p->i) != 1) { any_nondefault = TRUE; break; }
    }
    if (any_nondefault) {
      fprintf(fp, "\nlist(kbo_weights).\n");
      for (p = fsyms; p; p = p->next) {
        if (sn_to_kb_wt(p->i) != 1)
          fprintf(fp, "%s = %d.\n", sn_to_str(p->i), sn_to_kb_wt(p->i));
      }
      fprintf(fp, "end_of_list.\n");
    }
    zap_ilist(fsyms);
  }
  if (Glob.actions)
    fwrite_term_list(fp, Glob.actions, "actions");
  if (Glob.interps)
    fwrite_term_list(fp, Glob.interps, "interpretations");
  if (Glob.given_selection)
    fwrite_term_list(fp, Glob.given_selection, "given_selection");
  if (Glob.keep_rules)
    fwrite_term_list(fp, Glob.keep_rules, "keep");
  if (Glob.delete_rules)
    fwrite_term_list(fp, Glob.delete_rules, "delete");

  fclose(fp);
}  /* write_checkpoint_input */

/*************
 *
 *   write_checkpoint()
 *
 *   Write the current search state to a checkpoint directory.
 *
 *************/

static
void write_checkpoint(void)
{
  char tmpdir[520], finaldir[512];
  FILE *fp;
  int n;

  /* Build directory names */
  n = snprintf(finaldir, sizeof(finaldir),
               "prover9_%d_ckpt_%llu", getpid(), Stats.given);
  if (n < 0 || n >= (int)sizeof(finaldir))
    fatal_error("write_checkpoint: directory name too long");

  snprintf(tmpdir, sizeof(tmpdir), "%s.tmp", finaldir);

  /* Remove stale temp dir if it exists, then create */
  rmdir(tmpdir);  /* ignore errors */
  if (mkdir(tmpdir, 0755) != 0) {
    fprintf(stderr, "ERROR: cannot create checkpoint directory %s: %s\n",
            tmpdir, strerror(errno));
    return;
  }

  /* 1. Write metadata.txt */
  {
    char path[600];
    snprintf(path, sizeof(path), "%s/metadata.txt", tmpdir);
    fp = fopen(path, "w");
    if (!fp) { fprintf(stderr, "ERROR: cannot write %s\n", path); return; }

    fprintf(fp, "checkpoint_format 3\n");
    fprintf(fp, "version %s\n", PROGRAM_VERSION);
    fprintf(fp, "date %s\n", PROGRAM_DATE);
    fprintf(fp, "max_clause_id %llu\n", clause_ids_assigned());
    fprintf(fp, "given %llu\n", Stats.given);
    fprintf(fp, "generated %llu\n", Stats.generated);
    fprintf(fp, "kept %llu\n", Stats.kept);
    fprintf(fp, "proofs %llu\n", Stats.proofs);
    fprintf(fp, "back_subsumed %llu\n", Stats.back_subsumed);
    fprintf(fp, "back_demodulated %llu\n", Stats.back_demodulated);
    fprintf(fp, "subsumed %llu\n", Stats.subsumed);
    fprintf(fp, "sos_limit_deleted %llu\n", Stats.sos_limit_deleted);
    fprintf(fp, "new_demodulators %llu\n", Stats.new_demodulators);
    fprintf(fp, "new_lex_demods %llu\n", Stats.new_lex_demods);
    fprintf(fp, "back_unit_deleted %llu\n", Stats.back_unit_deleted);
    fprintf(fp, "demod_attempts %llu\n", Stats.demod_attempts);
    fprintf(fp, "demod_rewrites %llu\n", Stats.demod_rewrites);
    fprintf(fp, "res_instance_prunes %llu\n", Stats.res_instance_prunes);
    fprintf(fp, "para_instance_prunes %llu\n", Stats.para_instance_prunes);
    fprintf(fp, "basic_para_prunes %llu\n", Stats.basic_para_prunes);
    fprintf(fp, "nonunit_fsub %llu\n", Stats.nonunit_fsub);
    fprintf(fp, "nonunit_bsub %llu\n", Stats.nonunit_bsub);
    fprintf(fp, "new_constants %llu\n", Stats.new_constants);
    fprintf(fp, "kept_by_rule %llu\n", Stats.kept_by_rule);
    fprintf(fp, "deleted_by_rule %llu\n", Stats.deleted_by_rule);
    fprintf(fp, "sos_displaced %llu\n", Stats.sos_displaced);
    fprintf(fp, "sos_removed %llu\n", Stats.sos_removed);
    fprintf(fp, "user_seconds %.2f\n", user_seconds());
    /* Save Low selector cycle state for deterministic resume */
    {
      const char *sel_name;
      int sel_count;
      get_low_selector_state(&sel_name, &sel_count);
      fprintf(fp, "low_selector %s\n", sel_name);
      fprintf(fp, "low_selector_count %d\n", sel_count);
      get_high_selector_state(&sel_name, &sel_count);
      fprintf(fp, "high_selector %s\n", sel_name);
      fprintf(fp, "high_selector_count %d\n", sel_count);
    }
    /* Save cac_clauses IDs (commutativity/associativity/AC triggers) */
    if (Glob.cac_clauses != NULL) {
      Plist p;
      fprintf(fp, "cac_clauses");
      for (p = Glob.cac_clauses; p; p = p->next)
        fprintf(fp, " %llu", ((Topform) p->v)->id);
      fprintf(fp, "\n");
    }
    /* Save desc_to_be_disabled clause IDs (may be NULL at checkpoint time) */
    if (Glob.desc_to_be_disabled != NULL) {
      Plist p;
      fprintf(fp, "desc_to_be_disabled");
      for (p = Glob.desc_to_be_disabled; p; p = p->next)
        fprintf(fp, " %llu", ((Topform) p->v)->id);
      fprintf(fp, "\n");
    }
    /* Save hoisted function-local statics */
    fprintf(fp, "bf_level %d\n", Bf_level);
    fprintf(fp, "bf_last_of_level %d\n", Bf_last_of_level);
    fprintf(fp, "nohints_count %d\n", Nohints_count);
    fclose(fp);
  }

  /* 2. Write clause_data.txt and clause files */
  {
    char cdata_path[600];
    char cpath[600];
    FILE *data_fp;
    int total_clauses = 0;

    snprintf(cdata_path, sizeof(cdata_path), "%s/clause_data.txt", tmpdir);
    data_fp = fopen(cdata_path, "w");
    if (!data_fp) {
      fprintf(stderr, "ERROR: cannot write %s\n", cdata_path);
      return;
    }

    /* Write-side dedup: track clause IDs already written to any .clauses
       file.  When demods writes a clause already in usable/sos, it marks
       the clause_data entry as "shared" and skips the clause text. */
#define SEEN_TAB_SIZE 50000
    {
      Plist seen_tab[SEEN_TAB_SIZE];
      memset(seen_tab, 0, sizeof(seen_tab));

    /* SOS */
    snprintf(cpath, sizeof(cpath), "%s/sos.clauses", tmpdir);
    fp = fopen(cpath, "w");
    if (fp) {
      total_clauses += write_clist_bare(fp, data_fp, Glob.sos, "sos",
                                        seen_tab, SEEN_TAB_SIZE);
      fclose(fp);
    }

    /* Usable */
    snprintf(cpath, sizeof(cpath), "%s/usable.clauses", tmpdir);
    fp = fopen(cpath, "w");
    if (fp) {
      total_clauses += write_clist_bare(fp, data_fp, Glob.usable, "usable",
                                        seen_tab, SEEN_TAB_SIZE);
      fclose(fp);
    }

    /* Demodulators — uses seen_tab to detect shared clauses */
    snprintf(cpath, sizeof(cpath), "%s/demods.clauses", tmpdir);
    fp = fopen(cpath, "w");
    if (fp) {
      total_clauses += write_clist_bare(fp, data_fp, Glob.demods,
                                        "demodulators",
                                        seen_tab, SEEN_TAB_SIZE);
      fclose(fp);
    }

    /* Hints — no dedup needed (separate ID namespace) */
    if (Glob.hints->length > 0) {
      snprintf(cpath, sizeof(cpath), "%s/hints.clauses", tmpdir);
      fp = fopen(cpath, "w");
      if (fp) {
        total_clauses += write_clist_bare(fp, data_fp, Glob.hints, "hints",
                                          NULL, 0);
        fclose(fp);
      }
    }

    /* Limbo */
    if (Glob.limbo->length > 0) {
      snprintf(cpath, sizeof(cpath), "%s/limbo.clauses", tmpdir);
      fp = fopen(cpath, "w");
      if (fp) {
        total_clauses += write_clist_bare(fp, data_fp, Glob.limbo, "limbo",
                                          NULL, 0);
        fclose(fp);
      }
    }

    /* Disabled (ancestors for proof reconstruction) */
    if (flag(Opt->checkpoint_ancestors) && Glob.disabled->length > 0) {
      snprintf(cpath, sizeof(cpath), "%s/disabled.clauses", tmpdir);
      fp = fopen(cpath, "w");
      if (fp) {
        total_clauses += write_clist_bare(fp, data_fp, Glob.disabled,
                                          "disabled", NULL, 0);
        fclose(fp);
      }
    }

    /* Empties (proof clauses) — Plist, not Clist.  Build temporary Clist. */
    if (Glob.empties != NULL) {
      Plist ep;
      Clist tmp_empties = clist_init("empties");
      for (ep = Glob.empties; ep; ep = ep->next)
        clist_append((Topform) ep->v, tmp_empties);
      snprintf(cpath, sizeof(cpath), "%s/empties.clauses", tmpdir);
      fp = fopen(cpath, "w");
      if (fp) {
        total_clauses += write_clist_bare(fp, data_fp, tmp_empties,
                                          "empties", NULL, 0);
        fclose(fp);
      }
      /* Remove from temp Clist without freeing clauses */
      while (tmp_empties->first)
        clist_remove(tmp_empties->first->c, tmp_empties);
      clist_zap(tmp_empties);
    }

    }  /* end seen_tab scope */

    fclose(data_fp);

    /* 3. Write options.txt for human reference */
    snprintf(cpath, sizeof(cpath), "%s/options.txt", tmpdir);
    fp = fopen(cpath, "w");
    if (fp) {
      fprint_options(fp);
      fclose(fp);
    }

    /* 3b. Write precedence.txt — symbol ordering for deterministic resume.
       Format: "F name arity [S]" for function, "R name arity" for predicate.
       S flag indicates Skolem constant. */
    snprintf(cpath, sizeof(cpath), "%s/precedence.txt", tmpdir);
    fp = fopen(cpath, "w");
    if (fp) {
      Ilist fsyms = current_fsym_precedence();
      Ilist rsyms = current_rsym_precedence();
      Ilist p;
      for (p = fsyms; p; p = p->next)
        fprintf(fp, "F %s %d%s\n", sn_to_str(p->i), sn_to_arity(p->i),
                is_skolem(p->i) ? " S" : "");
      for (p = rsyms; p; p = p->next)
        fprintf(fp, "R %s %d\n", sn_to_str(p->i), sn_to_arity(p->i));
      zap_ilist(fsyms);
      zap_ilist(rsyms);
      fclose(fp);
    }

    /* 3b2. Write symbol table (symnum assignments) for deterministic
       term_compare_vcp on resume.  The secondary ordering for
       NOT_COMPARABLE equations uses raw SYMNUM, not lex_val. */
    {
      char spath[600];
      FILE *sfp;
      int sn;
      snprintf(spath, sizeof(spath), "%s/symbols.txt", tmpdir);
      sfp = fopen(spath, "w");
      if (sfp) {
        int max_sn = greatest_symnum();
        fprintf(sfp, "%d\n", max_sn);
        for (sn = 1; sn <= max_sn; sn++) {
          char *name = sn_to_str(sn);
          if (name != NULL)
            fprintf(sfp, "%d %d %s\n", sn, sn_to_arity(sn), name);
        }
        fclose(sfp);
      }
    }

    /* 3c. Write FPA_IDs for deterministic FPA leaf ordering on resume */
    write_fpa_ids(tmpdir);

    /* 3c2. Write DISCRIM index leaf orderings for deterministic
       forward demodulation and forward subsumption on resume */
    write_demod_index(tmpdir);
    write_unit_discrim_index(tmpdir);

    /* 3c3. Write FPA trie structure for fast resume (avoids rebuilding
       from scratch, which is O(n * paths * depth) for millions of clauses) */
    write_fpa_lits_index(tmpdir);
    write_fpa_back_demod_index(tmpdir);
    /* Clashable FPA index */
    {
      char cpath[600];
      FILE *cfp;
      snprintf(cpath, sizeof(cpath), "%s/fpa_clashable_index.txt", tmpdir);
      cfp = fopen(cpath, "w");
      if (cfp) {
        fprintf(cfp, "SECTION pos\n");
        fpa_write_index(cfp, Glob.clashable_idx->pos->fpa);
        fprintf(cfp, "SECTION neg\n");
        fpa_write_index(cfp, Glob.clashable_idx->neg->fpa);
        fprintf(cfp, "END\n");
        fclose(cfp);
      }
    }

    /* 3d. Write justifications for proof reconstruction on resume */
    write_justifications(tmpdir);

    /* 3e. Write non-clause formulas (goals) for proof ancestor tracing */
    write_checkpoint_formulas(tmpdir);

    /* 3f. Write saved_input.txt for self-contained resume */
    write_checkpoint_input(tmpdir);

    /* 3g. Write verification hashes (if checkpoint_verify enabled) */
    if (flag(Opt->checkpoint_verify))
      write_checkpoint_hashes(tmpdir);

    /* 4. Rename temp dir to final name */
    if (rename(tmpdir, finaldir) != 0) {
      fprintf(stderr, "ERROR: cannot rename %s to %s: %s\n",
              tmpdir, finaldir, strerror(errno));
      return;
    }

    fprintf(stderr, "\nCheckpoint written (experimental): %s (%d clauses, %lld MB)\n",
            finaldir, total_clauses, megs_malloced());
    fflush(stderr);
    printf("\n%% Checkpoint written: %s (%d clauses)\n", finaldir, total_clauses);
    fflush(stdout);
  }
}  /* write_checkpoint */

#endif /* !PRIMITIVE_ENVIRONMENT */

/*************
 *
 *   read_metadata_ull()
 *
 *   Read a named unsigned long long value from metadata.
 *
 *************/

static
unsigned long long read_metadata_ull(FILE *fp, const char *key)
{
  char buf[256], name[128];
  unsigned long long val;
  while (fgets(buf, sizeof(buf), fp)) {
    if (sscanf(buf, "%127s %llu", name, &val) == 2) {
      if (strcmp(name, key) == 0)
        return val;
    }
  }
  fprintf(stderr, "WARNING: metadata key '%s' not found, using 0\n", key);
  return 0;
}  /* read_metadata_ull */

/*************
 *
 *   read_metadata_str()
 *
 *   Read a named string value from metadata.
 *   Returns TRUE if found, FALSE otherwise.
 *   Caller must provide buffer and size.
 *
 *************/

static
BOOL read_metadata_str(FILE *fp, const char *key, char *val, int val_size)
{
  char buf[256], name[128], sval[128];
  while (fgets(buf, sizeof(buf), fp)) {
    if (sscanf(buf, "%127s %127s", name, sval) == 2) {
      if (strcmp(name, key) == 0) {
        {
          int n = strlen(sval);
          if (n >= val_size) n = val_size - 1;
          memcpy(val, sval, n);
          val[n] = '\0';
        }
        return TRUE;
      }
    }
  }
  return FALSE;
}  /* read_metadata_str */

/*************
 *
 *   read_metadata_double()
 *
 *   Read a named double value from metadata.
 *
 *************/

static
double read_metadata_double(FILE *fp, const char *key)
{
  char buf[256], name[128];
  double val;
  while (fgets(buf, sizeof(buf), fp)) {
    if (sscanf(buf, "%127s %lf", name, &val) == 2) {
      if (strcmp(name, key) == 0)
        return val;
    }
  }
  return 0.0;  /* not found — no warning, old checkpoints may lack this */
}  /* read_metadata_double */

/*************
 *
 *   load_clause_data()
 *
 *   Read clause_data.txt into parallel arrays indexed by (list, position).
 *   Returns total number of entries read.
 *
 *************/

struct clause_meta {
  char list_name[32];
  int position;
  unsigned long long id;
  double weight;
  int initial;    /* c->initial flag (0 or 1) */
  int shared;     /* 1 if clause is shared with another list (dedup) */
  int hint_match; /* matched hint ID (1-based), 0 if none */
  int used;       /* c->used flag */
  int was_given;  /* c->was_given flag */
  unsigned long long last_matched; /* hint last_matched_given (for expiry) */
  int redundant_hint; /* hint was in Redundant_hints at checkpoint time */
  unsigned aflags[10]; /* atom private_flags per literal (max 10 lits) */
  int aflags_count;    /* number of aflags entries */
};

static
int load_clause_data(const char *dir, struct clause_meta **out)
{
  char path[600], line[512];
  FILE *fp;
  int capacity = 4096, count = 0;
  struct clause_meta *arr;

  snprintf(path, sizeof(path), "%s/clause_data.txt", dir);
  fp = fopen(path, "r");
  if (!fp)
    fatal_error("resume: cannot open clause_data.txt");

  arr = safe_malloc(capacity * sizeof(struct clause_meta));

  while (fgets(line, sizeof(line), fp)) {
    struct clause_meta *m = &arr[count];
    char *p;
    m->shared = 0;
    m->hint_match = 0;
    m->used = 0;
    m->was_given = 0;
    m->last_matched = 0;
    m->redundant_hint = 0;
    m->aflags_count = 0;
    if (sscanf(line, "%31s %d %llu %lf %d",
               m->list_name, &m->position,
               &m->id, &m->weight, &m->initial) == 5) {
      if (strstr(line, "shared") != NULL)
        m->shared = 1;
      p = strstr(line, "hint_match");
      if (p != NULL)
        sscanf(p, "hint_match %d", &m->hint_match);
      if (strstr(line, " used") != NULL)
        m->used = 1;
      if (strstr(line, "was_given") != NULL)
        m->was_given = 1;
      p = strstr(line, "last_matched");
      if (p != NULL)
        sscanf(p, "last_matched %llu", &m->last_matched);
      if (strstr(line, "redundant_hint") != NULL)
        m->redundant_hint = 1;
      /* Parse atom private_flags: "aflags N [aflags N ...]" */
      p = strstr(line, "aflags");
      while (p != NULL && m->aflags_count < 10) {
        unsigned fval;
        if (sscanf(p, "aflags %u", &fval) == 1)
          m->aflags[m->aflags_count++] = fval;
        p = strstr(p + 6, "aflags");
      }
      count++;
      if (count >= capacity) {
        capacity *= 2;
        arr = safe_realloc(arr, capacity * sizeof(struct clause_meta));
      }
    }
  }
  fclose(fp);
  *out = arr;
  return count;
}  /* load_clause_data */

/*************
 *
 *   load_clauses_from_file()
 *
 *   Read clauses from a .clauses file.  Returns a Clist.
 *   Assigns IDs and weights from clause_data metadata.
 *
 *************/

static
Clist load_clauses_from_file(const char *dir, const char *filename,
                             const char *list_name,
                             struct clause_meta *meta, int meta_count,
                             int *meta_offset, BOOL skip_register)
{
  char path[600];
  FILE *fp;
  Clist lst;
  int pos = 0;

  snprintf(path, sizeof(path), "%s/%s", dir, filename);
  fp = fopen(path, "r");
  if (!fp)
    return NULL;  /* file doesn't exist -- ok for optional lists */

  lst = read_clause_clist(fp, stderr, (char *)list_name, FALSE);
  fclose(fp);

  /* Now assign IDs and weights from metadata.
     Skip shared entries (they don't appear in the .clauses file). */
  {
    Clist_pos cp;
    int meta_pos = *meta_offset;

    /* Advance meta_pos past shared entries to find first non-shared */
    for (cp = lst->first; cp != NULL; cp = cp->next) {
      Topform c = cp->c;

      /* Skip shared metadata entries for this list */
      while (meta_pos < meta_count &&
             strcmp(meta[meta_pos].list_name, list_name) == 0 &&
             meta[meta_pos].shared)
        meta_pos++;

      if (meta_pos < meta_count &&
          strcmp(meta[meta_pos].list_name, list_name) == 0 &&
          !meta[meta_pos].shared &&
          meta[meta_pos].position == pos) {
        c->id = meta[meta_pos].id;
        c->weight = meta[meta_pos].weight;
        c->initial = meta[meta_pos].initial;
        c->used = meta[meta_pos].used;
        c->was_given = meta[meta_pos].was_given;
        if (!skip_register)
          register_clause_with_id(c);
        meta_pos++;
      }
      else {
        /* Fallback: search all non-shared entries for this list+pos */
        int j;
        for (j = 0; j < meta_count; j++) {
          if (strcmp(meta[j].list_name, list_name) == 0 &&
              !meta[j].shared && meta[j].position == pos) {
            c->id = meta[j].id;
            c->weight = meta[j].weight;
            c->initial = meta[j].initial;
            c->used = meta[j].used;
            c->was_given = meta[j].was_given;
            if (!skip_register)
              register_clause_with_id(c);
            break;
          }
        }
        if (c->id == 0) {
          fprintf(stderr, "WARNING: no metadata for %s clause %d\n",
                  list_name, pos);
          if (!skip_register)
            assign_clause_id(c);
        }
      }
      pos++;
    }
  }
  /* Advance meta_offset past ALL entries for this list (shared + non-shared) */
  while (*meta_offset < meta_count &&
         strcmp(meta[*meta_offset].list_name, list_name) == 0)
    (*meta_offset)++;
  return lst;
}  /* load_clauses_from_file */

/*************
 *
 *   resume_load_precedence()
 *
 *   Read precedence.txt from checkpoint directory and set up
 *   preliminary symbol precedence.  This ensures symbol ordering
 *   on resume matches the original run exactly.
 *
 *   Must be called AFTER loading clauses (so symbols exist in the
 *   symbol table) and BEFORE init_search() (which calls symbol_order).
 *
 *************/

static
void resume_load_precedence(const char *dir)
{
  char path[600];
  FILE *fp;
  Ilist fsyms = NULL, rsyms = NULL;

  snprintf(path, sizeof(path), "%s/precedence.txt", dir);
  fp = fopen(path, "r");
  if (!fp)
    return;  /* old checkpoint without precedence — fall through to default */

  {
    char line[1024];
    while (fgets(line, sizeof(line), fp)) {
      char type_ch;
      char name[512];
      int arity;
      char skolem_flag[16];
      int n;

      skolem_flag[0] = '\0';
      n = sscanf(line, " %c %511s %d %15s", &type_ch, name, &arity, skolem_flag);
      if (n < 3)
        continue;

      {
        int sn = str_to_sn(name, arity);
        if (type_ch == 'F') {
          set_symbol_type(sn, FUNCTION_SYMBOL);
          if (skolem_flag[0] == 'S')
            set_skolem(sn);
          fsyms = ilist_prepend(fsyms, sn);
        }
        else if (type_ch == 'R') {
          set_symbol_type(sn, PREDICATE_SYMBOL);
          rsyms = ilist_prepend(rsyms, sn);
        }
      }
    }
  }
  fclose(fp);

  fsyms = reverse_ilist(fsyms);
  rsyms = reverse_ilist(rsyms);

  /* Set as preliminary precedence so symbol_order uses this ordering */
  if (fsyms)
    set_preliminary_precedence_ilist(fsyms, FUNCTION_SYMBOL);
  if (rsyms)
    set_preliminary_precedence_ilist(rsyms, PREDICATE_SYMBOL);
}  /* resume_load_precedence */

/*************
 *
 *   resume_load_clauses()
 *
 *   Phase 1 of resume: load clauses from checkpoint directory into
 *   Glob lists.  No orient_equalities, mark_maximal_literals, or
 *   indexing — those require init_search() to have set up the term
 *   ordering and inference rules first.
 *
 *************/

static
void resume_load_clauses(const char *dir)
{
  char path[600];
  FILE *fp;
  struct clause_meta *meta;
  int meta_count, meta_offset;
  unsigned long long max_clause_id;
  Clist loaded_sos, loaded_usable, loaded_demods, loaded_hints;
  Clist loaded_limbo, loaded_disabled, loaded_empties;

  fprintf(stderr, "Resuming from checkpoint (experimental): %s\n", dir);
  fflush(stderr);

  /* 1. Read metadata */
  snprintf(path, sizeof(path), "%s/metadata.txt", dir);
  fp = fopen(path, "r");
  if (!fp)
    fatal_error("resume: cannot open metadata.txt");

  /* Check checkpoint format version */
  {
    unsigned long long fmt = read_metadata_ull(fp, "checkpoint_format");
    if (fmt != 3) {
      fprintf(stderr, "resume: checkpoint format %llu not supported "
              "(this version requires format 3)\n", (unsigned long long)fmt);
      fatal_error("resume: unsupported checkpoint format");
    }
  }

  /* Read max_clause_id */
  rewind(fp);
  max_clause_id = read_metadata_ull(fp, "max_clause_id");

  /* Read stats */
  rewind(fp); Stats.given = read_metadata_ull(fp, "given");
  rewind(fp); Stats.generated = read_metadata_ull(fp, "generated");
  rewind(fp); Stats.kept = read_metadata_ull(fp, "kept");
  rewind(fp); Stats.proofs = read_metadata_ull(fp, "proofs");
  rewind(fp); Stats.back_subsumed = read_metadata_ull(fp, "back_subsumed");
  rewind(fp); Stats.back_demodulated = read_metadata_ull(fp, "back_demodulated");
  rewind(fp); Stats.subsumed = read_metadata_ull(fp, "subsumed");
  rewind(fp); Stats.sos_limit_deleted = read_metadata_ull(fp, "sos_limit_deleted");
  rewind(fp); Stats.new_demodulators = read_metadata_ull(fp, "new_demodulators");
  rewind(fp); Stats.new_lex_demods = read_metadata_ull(fp, "new_lex_demods");
  rewind(fp); Stats.back_unit_deleted = read_metadata_ull(fp, "back_unit_deleted");
  rewind(fp); Stats.demod_attempts = read_metadata_ull(fp, "demod_attempts");
  rewind(fp); Stats.demod_rewrites = read_metadata_ull(fp, "demod_rewrites");
  rewind(fp); Stats.res_instance_prunes = read_metadata_ull(fp, "res_instance_prunes");
  rewind(fp); Stats.para_instance_prunes = read_metadata_ull(fp, "para_instance_prunes");
  rewind(fp); Stats.basic_para_prunes = read_metadata_ull(fp, "basic_para_prunes");
  rewind(fp); Stats.nonunit_fsub = read_metadata_ull(fp, "nonunit_fsub");
  rewind(fp); Stats.nonunit_bsub = read_metadata_ull(fp, "nonunit_bsub");
  rewind(fp); Stats.new_constants = read_metadata_ull(fp, "new_constants");
  rewind(fp); Stats.kept_by_rule = read_metadata_ull(fp, "kept_by_rule");
  rewind(fp); Stats.deleted_by_rule = read_metadata_ull(fp, "deleted_by_rule");
  rewind(fp); Stats.sos_displaced = read_metadata_ull(fp, "sos_displaced");
  rewind(fp); Stats.sos_removed = read_metadata_ull(fp, "sos_removed");

  /* Restore accumulated CPU time from original run so max_seconds and
     reporting account for total time across checkpoint/resume cycles. */
  {
    double saved_seconds;
    rewind(fp);
    saved_seconds = read_metadata_double(fp, "user_seconds");
    if (saved_seconds > 0.0) {
      /* Don't restore wall clock offset — it causes checkpoint_minutes
         to trigger immediately on resume if the saved time exceeds the
         interval.  CPU time is tracked separately in statistics. */
      /* set_user_seconds_offset(saved_seconds); */
      printf("%%   Saved user_seconds: %.2f (not restored)\n", saved_seconds);
    }
  }

  /* Read selector cycle state (may not be present in old checkpoints) */
  rewind(fp);
  if (!read_metadata_str(fp, "low_selector", Resume_low_selector_name,
                          sizeof(Resume_low_selector_name)))
    Resume_low_selector_name[0] = '\0';
  rewind(fp);
  Resume_low_selector_count = (int) read_metadata_ull(fp, "low_selector_count");
  rewind(fp);
  if (!read_metadata_str(fp, "high_selector", Resume_high_selector_name,
                          sizeof(Resume_high_selector_name)))
    Resume_high_selector_name[0] = '\0';
  rewind(fp);
  Resume_high_selector_count = (int) read_metadata_ull(fp, "high_selector_count");

  /* Read cac_clauses IDs (restored after clause loading via find_clause_by_id) */
  rewind(fp);
  {
    char buf[4096], name[128];
    Resume_cac_ids = NULL;
    Resume_cac_count = 0;
    while (fgets(buf, sizeof(buf), fp)) {
      if (sscanf(buf, "%127s", name) == 1 && strcmp(name, "cac_clauses") == 0) {
        char *p = buf + strlen("cac_clauses");
        unsigned long long id;
        int cap = 0;
        while (sscanf(p, " %llu%n", &id, &cap) == 1) {
          Resume_cac_count++;
          Resume_cac_ids = (unsigned long long *)
            safe_realloc(Resume_cac_ids,
                         Resume_cac_count * sizeof(unsigned long long));
          Resume_cac_ids[Resume_cac_count - 1] = id;
          p += cap;
        }
        break;
      }
    }
  }

  /* Read desc_to_be_disabled IDs (same pattern as cac_clauses) */
  rewind(fp);
  {
    char buf[4096], name[128];
    Resume_dtbd_ids = NULL;
    Resume_dtbd_count = 0;
    while (fgets(buf, sizeof(buf), fp)) {
      if (sscanf(buf, "%127s", name) == 1 &&
          strcmp(name, "desc_to_be_disabled") == 0) {
        char *p = buf + strlen("desc_to_be_disabled");
        unsigned long long id;
        int cap = 0;
        while (sscanf(p, " %llu%n", &id, &cap) == 1) {
          Resume_dtbd_count++;
          Resume_dtbd_ids = (unsigned long long *)
            safe_realloc(Resume_dtbd_ids,
                         Resume_dtbd_count * sizeof(unsigned long long));
          Resume_dtbd_ids[Resume_dtbd_count - 1] = id;
          p += cap;
        }
        break;
      }
    }
  }

  /* Restore hoisted function-local statics */
  rewind(fp);
  Bf_level = (int) read_metadata_ull(fp, "bf_level");
  rewind(fp);
  Bf_last_of_level = (int) read_metadata_ull(fp, "bf_last_of_level");
  rewind(fp);
  Nohints_count = (int) read_metadata_ull(fp, "nohints_count");

  fclose(fp);

  /* 2. Load clause_data */
  meta_count = load_clause_data(dir, &meta);

  /* 3. Load clause files into Glob lists (no orient/index yet).
     Hints use skip_register=TRUE (separate ID namespace). */
  meta_offset = 0;
  loaded_sos = load_clauses_from_file(dir, "sos.clauses", "sos",
                                       meta, meta_count, &meta_offset,
                                       FALSE);
  loaded_usable = load_clauses_from_file(dir, "usable.clauses", "usable",
                                          meta, meta_count, &meta_offset,
                                          FALSE);
  loaded_demods = load_clauses_from_file(dir, "demods.clauses",
                                          "demodulators",
                                          meta, meta_count, &meta_offset,
                                          FALSE);
  loaded_hints = load_clauses_from_file(dir, "hints.clauses", "hints",
                                         meta, meta_count, &meta_offset,
                                         TRUE);  /* skip register */
  loaded_limbo = load_clauses_from_file(dir, "limbo.clauses", "limbo",
                                         meta, meta_count, &meta_offset,
                                         FALSE);
  loaded_disabled = load_clauses_from_file(dir, "disabled.clauses",
                                            "disabled",
                                            meta, meta_count, &meta_offset,
                                            FALSE);
  loaded_empties = load_clauses_from_file(dir, "empties.clauses",
                                           "empties",
                                           meta, meta_count, &meta_offset,
                                           FALSE);

  /* 4. Set clause ID counter past all loaded IDs */
  set_clause_id_count(max_clause_id);

  /* 5. Move loaded clauses into Glob lists (no orient/index) */
  if (loaded_sos) {
    while (loaded_sos->first) {
      Topform c = loaded_sos->first->c;
      clist_remove(c, loaded_sos);
      clist_append(c, Glob.sos);
    }
    clist_zap(loaded_sos);
  }
  if (loaded_usable) {
    while (loaded_usable->first) {
      Topform c = loaded_usable->first->c;
      clist_remove(c, loaded_usable);
      clist_append(c, Glob.usable);
    }
    clist_zap(loaded_usable);
  }
  /* Demods: interleave shared and non-shared in original list order.
     Shared clauses (in both demods and usable/sos) were not written to
     demods.clauses; resolve them by ID from already-loaded lists. */
  {
    int shared_count = 0, i;
    Clist_pos next_loaded = loaded_demods ? loaded_demods->first : NULL;
    for (i = 0; i < meta_count; i++) {
      if (strcmp(meta[i].list_name, "demodulators") != 0)
        continue;
      if (meta[i].shared) {
        Topform existing = find_clause_by_id(meta[i].id);
        if (existing != NULL) {
          clist_append(existing, Glob.demods);
          shared_count++;
        }
      }
      else if (next_loaded != NULL) {
        Topform c = next_loaded->c;
        next_loaded = next_loaded->next;
        clist_remove(c, loaded_demods);
        clist_append(c, Glob.demods);
      }
    }
    /* Append any remaining loaded demods (safety) */
    if (loaded_demods) {
      while (loaded_demods->first) {
        Topform c = loaded_demods->first->c;
        clist_remove(c, loaded_demods);
        clist_append(c, Glob.demods);
      }
      clist_zap(loaded_demods);
    }
    if (shared_count > 0)
      printf("%%   (%d shared demods resolved from usable/sos)\n",
             shared_count);
  }
  if (loaded_hints) {
    while (loaded_hints->first) {
      Topform c = loaded_hints->first->c;
      clist_remove(c, loaded_hints);
      clist_append(c, Glob.hints);
    }
    clist_zap(loaded_hints);
  }
  if (loaded_limbo) {
    while (loaded_limbo->first) {
      Topform c = loaded_limbo->first->c;
      clist_remove(c, loaded_limbo);
      clist_append(c, Glob.limbo);
    }
    clist_zap(loaded_limbo);
  }
  if (loaded_disabled) {
    while (loaded_disabled->first) {
      Topform c = loaded_disabled->first->c;
      clist_remove(c, loaded_disabled);
      clist_append(c, Glob.disabled);
    }
    clist_zap(loaded_disabled);
  }
  /* Empties (proof clauses) — load into Glob.empties Plist */
  if (loaded_empties) {
    int n = 0;
    while (loaded_empties->first) {
      Topform c = loaded_empties->first->c;
      clist_remove(c, loaded_empties);
      Glob.empties = plist_append(Glob.empties, c);
      n++;
    }
    clist_zap(loaded_empties);
    if (n > 0)
      printf("%%   Restored %d empty (proof) clauses from checkpoint.\n", n);
  }
  /* Keep meta for hint_match restoration in resume_index_clauses */
  Resume_meta = meta;
  Resume_meta_count = meta_count;

  printf("\n%% Loaded from checkpoint: %s\n", dir);
  printf("%%   sos=%d, usable=%d, demods=%d, hints=%d, limbo=%d, disabled=%d\n",
         Glob.sos->length, Glob.usable->length, Glob.demods->length,
         Glob.hints->length, Glob.limbo->length, Glob.disabled->length);
  printf("%%   Stats: given=%llu, generated=%llu, kept=%llu, proofs=%llu\n",
         Stats.given, Stats.generated, Stats.kept, Stats.proofs);
  printf("%%   max_clause_id=%llu\n", max_clause_id);
  fflush(stdout);
}  /* resume_load_clauses */

/*************
 *
 *   topform_id_qsort_compare() -- qsort wrapper for sorting by clause ID
 *
 *************/

static
int topform_id_qsort_compare(const void *a, const void *b)
{
  Topform ca = *(Topform *)a;
  Topform cb = *(Topform *)b;
  if (ca->id < cb->id) return -1;
  if (ca->id > cb->id) return  1;
  return 0;
}

/*************
 *
 *   load_checkpoint_into_loop()
 *
 *   Load checkpoint data and rebuild indexes INSIDE the main search loop.
 *   Called at the same program point as the checkpoint save (before
 *   make_inferences, after limbo_process from the previous iteration).
 *   This ensures save and restore happen at the same loop location,
 *   producing bit-identical state.
 *
 *************/

static
void load_checkpoint_into_loop(void)
{
  Clist_pos p;
  int fpa_depth;

  /* 0a. Clear clause ID hash table so stale entries don't shadow
     newly-loaded clauses (critical for in-process save+reload). */
  clear_clause_id_tab();

  /* 0b. Restore symbol table (symnum assignments) BEFORE any clause loading.
     Ensures str_to_sn assigns the same symnums as the original run, which
     is critical for term_compare_vcp secondary ordering. */
  {
    char spath[600];
    FILE *sfp;
    snprintf(spath, sizeof(spath), "%s/symbols.txt", Resume_dir);
    sfp = fopen(spath, "r");
    if (sfp) {
      int max_sn, sn, arity, restored = 0;
      char name[512];
      if (fscanf(sfp, "%d", &max_sn) == 1) {
        while (fscanf(sfp, "%d %d %511s", &sn, &arity, name) == 3) {
          int actual_sn = str_to_sn(name, arity);
          if (actual_sn != sn)
            fprintf(stderr, "WARNING: symbol %s/%d: expected sn=%d, got %d\n",
                    name, arity, sn, actual_sn);
          restored++;
        }
      }
      fclose(sfp);
      printf("%%   Restored %d symbols from checkpoint (%d max)\n",
             restored, greatest_symnum());
    }
  }

  /* 1. Clear Glob lists and selector AVL trees.  Selectors are rebuilt
     from scratch via insert_into_sos2 later in this function. */
  reset_selector_indexes();
  while (Glob.sos->first)
    clist_remove(Glob.sos->first->c, Glob.sos);
  while (Glob.usable->first)
    clist_remove(Glob.usable->first->c, Glob.usable);
  while (Glob.demods->first)
    clist_remove(Glob.demods->first->c, Glob.demods);
  while (Glob.hints->first)
    clist_remove(Glob.hints->first->c, Glob.hints);

  /* 2. Load checkpoint data */
  resume_load_clauses(Resume_dir);
  restore_fpa_ids(Resume_dir);
#ifndef PRIMITIVE_ENVIRONMENT
  restore_checkpoint_formulas(Resume_dir);
  restore_justifications(Resume_dir);
#endif
  resume_load_precedence(Resume_dir);

  /* 2b. Restore atom private_flags (oriented_eq, renamable_flip, maximal,
     selected marks) from checkpoint metadata.  These flags are stored in
     term->private_flags and are lost during text serialization. */
  if (Resume_meta != NULL) {
    int i, restored = 0, not_found = 0;
    for (i = 0; i < Resume_meta_count; i++) {
      /* Skip hint entries — hints use a separate ID namespace (1..N)
         that collides with regular clause IDs.  Hint aflags would
         corrupt regular clauses found by find_clause_by_id. */
      if (strcmp(Resume_meta[i].list_name, "hints") == 0)
        continue;
      if (Resume_meta[i].aflags_count > 0) {
        Topform c = find_clause_by_id(Resume_meta[i].id);
        if (c != NULL) {
          Literals lit;
          int j = 0;
          for (lit = c->literals; lit != NULL && j < Resume_meta[i].aflags_count;
               lit = lit->next, j++) {
            lit->atom->private_flags = (FLAGS_TYPE) Resume_meta[i].aflags[j];
          }
          restored++;
        }
        else
          not_found++;
      }
    }
    printf("%%   Restored aflags: %d clauses (%d not found)\n",
           restored, not_found);
  }

  /* Clear and restore Glob.cac_clauses from saved IDs.
     Must clear first — in-process reload leaves stale entries. */
  if (Glob.cac_clauses != NULL) {
    zap_plist(Glob.cac_clauses);
    Glob.cac_clauses = NULL;
  }
  if (Resume_cac_ids != NULL) {
    int i, restored = 0;
    /* Iterate backward: IDs were written head-to-tail, plist_prepend
       reverses, so backward iteration preserves original order. */
    for (i = Resume_cac_count - 1; i >= 0; i--) {
      Topform c = find_clause_by_id(Resume_cac_ids[i]);
      if (c != NULL) {
        Glob.cac_clauses = plist_prepend(Glob.cac_clauses, c);
        restored++;
      }
    }
    safe_free(Resume_cac_ids);
    Resume_cac_ids = NULL;
    if (restored > 0)
      printf("%%   Restored %d cac_clauses from checkpoint.\n", restored);
  }

  /* Clear and restore Glob.desc_to_be_disabled from saved IDs. */
  if (Glob.desc_to_be_disabled != NULL) {
    zap_plist(Glob.desc_to_be_disabled);
    Glob.desc_to_be_disabled = NULL;
  }
  if (Resume_dtbd_ids != NULL) {
    int i, restored = 0;
    for (i = Resume_dtbd_count - 1; i >= 0; i--) {
      Topform c = find_clause_by_id(Resume_dtbd_ids[i]);
      if (c != NULL) {
        Glob.desc_to_be_disabled = plist_prepend(Glob.desc_to_be_disabled, c);
        restored++;
      }
    }
    safe_free(Resume_dtbd_ids);
    Resume_dtbd_ids = NULL;
    if (restored > 0)
      printf("%%   Restored %d desc_to_be_disabled from checkpoint.\n",
             restored);
  }

  /* Recompute clause properties from loaded clauses (the call in the
     resume setup block ran on empty lists before clauses were loaded). */
  basic_clause_properties(Glob.sos, Glob.usable);

  /* Rebuild AC/C redundancy detection state from loaded clauses.
     The ac_redun.c static lists (C_symbols, A1_symbols, A2_symbols,
     AC_symbols) are process-local and empty in a fresh process.
     Scan for commutativity/associativity axioms to re-seed them. */
  if (flag(Opt->cac_redundancy)) {
    Clist scan_lists[4];
    int li, seeded = 0;
    scan_lists[0] = Glob.usable;
    scan_lists[1] = Glob.sos;
    scan_lists[2] = Glob.demods;
    scan_lists[3] = Glob.disabled;
    for (li = 0; li < 4; li++) {
      Clist_pos cp;
      for (cp = scan_lists[li]->first; cp != NULL; cp = cp->next) {
        if (seed_cac_properties(cp->c))
          seeded++;
      }
    }
    if (seeded > 0)
      printf("%%   Seeded %d CAC properties from checkpoint clauses.\n",
             seeded);
  }

  /* Convert preliminary precedence to actual lex_val ordering.
     symbol_order uses the preliminary precedence + clause symbols
     to assign lex_val (the actual precedence used by term ordering). */
  symbol_order(Glob.usable, Glob.sos, Glob.demods, !flag(Opt->quiet));


  /* 3. Re-initialize indexes (old indexes are leaked — acceptable for
     in-process save+reload testing and cross-process resume alike) */

  /* Initialize indexes */
  Glob.use_clash_idx = (flag(Opt->binary_resolution) ||
                        flag(Opt->neg_binary_resolution) ||
                        flag(Opt->pos_hyper_resolution) ||
                        flag(Opt->neg_hyper_resolution) ||
                        flag(Opt->pos_ur_resolution) ||
                        flag(Opt->neg_ur_resolution));

  set_fpa_hash_threshold(parm(Opt->fpa_hash_threshold));
  set_discrim_hash_threshold(parm(Opt->discrim_hash_threshold));

  fpa_depth = parm(Opt->fpa_depth);
  init_literals_index(fpa_depth);
  init_demodulator_index(DISCRIM_BIND, ORDINARY_UNIF, 0);
  init_back_demod_index(FPA, ORDINARY_UNIF, fpa_depth);
  Glob.clashable_idx = lindex_init(FPA, ORDINARY_UNIF, fpa_depth,
                                   FPA, ORDINARY_UNIF, fpa_depth);
  init_hints(ORDINARY_UNIF, Att.bsub_hint_wt,
             flag(Opt->collect_hint_labels),
             flag(Opt->back_demod_hints),
             parm(Opt->hints_fpa_depth),
             demodulate_clause);
  set_hint_match_stats(flag(Opt->hint_match_stats));
  set_hint_match_once(flag(Opt->hint_match_once));
  init_semantics(Glob.interps, Clocks.semantics,
                 stringparm1(Opt->multiple_interps),
                 parm(Opt->eval_limit),
                 parm(Opt->eval_var_limit));

  /* 4-8. Orient, index all checkpoint clauses in CLAUSE ID ORDER.
     The original run indexed clauses in the order they were discovered
     (which is strictly increasing by clause ID).  DISCRIM tree leaf-list
     ordering depends on insertion order, so we must reproduce it exactly
     for deterministic forward subsumption (backsub_check is bounded). */
  {
    int n_usable, n_sos, n_all, idx;
    Topform *all_clauses;  /* merged usable+SOS for ID-sorted indexing */

    /* Build merged array of usable + SOS clauses */
    n_usable = Glob.usable->length;
    n_sos    = Glob.sos->length;
    n_all    = n_usable + n_sos;
    all_clauses = (Topform *) safe_malloc(n_all * sizeof(Topform));
    idx = 0;
    for (p = Glob.usable->first; p != NULL; p = p->next)
      all_clauses[idx++] = p->c;
    for (p = Glob.sos->first; p != NULL; p = p->next)
      all_clauses[idx++] = p->c;

    /* Sort by clause ID (reproduces original insertion order) */
    qsort(all_clauses, n_all, sizeof(Topform), topform_id_qsort_compare);

    /* Set container links for all clauses (needed regardless of index method) */
    for (idx = 0; idx < n_all; idx++)
      upward_clause_links(all_clauses[idx]);

    /* Try fast FPA restore from serialized trie files.
       Falls back to per-clause FPA rebuild if files are missing. */
    {
      BOOL fpa_restored = FALSE;

      /* Build FPA_ID -> Term* lookup table for trie restore */
      {
        unsigned id_count = get_fpa_id_count();
        Term *id_table = (Term *) safe_calloc(id_count + 1, sizeof(Term));
        int vi;
        Term v;

        /* Collect variable term IDs */
        for (vi = 0; (v = get_variable_term_if_exists(vi)) != NULL; vi++) {
          if (FPA_ID(v) != 0 && FPA_ID(v) <= id_count)
            id_table[FPA_ID(v)] = v;
        }
        /* Collect all clause term IDs */
        for (idx = 0; idx < n_all; idx++) {
          Literals lit;
          for (lit = all_clauses[idx]->literals; lit != NULL; lit = lit->next) {
            Term atom = lit->atom;
            /* Walk atom and all subterms (for back_demod index) */
            {
              struct { Term t; int i; } stk[256];
              int sp = 0;
              stk[sp].t = atom; stk[sp].i = 0; sp++;
              while (sp > 0) {
                Term t = stk[sp-1].t;
                int ci = stk[sp-1].i;
                if (ci >= ARITY(t)) {
                  if (FPA_ID(t) != 0 && FPA_ID(t) <= id_count)
                    id_table[FPA_ID(t)] = t;
                  sp--;
                } else {
                  stk[sp-1].i = ci + 1;
                  if (sp < 256) {
                    stk[sp].t = ARG(t, ci);
                    stk[sp].i = 0;
                    sp++;
                  }
                }
              }
            }
          }
        }
        /* Also walk hint and disabled clause terms */
        {
          Clist extra_lists[2];
          int li;
          extra_lists[0] = Glob.hints;
          extra_lists[1] = Glob.disabled;
          for (li = 0; li < 2; li++) {
            Clist_pos cp;
            for (cp = extra_lists[li]->first; cp != NULL; cp = cp->next) {
              Literals lit;
              for (lit = cp->c->literals; lit != NULL; lit = lit->next) {
                Term atom = lit->atom;
                struct { Term t; int i; } stk[256];
                int sp = 0;
                stk[sp].t = atom; stk[sp].i = 0; sp++;
                while (sp > 0) {
                  Term t = stk[sp-1].t;
                  int ci = stk[sp-1].i;
                  if (ci >= ARITY(t)) {
                    if (FPA_ID(t) != 0 && FPA_ID(t) <= id_count)
                      id_table[FPA_ID(t)] = t;
                    sp--;
                  } else {
                    stk[sp-1].i = ci + 1;
                    if (sp < 256) {
                      stk[sp].t = ARG(t, ci);
                      stk[sp].i = 0;
                      sp++;
                    }
                  }
                }
              }
            }
          }
        }

        fpa_set_id_table(id_table, id_count);
        fprintf(stderr, "%% Built FPA_ID lookup table (%u entries).\n", id_count);
        fflush(stderr);
      }

      /* Try restoring FPA indexes from serialized trie files */
      {
        BOOL lits_ok, bdemod_ok, clash_ok;
        fprintf(stderr, "%% Restoring FPA indexes from checkpoint...\n");
        fflush(stderr);

        lits_ok = restore_fpa_lits_index(Resume_dir);
        bdemod_ok = restore_fpa_back_demod_index(Resume_dir);

        /* Clashable FPA index */
        clash_ok = FALSE;
        {
          char cpath[600];
          FILE *cfp;
          snprintf(cpath, sizeof(cpath), "%s/fpa_clashable_index.txt", Resume_dir);
          cfp = fopen(cpath, "r");
          if (cfp) {
            char buf[64];
            int restored = 0;
            while (fscanf(cfp, " %63s", buf) == 1) {
              if (strcmp(buf, "END") == 0) break;
              if (strcmp(buf, "SECTION") != 0) continue;
              if (fscanf(cfp, " %63s", buf) != 1) break;
              if (strcmp(buf, "pos") == 0) {
                if (fpa_restore_index(cfp, Glob.clashable_idx->pos->fpa))
                  restored++;
              } else if (strcmp(buf, "neg") == 0) {
                if (fpa_restore_index(cfp, Glob.clashable_idx->neg->fpa))
                  restored++;
              }
            }
            fclose(cfp);
            clash_ok = (restored == 2);
            if (clash_ok)
              printf("%%   Restored FPA clashable index from %s\n", cpath);
          }
        }

        fpa_restored = lits_ok && bdemod_ok && clash_ok;
      }

      fpa_free_id_table();

      if (!fpa_restored) {
        /* Fallback: rebuild FPA indexes from scratch (format 3 checkpoints
           or missing FPA trie files). */
        char *is_usable = (char *) safe_calloc(n_all, sizeof(char));
        for (p = Glob.usable->first; p != NULL; p = p->next) {
          int lo = 0, hi = n_all - 1;
          while (lo <= hi) {
            int mid = lo + (hi - lo) / 2;
            if (all_clauses[mid]->id == p->c->id) {
              is_usable[mid] = 1; break;
            }
            else if (all_clauses[mid]->id < p->c->id) lo = mid + 1;
            else hi = mid - 1;
          }
        }
        fprintf(stderr, "%% FPA trie files not found, rebuilding indexes...\n");
        fprintf(stderr, "%% Indexing %d clauses...\n", n_all);
        fflush(stderr);
        for (idx = 0; idx < n_all; idx++) {
          Topform c = all_clauses[idx];
          index_literals_fpa_only(c, INSERT, Clocks.index, FALSE);
          index_back_demod(c, INSERT, Clocks.index, flag(Opt->back_demod));
          if (is_usable[idx])
            index_clashable(c, INSERT);
          if ((idx + 1) % 1000000 == 0) {
            fprintf(stderr, "%%   %d / %d clauses indexed...\n", idx + 1, n_all);
            fflush(stderr);
          }
        }
        safe_free(is_usable);
      }
    }
    safe_free(all_clauses);

    /* Set up container links for demodulators (needed for demod index
       serialization which navigates term→clause).  Skip orient_equalities
       — atom flags restored from aflags in checkpoint metadata. */
    for (p = Glob.demods->first; p != NULL; p = p->next)
      upward_clause_links(p->c);

    /* Restore DISCRIM index leaf orderings from serialized data.
       This preserves the exact leaf-list order from the original run,
       which determines forward demodulation and subsumption behavior. */
    restore_demod_index(Resume_dir, Clocks.index);
    restore_unit_discrim_index(Resume_dir);

    if (flag(Opt->eval_rewrite))
      init_dollar_eval(Glob.demods);

    /* Index hints, preserving the redundant/active partition from the
       original run.  Hints marked redundant_hint in clause_data are put
       directly into Redundant_hints without the subsumption check that
       index_hint normally performs (which gives different results when
       back-demodulated hints are re-indexed from scratch). */
    {
      int hint_id_number = 1;
      int meta_hint_pos = 0;  /* tracks position in Resume_meta hints section */
      fprintf(stderr, "%% Indexing %d hints...\n", Glob.hints->length);
      fflush(stderr);
      for (p = Glob.hints->first; p != NULL; p = p->next) {
        Topform h = p->c;
        int is_redundant = 0;

        /* Find this hint's redundant status from metadata */
        if (Resume_meta != NULL) {
          while (meta_hint_pos < Resume_meta_count &&
                 strcmp(Resume_meta[meta_hint_pos].list_name, "hints") != 0)
            meta_hint_pos++;
          if (meta_hint_pos < Resume_meta_count)
            is_redundant = Resume_meta[meta_hint_pos].redundant_hint;
          meta_hint_pos++;
        }

        h->id = hint_id_number++;
        orient_equalities(h, FALSE);
        renumber_variables(h, MAX_VARS);
        if (is_redundant)
          index_hint_as_redundant(h);
        else
          index_hint(h);  /* NOTE: this zeroes h->weight */
      }
    }

    /* Restore hint degradation weights and last_matched_given from
       checkpoint metadata.  index_hint zeroes h->weight, so we must
       re-apply the saved values.  last_matched_given drives hint expiry
       and re-match statistics.  Hints matched by position. */
    {
      int hint_pos = 0, restored = 0;
      int i;
      for (i = 0; i < Resume_meta_count; i++) {
        if (strcmp(Resume_meta[i].list_name, "hints") == 0) {
          if (Resume_meta[i].weight != 0.0 || Resume_meta[i].last_matched != 0) {
            int hid = hint_pos + 1;
            Clist_pos hp;
            for (hp = Glob.hints->first; hp != NULL; hp = hp->next) {
              if (hp->c->id == (unsigned long long)hid) {
                if (Resume_meta[i].weight != 0.0)
                  hp->c->weight = Resume_meta[i].weight;
                if (Resume_meta[i].last_matched != 0)
                  hp->c->last_matched_given = Resume_meta[i].last_matched;
                restored++;
                break;
              }
            }
          }
          hint_pos++;
        }
      }
      if (restored > 0)
        printf("%%   Restored %d hint degradation weights.\n", restored);
    }

    /* Restore matching_hint pointers from checkpoint metadata */
    if (Resume_meta != NULL) {
      int i, restored = 0;
      Topform *hint_arr = NULL;
      int hint_count = Glob.hints->length;
      if (hint_count > 0) {
        hint_arr = (Topform *) safe_malloc((hint_count+1) * sizeof(Topform));
        for (p = Glob.hints->first; p != NULL; p = p->next) {
          Topform h = p->c;
          if (h->id >= 1 && h->id <= (unsigned long long)hint_count)
            hint_arr[h->id] = h;
        }
      }
      for (i = 0; i < Resume_meta_count; i++) {
        if (Resume_meta[i].hint_match > 0 && hint_arr != NULL &&
            Resume_meta[i].hint_match <= hint_count) {
          Topform c = find_clause_by_id(Resume_meta[i].id);
          if (c != NULL) {
            c->matching_hint = hint_arr[Resume_meta[i].hint_match];
            restored++;
          }
        }
      }
      if (hint_arr) safe_free(hint_arr);
      safe_free(Resume_meta);
      Resume_meta = NULL;
      if (restored > 0)
        printf("%%   Restored %d hint matches from checkpoint.\n", restored);
    }

    /* Insert SOS clauses into weight-ordered AVL for given selection. */
    {
      Clist temp_sos;
      fprintf(stderr, "%% Inserting %d SOS clauses into selection queue...\n",
              Glob.sos->length);
      fflush(stderr);
      temp_sos = clist_init("temp_sos");
      while (Glob.sos->first) {
        Topform c = Glob.sos->first->c;
        clist_remove(c, Glob.sos);
        clist_append(c, temp_sos);
      }
      while (temp_sos->first) {
        Topform c = temp_sos->first->c;
        clist_remove(c, temp_sos);
        insert_into_sos2(c, Glob.sos);
      }
      clist_zap(temp_sos);
    }
  }

  /* 9. Restore selector cycle state */
  if (Resume_low_selector_name[0] != '\0')
    set_low_selector_state(Resume_low_selector_name,
                           Resume_low_selector_count);
  if (Resume_high_selector_name[0] != '\0')
    set_high_selector_state(Resume_high_selector_name,
                            Resume_high_selector_count);

  /* 10. Verify checkpoint hashes */
  if (flag(Opt->checkpoint_verify))
    verify_checkpoint_hashes(Resume_dir);

  if (flag(Opt->print_derivations))
    get_hit_list();

  /* 11. Update stats and print status */
  update_stats();

  if (!flag(Opt->quiet)) {
    printf("%% Resumed: sos=%d, usable=%d, demods=%d, disabled=%d\n",
           Glob.sos->length, Glob.usable->length, Glob.demods->length,
           Glob.disabled->length);
    print_separator(stdout, "end of process initial clauses", TRUE);
    print_separator(stdout, "CLAUSES FOR SEARCH", TRUE);
  }

  if (flag(Opt->print_initial_clauses)) {
    printf("\n%% Clauses after checkpoint restore:\n");
    fwrite_clause_clist(stdout, Glob.usable, CL_FORM_STD);
    fwrite_clause_clist(stdout, Glob.sos, CL_FORM_STD);
    fwrite_demod_clist(stdout, Glob.demods, CL_FORM_STD);
  }
  if (!flag(Opt->quiet) && Glob.hints->length > 0) {
    int redundant = redundant_hints();
    printf("\n%% %d hints (%d processed, %d redundant).\n",
           Glob.hints->length - redundant, Glob.hints->length, redundant);
  }

  if (!flag(Opt->quiet))
    print_separator(stdout, "end of clauses for search", TRUE);
}  /* load_checkpoint_into_loop */

/*************
 *
 *   set_progress_callback()
 *
 *   Install a callback that search() invokes at key preprocessing
 *   stages and periodically during the main loop.  Used by the
 *   -cores N scheduler for shared-memory progress reporting.
 *
 *************/

/* PUBLIC */
void set_progress_callback(Search_progress_fn fn)
{
  Progress_callback = fn;
}  /* set_progress_callback */

/*************
 *
 *   search()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Prover_results search(Prover_input p)
{
  int return_code = setjmp(Jump_env);
  if (return_code != 0) {
    // we just landed from longjmp(); fix return code and return
    if (!Opt || !flag(Opt->quiet))
      print_separator(stdout, "end of search", TRUE);
    Glob.return_code = (return_code == INT_MAX ? 0 : return_code);
    fatal_setjmp();  /* This makes longjmps cause a fatal_error. */
    return collect_prover_results(p->xproofs);
  }
  else {
    // search for a proof

    if (!flag(p->options->quiet))
      print_separator(stdout, "PROCESS INITIAL CLAUSES", TRUE);

    Opt = p->options;          // put options into a global variable
    Glob.initialized = TRUE;   // this signifies that Glob is being used
    Glob.has_goals = p->has_goals;  // for SZS status: Theorem vs Unsatisfiable
    Glob.has_neg_conj = p->has_neg_conj; // CNF negated_conjecture (refutation)
    Glob.problem_name = p->problem_name;  // for SZS "for <name>" suffix

    enable_sigusr1_report();   // SIGUSR1 now safe (Opt/Glob ready)
    enable_sigusr2_checkpoint(); // SIGUSR2 now safe (Opt/Glob ready)

    // Arm wall-clock timeout via SIGALRM (replaces polling in hot loop)
    setup_timeout_signal(parm(Opt->max_seconds));

#ifdef __EMSCRIPTEN__
    {
      int wasm_max_sec = parm(Opt->max_seconds);
      Wasm_deadline_ms = (wasm_max_sec > 0)
        ? emscripten_get_now() + wasm_max_sec * 1000.0
        : 0;
    }
#endif

    // Enable comma formatting for statistics if requested
    if (flag(Opt->comma_stats))
      set_comma_formatting(TRUE);

    // Set candidate limits for index queries
    set_candidate_limits(parm(Opt->candidate_warn_limit),
                         parm(Opt->candidate_hard_limit));

    To_trace_id = parm(Opt->cl_to_trace);

    Glob.start_time  = user_seconds();
    Glob.start_ticks = bogo_ticks();

    if (flag(Opt->sort_initial_sos) && plist_count(p->sos) <= 100)
      p->sos = sort_plist(p->sos,
			  (Ordertype (*)(void*, void*)) clause_compare_m4);

    // Move clauses and term lists into Glob; do not assign IDs to clauses.

    Glob.usable  = move_clauses_to_clist(p->usable, "usable", FALSE);
    Glob.sos     = move_clauses_to_clist(p->sos, "sos", FALSE);
    Glob.demods  = move_clauses_to_clist(p->demods,"demodulators",FALSE);
    Glob.hints   = move_clauses_to_clist(p->hints, "hints", FALSE);

    Glob.weights          = tlist_copy(p->weights);
    Glob.kbo_weights      = tlist_copy(p->kbo_weights);
    Glob.actions          = tlist_copy(p->actions);
    Glob.interps          = tlist_copy(p->interps);
    Glob.given_selection  = tlist_copy(p->given_selection);
    Glob.keep_rules       = tlist_copy(p->keep_rules);
    Glob.delete_rules     = tlist_copy(p->delete_rules);

    // Allocate auxiliary clause lists.

    Glob.limbo    = clist_init("limbo");
    Glob.disabled = clist_init("disabled");
    Glob.empties  = NULL;

    if (p->resume_dir) {
      // Resume from checkpoint.  Minimal setup here — the actual checkpoint
      // data is loaded inside the main loop's first iteration, at the same
      // program point as the checkpoint save (before make_inferences).
      // saved_input.txt has clear(auto_inference)/clear(auto_process) so
      // init_search won't re-run auto-mode on the empty clause lists.

      Resume_dir = p->resume_dir;  // set BEFORE init_search so it can
                                    // skip duplicate given_selection/delete_rules
      resume_load_precedence(p->resume_dir);  // set preliminary precedence
                                               // BEFORE init_search so
                                               // symbol_order uses it
      basic_clause_properties(Glob.sos, Glob.usable);
      init_search();
      Load_checkpoint = TRUE;
    }
    else {
      // Normal path.

      if (flag(Opt->print_initial_clauses)) {
        printf("\n%% Clauses before input processing:\n");
        fwrite_clause_clist(stdout, Glob.usable,  CL_FORM_STD);
        fwrite_clause_clist(stdout, Glob.sos,     CL_FORM_STD);
        fwrite_clause_clist(stdout, Glob.demods,  CL_FORM_STD);
        if (Glob.hints->length > 0)
	  printf("\n%% %d hints input.\n", Glob.hints->length);
      }

      // Predicate elimination (may add to sos and move clauses to disabled)

      if (Progress_callback)
        Progress_callback(STAGE_PRED_ELIM, (int) Stats.given, (int) Stats.kept,
                          (int) Stats.sos_size, (int) Stats.usable_size,
                          (int) megs_malloced());

      if (flag(p->options->predicate_elim) && clist_empty(Glob.usable)) {
        if (flag(Opt->fast_pred_elim))
          set_pred_elim_timeout(3);  /* 3s limit */
        if (!flag(Opt->quiet))
          print_separator(stdout, "PREDICATE ELIMINATION", TRUE);
        predicate_elimination(Glob.sos, Glob.disabled, !flag(Opt->quiet));
        if (!flag(Opt->quiet))
          print_separator(stdout, "end predicate elimination", TRUE);
      }

      if (Progress_callback)
        Progress_callback(STAGE_BASIC_PROPS, (int) Stats.given, (int) Stats.kept,
                          (int) Stats.sos_size, (int) Stats.usable_size,
                          (int) megs_malloced());

      basic_clause_properties(Glob.sos, Glob.usable);

      // Possible special treatment for denials (negative in Horn sets)

      if (flag(Opt->auto_denials))
        auto_denials(Glob.sos, Glob.usable, Opt);

      if (Progress_callback)
        Progress_callback(STAGE_INIT_SEARCH, (int) Stats.given, (int) Stats.kept,
                          (int) Stats.sos_size, (int) Stats.usable_size,
                          (int) megs_malloced());

      init_search();  // init clocks, ordering, auto-mode, init packages

      if (Progress_callback)
        Progress_callback(STAGE_INDEX_INITIAL, (int) Stats.given, (int) Stats.kept,
                          (int) Stats.sos_size, (int) Stats.usable_size,
                          (int) megs_malloced());

      index_and_process_initial_clauses();
      if (flag(Opt->print_derivations))
	get_hit_list();
    }

    if (!flag(Opt->quiet))
      print_separator(stdout, "SEARCH", TRUE);

    if (!flag(Opt->quiet))
      printf("\n%% Starting search at %.2f seconds.\n", user_seconds());
    fflush(stdout);
    Glob.start_time = user_seconds();
    Glob.searching = TRUE;

    /* Signal that preprocessing is complete and search is starting. */
    if (Progress_callback)
      Progress_callback(STAGE_SEARCHING, 0, (int) Stats.kept,
                        (int) Stats.sos_size, (int) Stats.usable_size,
                        (int) megs_malloced());

    if (parm(Opt->checkpoint_minutes) > 0) {
      int mins = parm(Opt->checkpoint_minutes);
      if (mins < 1) {
        fprintf(stderr,
          "WARNING: checkpoint_minutes=%d too small, using 1.\n", mins);
        assign_parm(Opt->checkpoint_minutes, 1, TRUE);
      }
      Last_auto_ckpt_time = time(NULL);
    }

    /* Set wall-clock deadline for clash_recurse() timeout.
       Prevents indefinite hangs inside hyper/UR/binary resolution. */
    if (parm(Opt->max_seconds) >= 0)
      set_clash_deadline(time(NULL) + (time_t)parm(Opt->max_seconds));


    // ****************************** Main Loop ******************************
    //
    // Checkpoint save and load happen at the TOP of the loop, BEFORE
    // make_inferences().  At this point limbo is empty (drained by the
    // previous iteration's limbo_process).  Save and load at the same
    // program point guarantees bit-identical state on resume.

    while (Load_checkpoint || inferences_to_make()) {

#ifndef __EMSCRIPTEN__
      // Checkpoint save triggers (periodic / SIGUSR2).
      // Skip on the first iteration if we are loading a checkpoint.
      if (!Load_checkpoint) {

        // Check for periodic automatic checkpoint
        if (parm(Opt->checkpoint_minutes) > 0) {
          time_t now = time(NULL);
          if (now - Last_auto_ckpt_time >=
              (time_t)parm(Opt->checkpoint_minutes) * 60) {
            char auto_dir[512];
            fprintf(stderr, "\nPeriodic checkpoint at given #%llu...\n",
                    Stats.given);
            fflush(stderr);
            write_checkpoint();
            fprintf(stderr, "\nCheckpoint saved at given #%llu.\n",
                    Stats.given);
            fflush(stderr);
            Last_auto_ckpt_time = now;
            snprintf(auto_dir, sizeof(auto_dir),
                     "prover9_%d_ckpt_%llu", getpid(), Stats.given);
            record_auto_checkpoint(auto_dir);
            if (flag(Opt->checkpoint_exit))
              done_with_search(CHECKPOINT_EXIT);
          }
        }

        // Check for SIGUSR2 checkpoint request
        if (checkpoint_requested()) {
          fprintf(stderr, "\nCheckpoint requested at given #%llu...\n",
                  Stats.given);
          fflush(stderr);
          write_checkpoint();
          fprintf(stderr, "\nCheckpoint saved at given #%llu.\n",
                  Stats.given);
          fflush(stderr);
          clear_checkpoint_request();
          if (flag(Opt->checkpoint_exit))
            done_with_search(CHECKPOINT_EXIT);
        }


      }  /* !Load_checkpoint */
#endif /* !__EMSCRIPTEN__ */


      // Checkpoint load (resume — first iteration only).
      if (Load_checkpoint) {
        load_checkpoint_into_loop();
        Load_checkpoint = FALSE;
      }

      // make_inferences: each inferred clause is cl_processed, which
      // does forward demodulation and subsumption; if the clause is kept
      // it is put on the Limbo list, and it is indexed so that it can be
      // used immediately with subsequent newly inferred clauses.


      make_inferences();

#ifdef __EMSCRIPTEN__
      if (Wasm_deadline_ms > 0 && emscripten_get_now() > Wasm_deadline_ms)
        done_with_search(MAX_SECONDS_EXIT);
#endif

      if (Progress_callback && Stats.given % 100 == 0)
        Progress_callback(STAGE_SEARCHING, (int) Stats.given, (int) Stats.kept,
                          (int) Stats.sos_size, (int) Stats.usable_size,
                          (int) megs_malloced());

      /* Periodic hint expiry sweep */
      if (parm(Opt->hint_expiry) > 0 &&
	  Stats.given % (unsigned long long) parm(Opt->hint_sweep_interval) == 0) {
	int expired = expire_old_hints(Stats.given,
				       (unsigned long long) parm(Opt->hint_expiry),
				       parm(Opt->hint_expiry_min),
				       Glob.hints);
	if (expired > 0)
	  fprintf(stderr, "%% Expired %d hints at given #%llu (%d active).\n",
		  expired, Stats.given, active_hints());
      }

      // limbo_process: this applies back subsumption, back demodulation,
      // and other operations that can disable clauses.  Limbo clauses
      // are moved to the Sos list.

      limbo_process(FALSE);

    }  // ************************ end of main loop ************************

    if (Progress_callback)
      Progress_callback(STAGE_DONE, (int) Stats.given, (int) Stats.kept,
                        (int) Stats.sos_size, (int) Stats.usable_size,
                        (int) megs_malloced());

    fprint_all_stats(stdout, Opt ? stringparm1(Opt->stats) : "lots");
    if (!flag(Opt->quiet))
      print_separator(stdout, "end of search", TRUE);
    fatal_setjmp();  /* This makes longjmps cause a fatal_error. */
    Glob.return_code = Glob.empties ? MAX_PROOFS_EXIT : SOS_EMPTY_EXIT;
    return collect_prover_results(p->xproofs);
  }
}  /* search */

#ifndef __EMSCRIPTEN__

/*************
 *
 *   forking_search()
 *
 *************/

/* DOCUMENTATION
This is similar to search(), except that a child process is created
to do the search, and the child sends its results to the parent on
a pipe.

<P>
The parameters and results are the same as search().
As in search(), the Plists lists of objets (the parameters) are not changed.
*/

/* PUBLIC */
Prover_results forking_search(Prover_input input)
{
  Prover_results results;

  int rc;
  int fd[2];          /* pipe for child -> parent data */

  rc = pipe(fd);
  if (rc != 0) {
    perror("");
    fatal_error("forking_search: pipe creation failed");
  }

  fflush(stdout);
  fflush(stderr);
  rc = fork();
  if (rc < 0) {
    perror("");
    fatal_error("forking_search: fork failed");
  }

  /* kludge to get labels that might be introduced by child into symtab */
  (void) str_to_sn("flip_matches_hint", 0);

  if (rc == 0) {

    /*********************************************************************/
    /* This is the child process.  Search, send results to parent, exit. */
    /*********************************************************************/

    int to_parent = fd[1];  /* fd for writing data to parent */
    close(fd[0]);           /* close "read" end of pipe */

    fprintf(stdout,"\nChild search process %d started.\n", my_process_id());

    /* Remember how many symbols are in the symbol table.  If new symbols
       are introduced during the search, we have to send them to the
       parent so that clauses sent to the parent can be reconstructed.
    */

    mark_for_new_symbols();

    /* search */
    
    results = search(input);

    /* send results to the parent */

    {
      /* Format of data (all integers) sent to parent:
	---------------------- 
	nymber-of-new-symbols
	  symnum
	  arity
          ...
	number-of-proofs
	  number-of-steps
	    [clauses-in-proof]
	  number-of-steps
	    [clauses-in-proof]
          ...
        [same for xproofs]

	stats  (MAX_STATS of them)
	user_milliseconds
	system_milliseconds
	return_code

      */

      Ibuffer ibuf = ibuf_init();
      Plist p, a;
      I2list new_symbols, q;

      /* collect and write new_symbols */

      new_symbols = new_symbols_since_mark();
      ibuf_write(ibuf, i2list_count(new_symbols));
      for (q = new_symbols; q; q = q->next) {
	ibuf_write(ibuf, q->i);
	ibuf_write(ibuf, q->j);
      }
      zap_i2list(new_symbols);

      /* collect and write proofs */

      ibuf_write(ibuf, plist_count(results->proofs));  /* number of proofs */
      for (p = results->proofs; p; p = p->next) {
	ibuf_write(ibuf, plist_count(p->v));  /* steps in this proof */
	for (a = p->v; a; a = a->next) {
	  put_clause_to_ibuf(ibuf, a->v);
	}
      }
      
      /* collect and write xproofs */

      ibuf_write(ibuf, plist_count(results->xproofs));  /* number of xproofs */
      for (p = results->xproofs; p; p = p->next) {
	ibuf_write(ibuf, plist_count(p->v));  /* steps in this proof */
	for (a = p->v; a; a = a->next)
	  put_clause_to_ibuf(ibuf, a->v);
      }
      
      {
	/* collect stats (shortcut: handle stats struct as sequence of ints) */
	int *x = (void *) &(results->stats);
	int n = sizeof(struct prover_stats) / sizeof(int);
	int i;
	for (i = 0; i < n; i++)
	  ibuf_write(ibuf, x[i]);
      }

      /* collect clocks */
      ibuf_write(ibuf, (int) (results->user_seconds * 1000));
      ibuf_write(ibuf, (int) (results->system_seconds * 1000));
      /* collect return_code */
      ibuf_write(ibuf, results->return_code);

      /* write the data to the pipe */

      rc = write(to_parent,
		 ibuf_buffer(ibuf),
		 ibuf_length(ibuf) * sizeof(int));
      if (rc == -1) {
	perror("");
	fatal_error("forking_search, write error");
      }
      else if (rc != ibuf_length(ibuf) * sizeof(int))
	fatal_error("forking_search, incomplete write from child to parent");

      rc = close(to_parent);
      
      ibuf_free(ibuf);  /* not necessary, because we're going to exit now */
    }

    /* child exits */

    exit_with_message(stdout, results->return_code);
    
    return NULL;  /* won't happen */

  }  /* end of child code */

  else {

    /*********************************************************************/
    /* This is the parent process.  Get results from child, then return. */
    /*********************************************************************/

    int from_child = fd[0];  /* fd for reading data from child */
    close(fd[1]);            /* close "write" end of pipe */

    /* read results from child (read waits until data are available) */

    {
      Ibuffer ibuf = fd_read_to_ibuf(from_child);
      int num_proofs, num_steps, i, j;
      int num_new_symbols;
      I2list new_syms = NULL;

      results = safe_calloc(1, sizeof(struct prover_results));
      
      /* read new_symbols */

      num_new_symbols = ibuf_read(ibuf);
      for (i = 0; i < num_new_symbols; i++) {
	int symnum = ibuf_read(ibuf);
	int arity = ibuf_read(ibuf);
	new_syms = i2list_append(new_syms, symnum, arity);
      }
      add_new_symbols(new_syms);  /* add new symbols to symbol table */
      zap_i2list(new_syms);

      /* read proofs */

      num_proofs = ibuf_read(ibuf);
      for (i = 0; i < num_proofs; i++) {
	Plist proof = NULL;
	num_steps = ibuf_read(ibuf);
	for (j = 0; j < num_steps; j++) {
	  Topform c = get_clause_from_ibuf(ibuf);
	  proof = plist_prepend(proof, c);  /* build backward, reverse later */
	}
	results->proofs = plist_append(results->proofs, reverse_plist(proof));
      }

      /* read xproofs */

      num_proofs = ibuf_read(ibuf);
      for (i = 0; i < num_proofs; i++) {
	Plist proof = NULL;
	num_steps = ibuf_read(ibuf);
	for (j = 0; j < num_steps; j++) {
	  Topform c = get_clause_from_ibuf(ibuf);
	  proof = plist_prepend(proof, c);  /* build backward, reverse later */
	}
	results->xproofs = plist_append(results->xproofs,reverse_plist(proof));
      }

      {
	/* read stats (shortcut: handle stats struct as sequence of ints) */
	int *x = (void *) &(results->stats);
	int n = sizeof(struct prover_stats) / sizeof(int);
	int i;
	for (i = 0; i < n; i++)
	  x[i] = ibuf_read(ibuf);
      }

      /* read clocks */
      results->user_seconds = ibuf_read(ibuf) / 1000.0;
      results->system_seconds = ibuf_read(ibuf) / 1000.0;
      /* read return_code */
      results->return_code = ibuf_read(ibuf);
    }

    /* Wait for child to exit and get the exit code.  We should not
       have to wait long, because we already have its results. */

    {
      int child_status, child_exit_code;
      wait(&child_status);
      if (!WIFEXITED(child_status))
	fatal_error("forking_search: child terminated abnormally");
      child_exit_code = WEXITSTATUS(child_status);
      results->return_code = child_exit_code;
    }

    rc = close(from_child);

    return results;
  }  /* end of parent code */
}  /* forking_search */

#endif /* !__EMSCRIPTEN__ */
