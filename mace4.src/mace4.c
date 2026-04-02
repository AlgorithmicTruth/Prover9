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

#include "msearch.h"

#include "../ladr/banner.h"
#include "../ladr/memory.h"
#include "../ladr/tptp_parse.h"
#include "../ladr/tptp_trans.h"
#include "../ladr/fatal.h"

#ifndef __EMSCRIPTEN__
#include <signal.h>
#endif
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#ifndef __EMSCRIPTEN__
#include <sys/time.h>
#endif

#ifdef __EMSCRIPTEN__
#include <emscripten.h>
#endif

/* Checkpoint signal flag -- accessed by msearch.c via extern */
#ifndef __EMSCRIPTEN__
volatile sig_atomic_t Mace4_checkpoint_requested_flag = 0;
#else
int Mace4_checkpoint_requested_flag = 0;
#endif

/*************
 *
 *   init_attrs()
 *
 *************/

void init_attrs(void)
{
  // This will allow these attributes to occur on clauses.
  // Mace4 will ignore these attributes.

  (void) register_attribute("label",         STRING_ATTRIBUTE);
  (void) register_attribute("bsub_hint_wt",     INT_ATTRIBUTE);
  (void) register_attribute("answer",          TERM_ATTRIBUTE);
  (void) register_attribute("action",          TERM_ATTRIBUTE);
  (void) register_attribute("action2",         TERM_ATTRIBUTE);
}  /* init_attrs */

/*************
 *
 *   mace4_sig_handler()
 *
 *************/

/* DOCUMENTATION
*/

#ifndef __EMSCRIPTEN__
/* PUBLIC */
void mace4_sig_handler(int condition)
{
  switch (condition) {
  case SIGALRM:
    /* Wall-clock timeout -- fires asynchronously regardless of where
       mace4 is (clausification, propagation, etc.). */
    mace4_exit(MAX_SEC_NO_EXIT);
    break;
  case SIGSEGV:
    p_stats();
    mace4_exit(MACE_SIGSEGV_EXIT);
    break;
  case SIGINT:
    p_stats();
    mace4_exit(MACE_SIGINT_EXIT);
    break;
  case SIGTERM:
    mace4_exit(MACE_SIGTERM_EXIT);
    break;
  case SIGUSR1:
    p_stats();
    fflush(stdout);
    break;
  case SIGUSR2:
    Mace4_checkpoint_requested_flag = 1;
    signal(SIGUSR2, mace4_sig_handler);  /* re-arm */
    break;
#ifdef SIGXCPU
  case SIGXCPU:
    mace4_exit(MAX_SEC_NO_EXIT);
    break;
#endif
  default: fatal_error("mace4_sig_handler, unknown signal");
  }
}  /* mace4_sig_handler */
#endif /* !__EMSCRIPTEN__ */

/*************
 *
 *   process_distinct_terms()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Plist process_distinct_terms(Plist distinct)
{
  Plist p;
  Plist forms = NULL;
  for (p = distinct; p; p = p->next) {
    Term list = p->v;
    if (!proper_listterm(list))
      fatal_error("process_distinct_terms: lists must be proper, e.g., [a,b,c].\n");
    while (!nil_term(list)) {
      Term a = ARG(list,0);
      Term rest = ARG(list,1);
      while (!nil_term(rest)) {
	Term b = ARG(rest,0);
	Term neq = build_unary_term_safe(not_sym(),
					 build_binary_term_safe(eq_sym(),
								copy_term(a),
								copy_term(b)));
	Formula f = term_to_formula(neq);
	zap_term(neq);
	forms = plist_append(forms, f);
	rest = ARG(rest, 1);
      }
      list = ARG(list, 1);
    }
  }
  return forms;
}  /* process_distinct_terms */

/*************
 *
 *   read_mace4_input()
 *
 *************/

static
Plist read_mace4_input(int argc, char **argv, BOOL allow_unknown_things,
		      Mace_options opt)
{
  Plist wild_formulas, goals;
  Plist distinct_lists, distinct_forms;
  Plist wild_terms, hints;  /* we won't use these */

  // Tell the top_input package what lists to accept and where to put them.

  // Accept hints, but they will not be used.

  accept_list("hints", FORMULAS, TRUE, &hints);

  // Accept goals; these are negated individually (each must be falsified)

  accept_list("goals", FORMULAS, FALSE, &goals);

  // Accept lists of distinct items

  accept_list("distinct", TERMS, FALSE, &distinct_lists);

  // Accept any other clauses and formulas.  Each must be true.

  accept_list("",    FORMULAS, FALSE, &wild_formulas);

  // Accept any terms.  These will not be used.

  accept_list("",      TERMS,    FALSE, &wild_terms);

  // Read commands such as set, clear, op, lex.
  // Read lists, filling in variables given to the accept_list calls.

  print_separator(stdout, "INPUT", TRUE);

  read_all_input(argc, argv, stdout, TRUE,
		 allow_unknown_things ? WARN_UNKNOWN : KILL_UNKNOWN);

  if (wild_terms)
    printf("%%   term list(s) ignored\n");
  if (hints)
    printf("%%   hints list(s) ignored\n");

  process_command_line_args(argc, argv, opt);

  print_separator(stdout, "end of input", TRUE);

  if (!option_dependencies_state()) {
    /* This might be needed in the future. */
    printf("\n%% Enabling option dependencies (ignore applies only on input).\n");
    enable_option_dependencies();
  }

  distinct_forms = process_distinct_terms(distinct_lists);
  wild_formulas = plist_cat(wild_formulas, distinct_forms);

  wild_formulas = embed_formulas_in_topforms(wild_formulas, TRUE);
  goals = embed_formulas_in_topforms(goals, FALSE);

  // Clausify 

  print_separator(stdout, "PROCESS NON-CLAUSAL FORMULAS", TRUE);
  printf("\n%% Formulas that are not ordinary clauses:\n");

  wild_formulas = process_input_formulas(wild_formulas, TRUE);
  goals = process_goal_formulas(goals, TRUE);  /* negates goals */

  print_separator(stdout, "end of process non-clausal formulas", TRUE);

  wild_formulas = plist_cat(wild_formulas, goals);

  return wild_formulas;
}  /* read_mace4_input */

/*************
 *
 *   main()
 *
 *************/

int main(int argc, char **argv)
{
  struct mace_options opt;
  Plist clauses;
  Mace_results results;
  BOOL tptp_mode = FALSE;
  BOOL ladr_output = FALSE;   /* -ladr_out: LADR model format with TPTP input */
  char *tptp_file = NULL;     /* .p filename or NULL (stdin) */
  char *problem_name = NULL;
  BOOL has_goals = FALSE;
  char *resume_dir = NULL;    /* -r checkpoint directory */
  BOOL resume_from_tptp = FALSE; /* original run was TPTP mode */
  char *saved_command;
  int prescan_timeout = -1;   /* -t value from pre-scan, for early SIGALRM */
  (void) prescan_timeout;     /* used only in signal setup (non-WASM) */

  /* Save original command line before any argv mutation. */
  saved_command = build_command_string(argc, argv);

  /* Following says whether to ignore unregognized set/clear/assigns. */
  BOOL prover_compatability_mode = member_args(argc, argv, "-c");

  /* Pre-scan for -r resume directory */
  {
    int i;
    for (i = 1; i < argc; i++) {
      if (strcmp(argv[i], "-r") == 0 && i + 1 < argc) {
        resume_dir = argv[i+1];
        i++;
      }
    }
  }

  /* Check for memory logging flag before init */
  if (member_args(argc, argv, "-A"))
    enable_memory_logging();

  /* Quick pre-scan for TPTP indicators */
  {
    int i;
    char *f_arg = NULL;  /* capture -f argument for all checks */
    for (i = 1; i < argc; i++) {
      if (strcmp(argv[i], "-tptp") == 0) {
        tptp_mode = TRUE;
      }
      if (strcmp(argv[i], "-ladr_out") == 0 ||
          strcmp(argv[i], "-ladr-out") == 0) {
        ladr_output = TRUE;
        argv[i] = "-c";  /* consumed; -c is a harmless no-op in getopt */
      }
      if (strcmp(argv[i], "-t") == 0 && i + 1 < argc) {
        prescan_timeout = atoi(argv[i+1]);
      }
      if (strcmp(argv[i], "-f") == 0 && i + 1 < argc) {
        int len = strlen(argv[i+1]);
        f_arg = argv[i+1];
        /* .p or .ax extension auto-enables TPTP mode */
        if ((len >= 2 && strcmp(argv[i+1] + len - 2, ".p") == 0) ||
            (len >= 3 && strcmp(argv[i+1] + len - 3, ".ax") == 0)) {
          tptp_mode = TRUE;
          tptp_file = argv[i+1];
        }
      }
      /* Bare positional .p or .ax file (no -f flag) */
      if (argv[i][0] != '-') {
        int len = strlen(argv[i]);
        if ((len >= 2 && strcmp(argv[i] + len - 2, ".p") == 0) ||
            (len >= 3 && strcmp(argv[i] + len - 3, ".ax") == 0)) {
          tptp_mode = TRUE;
          tptp_file = argv[i];
        }
      }
    }
    /* If -tptp flag given with -f but file didn't have .p/.ax extension,
       still use the -f file (e.g., -tptp -f problem.tptp) */
    if (tptp_mode && tptp_file == NULL && f_arg != NULL)
      tptp_file = f_arg;
  }

  /* Set TPTP globals early so that mace4_exit() produces SZS output
     even if SIGALRM fires during scanning/parsing/clausifying. */
  if (tptp_mode) {
    Mace4_tptp_mode = TRUE;
    /* Extract problem name from filename for SZS status line */
    if (tptp_file != NULL) {
      const char *base = strrchr(tptp_file, '/');
      int len;
      base = (base != NULL) ? base + 1 : tptp_file;
      len = strlen(base);
      if (len >= 2 && strcmp(base + len - 2, ".p") == 0)
        len -= 2;
      if (len > 0) {
        problem_name = safe_malloc(len + 1);
        memcpy(problem_name, base, len);
        problem_name[len] = '\0';
        Mace4_problem_name = problem_name;
      }
    }
  }

  init_standard_ladr();
  init_mace_options(&opt);  /* We must do this before calling usage_message. */
  init_attrs();

  if (member_args(argc, argv, "help") ||
      member_args(argc, argv, "-help")) {
    usage_message(stderr, &opt);
    exit(1);
  }

  print_banner(saved_command, PROGRAM_NAME, PROGRAM_VERSION, PROGRAM_DATE,
               tptp_mode);
  set_program_name(PROGRAM_NAME);   /* for conditional input */

#ifndef __EMSCRIPTEN__
  signal(SIGINT,  mace4_sig_handler);
  signal(SIGTERM, mace4_sig_handler);
  signal(SIGUSR1, mace4_sig_handler);
  signal(SIGSEGV, mace4_sig_handler);
#ifdef SIGXCPU
  signal(SIGXCPU, mace4_sig_handler);
#endif
  signal(SIGUSR2, SIG_IGN);  /* ignore until search is ready */

  /* Arm wall-clock timeout via SIGALRM.
     Must be armed BEFORE scanning/parsing/clausifying, which can hang
     on large TPTP problems.  Uses pre-scanned -t value from argv.
     Also covers LADR-mode assign(max_seconds, N) via the later check. */
  if (prescan_timeout > 0) {
    struct itimerval itv;
    signal(SIGALRM, mace4_sig_handler);
    memset(&itv, 0, sizeof(itv));
    itv.it_value.tv_sec = prescan_timeout;
    setitimer(ITIMER_REAL, &itv, NULL);
  }
#endif /* !__EMSCRIPTEN__ */

  /* If resuming from checkpoint, check if original was TPTP mode
     and redirect stdin to saved_input.txt */
  if (resume_dir != NULL && !tptp_mode) {
    char saved_input_path[512];
    char meta_path[512];
    FILE *mfp;

    /* Early read of metadata.txt to check tptp_mode */
    sprintf(meta_path, "%s/metadata.txt", resume_dir);
    mfp = fopen(meta_path, "r");
    if (mfp != NULL) {
      char key[64];
      char val[64];
      while (fscanf(mfp, "%63s %63s", key, val) == 2) {
        if (strcmp(key, "tptp_mode") == 0 && atoi(val) != 0) {
          /* Original run was TPTP mode -- register TPTP parse operators
             to match symbol table ordering from original run */
          declare_tptp_input_types();
          set_variable_style(PROLOG_STYLE);
          resume_from_tptp = TRUE;
          break;
        }
      }
      fclose(mfp);
    }

    sprintf(saved_input_path, "%s/saved_input.txt", resume_dir);
    if (freopen(saved_input_path, "r", stdin) == NULL) {
      fprintf(stderr, "ERROR: cannot open %s for resume\n", saved_input_path);
      exit(1);
    }
    fprintf(stderr, "Resuming from checkpoint: %s\n", resume_dir);
  }

  if (tptp_mode) {
    /*=======================================================================
     * TPTP mode: use native TPTP parser, SZS output.
     *=======================================================================*/
    Scan_result scan;
    Tptp_input tptp;
    Plist assumptions, goals_list;

    declare_tptp_input_types();
    set_variable_style(PROLOG_STYLE);

    /* Phase 1: Scan */
    if (tptp_file)
      scan = scan_tptp_formulas(tptp_file);
    else
      scan = scan_tptp_stream(stdin, "<stdin>");

    has_goals = (scan->n_goals > 0);

    /* Phase 2: Parse all formulas (no SInE for mace4) */
    tptp = parse_scanned_formulas(scan, NULL);

    /* Inject distinct object inequality axioms */
    {
      Plist dobj = tptp_distinct_object_axioms(tptp->distinct_objects);
      if (dobj)
        tptp->assumptions = plist_cat(tptp->assumptions, dobj);
    }

    /* Set up SZS error output before clausify (max_vars can fatal) */
    set_fatal_tptp_mode(TRUE, problem_name);
    set_fatal_szs_status("GaveUp");

    /* Clausify */
    assumptions = embed_formulas_in_topforms(tptp->assumptions, TRUE);
    goals_list = embed_formulas_in_topforms(tptp->goals, FALSE);
    assumptions = process_input_formulas(assumptions, FALSE);
    goals_list = process_goal_formulas(goals_list, FALSE);
    clauses = plist_cat(assumptions, goals_list);

    /* Check for empty clauses ($false): trivially unsatisfiable */
    {
      Plist pp;
      for (pp = clauses; pp; pp = pp->next) {
        Topform tf = pp->v;
        if (tf->literals == NULL) {
          if (Mace4_problem_name)
            printf("%% SZS status Unsatisfiable for %s\n", Mace4_problem_name);
          else
            printf("%% SZS status Unsatisfiable\n");
          printf("\n%% Input contains the empty clause ($false).\n");
          exit(0);
        }
      }
    }

    /* Reset SZS status to default for search phase */
    set_fatal_szs_status(NULL);

    /* Set remaining TPTP globals for msearch.c and print.c.
       Mace4_tptp_mode and Mace4_problem_name are set earlier (pre-scan). */
    Mace4_ladr_output = ladr_output;
    Mace4_has_goals = has_goals;

    /* TPTP default: cap domain size at 1000 to prevent runaway iteration
       on large problems (e.g., BIO001+1 with 73K symbols would try a
       million domain sizes).  User can override with -N. */
    assign_parm(opt.end_size, 1000, FALSE);

    /* Apply command-line overrides (-t, -n, -N, etc.) */
    process_command_line_args(argc, argv, &opt);

    free_scan_result(scan);
    /* Note: tptp->assumptions and tptp->goals are consumed above */
  }
  else {
    /*=======================================================================
     * LADR mode: completely unchanged.
     *=======================================================================*/
    clauses = read_mace4_input(argc, argv, prover_compatability_mode, &opt);

    /* If resuming from a TPTP checkpoint, the LADR parser set symbol types
       to FUNCTION_SYMBOL/PREDICATE_SYMBOL via declare_functions_and_relations().
       In TPTP mode, symbols stay UNSPECIFIED_SYMBOL (the TPTP parser doesn't
       call declare_functions_and_relations).  The lex ordering in
       collect_mace4_syms() depends on symbol types, so we must match the
       original TPTP state by resetting all types to UNSPECIFIED. */
    if (resume_from_tptp) {
      Ilist fsyms = fsym_set_in_topforms(clauses);
      Ilist rsyms = rsym_set_in_topforms(clauses);
      Ilist p;
      for (p = fsyms; p; p = p->next)
        set_symbol_type(p->i, UNSPECIFIED_SYMBOL);
      for (p = rsyms; p; p = p->next)
        set_symbol_type(p->i, UNSPECIFIED_SYMBOL);
      zap_ilist(fsyms);
      zap_ilist(rsyms);
    }

    print_separator(stdout, "CLAUSES FOR SEARCH", TRUE);
    fwrite_clause_list(stdout, clauses, "mace4_clauses", CL_FORM_BARE);
    print_separator(stdout, "end of clauses for search", TRUE);
  }

#ifndef __EMSCRIPTEN__
  /* Enable SIGUSR2 checkpoint handler now that structures are ready */
  signal(SIGUSR2, mace4_sig_handler);

  /* If no -t flag was given on command line, check for assign(max_seconds, N)
     from the input file (LADR mode only) and arm SIGALRM now. */
  if (prescan_timeout <= 0) {
    int max_sec = parm(opt.max_seconds);
    if (max_sec > 0) {
      struct itimerval itv;
      signal(SIGALRM, mace4_sig_handler);
      memset(&itv, 0, sizeof(itv));
      itv.it_value.tv_sec = max_sec;
      setitimer(ITIMER_REAL, &itv, NULL);
    }
  }
#endif /* !__EMSCRIPTEN__ */

  /* Handle resume: read trail and modify mace4 behavior */
  if (resume_dir != NULL) {
    /* Read metadata */
    char meta_path[512];
    FILE *mfp;
    int saved_domain_size = 0;
    unsigned saved_total_models = 0;
    unsigned saved_selections = 0;
    int saved_depth = 0;

    sprintf(meta_path, "%s/metadata.txt", resume_dir);
    mfp = fopen(meta_path, "r");
    if (mfp == NULL) {
      fprintf(stderr, "ERROR: cannot read %s\n", meta_path);
      exit(1);
    }
    {
      char key[64];
      char val[64];
      while (fscanf(mfp, "%63s %63s", key, val) == 2) {
        if (strcmp(key, "domain_size") == 0)
          saved_domain_size = atoi(val);
        else if (strcmp(key, "total_models") == 0)
          saved_total_models = (unsigned)atoi(val);
        else if (strcmp(key, "selections") == 0)
          saved_selections = (unsigned)atoi(val);
        else if (strcmp(key, "search_depth") == 0)
          saved_depth = atoi(val);
      }
    }
    fclose(mfp);

    /* Read trail */
    {
      char trail_path[512];
      FILE *tfp;
      struct search_frame *saved_trail = NULL;
      int d;

      sprintf(trail_path, "%s/trail.txt", resume_dir);
      tfp = fopen(trail_path, "r");
      if (tfp == NULL) {
        fprintf(stderr, "ERROR: cannot read %s\n", trail_path);
        exit(1);
      }

      if (saved_depth > 0)
        saved_trail = (struct search_frame *)
          safe_malloc(saved_depth * sizeof(struct search_frame));

      for (d = 0; d < saved_depth; d++) {
        int depth_check;
        if (fscanf(tfp, "%d %d %d %d %d",
                   &depth_check,
                   &saved_trail[d].cell_id,
                   &saved_trail[d].value_index,
                   &saved_trail[d].last,
                   &saved_trail[d].max_constrained) != 5) {
          fprintf(stderr, "ERROR: malformed trail.txt at depth %d\n", d);
          exit(1);
        }
        saved_trail[d].stk = NULL;
      }
      fclose(tfp);

      fprintf(stderr, "Resume: domain_size=%d, total_models=%u, "
              "depth=%d, selections=%u\n",
              saved_domain_size, saved_total_models,
              saved_depth, saved_selections);

      /* Call mace4 in resume mode.
         We set up global state that mace4() checks. */
      {
        /* These are declared extern in msearch.c */
        extern BOOL Resuming;
        extern int Saved_domain_size;
        extern unsigned Saved_total_models;
        extern struct search_frame *Saved_trail;
        extern int Saved_trail_depth;

        Resuming = TRUE;
        Saved_domain_size = saved_domain_size;
        Saved_total_models = saved_total_models;
        Saved_trail = saved_trail;
        Saved_trail_depth = saved_depth;

        results = mace4(clauses, &opt);

        if (saved_trail != NULL)
          safe_free(saved_trail);
      }
    }
  }
  else {
    results = mace4(clauses, &opt);
  }

  mace4_exit(results->return_code);  /* print messages and exit */

  exit(0);  /* won't happen */

}  /* main */
