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

#include <string.h>
#include <time.h>
#include <sys/stat.h>
#include <stdio.h>
#include <errno.h>
#ifndef __EMSCRIPTEN__
#include <signal.h>
#else
#include <emscripten.h>
#endif

/* #define DEBUG */

/*****************************************************************************/
/* TPTP mode globals (set by mace4.c main) */

BOOL  Mace4_tptp_mode = FALSE;
BOOL  Mace4_ladr_output = FALSE;
BOOL  Mace4_has_goals = FALSE;
char *Mace4_problem_name = NULL;

/*****************************************************************************/
/* Variables -- most are used (extern) by other source files */

/* Options and Statistics */

Mace_options Opt;
struct mace_stats Mstats;

/* List of symbols and associated data */

Symbol_data Symbols;

/* This maps OPS symbol IDs to MACE symbol IDs, which start with 0. */

static int Sn_map_size;
Symbol_data *Sn_to_mace_sn;

/* Cell table is indexed by eterm IDs. */

int Number_of_cells;
struct cell *Cells;           /* the table of cells (dynamically allocated) */
struct cell **Ordered_cells;  /* (pointers to) permutation of Cells */
int First_skolem_cell;

/* Misc Variables*/

int Domain_size;
Term *Domain;    /* array of terms representing (shared) domain elements  */
BOOL Skolems_last;

Plist Ground_clauses;  /* Mclauses (see ground.h) */

int Relation_flag;  /* term flag */
int Negation_flag;  /* term flag */

int Eq_sn;
int Or_sn;
int Not_sn;

static int Max_domain_element_in_input;  /* For Least Number Heuristic */

static Plist Models;  /* in case we collect models as terms */

/* Iterative search stack */

static struct search_frame *Search_stack = NULL;
/* Search_depth not used as a global -- depth is tracked locally */
static int Search_stack_capacity = 0;
static int Current_depth = -1;  /* current search depth, for reporting */

/* Checkpoint state */

static Plist Saved_clauses = NULL;  /* for checkpoint saved_input.txt */
static time_t Last_auto_ckpt_time = 0;
#ifndef __EMSCRIPTEN__
static char *Auto_ckpt_dirs[100];   /* circular buffer */
static int Auto_ckpt_head = 0;
static int Auto_ckpt_count = 0;
#endif
BOOL Resuming = FALSE;       /* TRUE during resume */
int Saved_domain_size = 0;
unsigned Saved_total_models = 0;
struct search_frame *Saved_trail = NULL;
int Saved_trail_depth = 0;

Clock Mace4_clock;

/* stats for entire run */

unsigned Total_models;

static double Start_seconds;
static double Start_domain_seconds;
static long long Start_megs;

#ifdef __EMSCRIPTEN__
static double Wasm_deadline_ms = 0;        /* total timeout deadline */
static double Wasm_domain_deadline_ms = 0; /* per-domain timeout deadline */
#endif

/* end of variables */
/*****************************************************************************/

/* search return codes */

enum {
  SEARCH_GO_MODELS,           /* continue: model(s) found on current path */
  SEARCH_GO_NO_MODELS,        /* continue: no models found on current path */
  SEARCH_MAX_MODELS,          /* stop */
  SEARCH_MAX_MEGS,            /* stop */
  SEARCH_MAX_TOTAL_SECONDS,   /* stop */
  SEARCH_MAX_DOMAIN_SECONDS,  /* stop */
  SEARCH_DOMAIN_OUT_OF_RANGE, /* continue (may fit at larger size) */
  SEARCH_CELLS_OVERFLOW       /* stop (larger sizes only get worse) */
};

/* Ground terms.  MACE4 operates on ground clauses, which are
   represented by the structure mclause.  Ground terms (and
   atoms) are represented with ordinary LADR terms.  There are
   a few tricks:

   (1) We use upward pointers from terms to superterms
   and from atoms to clauses.
 
   (2) We need to mark atoms with a termflag, so that we know
   when to stop when following the upward pointers.  Also,
   a termflag is used to indicate that an atom is negated.

   (3) Domain elements are represented by variables (sorry,
   but it is very convenient to do so).  Also, there is only
   one actual copy of each domain element (structure sharing
   of domain elements).  Global array *Domain contains them.

   IDs.  If all of the arguments of a term (including atoms) are
   domain elements, that term is called an eterm.  For example,
   f(3,4), a, P(0), and Q.

   Each eterm has a unique ID which is used as an index into
   the cell table, for example, when a new eterm is obtained by
   evaluating a subterm to a domain element, we have to quickly
   check if this new eterm can be evaluated.  We do this by
   calculating its ID and looking up in Cells[ID].value.
   And when we have a new assignment, say f(3,4)=2, we find the
   list of occurrences of f(3,4) by looking in Cells[ID].occurrences.
*/

/*************
 *
 *   init_mace_options()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_mace_options(Mace_options opt)
{
  opt->domain_size       = init_parm("domain_size",      0,       0, INT_MAX);
  opt->start_size        = init_parm("start_size",       2,       2, INT_MAX);
  opt->end_size          = init_parm("end_size",        -1,      -1, INT_MAX);
  opt->iterate_up_to     = init_parm("iterate_up_to",   -1,      -1, INT_MAX);
  opt->max_models        = init_parm("max_models",       1,      -1, INT_MAX);
  opt->max_seconds       = init_parm("max_seconds",     -1,      -1, INT_MAX);
  opt->max_seconds_per   = init_parm("max_seconds_per", -1,      -1, INT_MAX);
  opt->selection_order   = init_parm("selection_order",  2,       0, 2);
  opt->selection_measure = init_parm("selection_measure",4,       0, 4);
  opt->increment         = init_parm("increment",        1,       1, INT_MAX);
#ifdef __EMSCRIPTEN__
  opt->max_megs          = init_parm("max_megs",      2048,      -1, 4096);
#else
  opt->max_megs          = init_parm("max_megs",     49152,      -1, INT_MAX);
#endif
  opt->report_stderr     = init_parm("report_stderr",    60,      -1, INT_MAX);
         
  opt->print_models           = init_flag("print_models",           TRUE);
  opt->print_models_tabular   = init_flag("print_models_tabular",   FALSE);
  opt->lnh                    = init_flag("lnh",                    TRUE);
  opt->trace                  = init_flag("trace",                  FALSE);
  opt->negprop                = init_flag("negprop",                TRUE);
  opt->neg_assign             = init_flag("neg_assign",             TRUE);
  opt->neg_assign_near        = init_flag("neg_assign_near",        TRUE);
  opt->neg_elim               = init_flag("neg_elim",               TRUE);
  opt->neg_elim_near          = init_flag("neg_elim_near",          TRUE);
  opt->verbose                = init_flag("verbose",                FALSE);
  opt->integer_ring           = init_flag("integer_ring",           FALSE);
  opt->order_domain           = init_flag("order_domain",           FALSE);
  opt->arithmetic             = init_flag("arithmetic",             FALSE);
  opt->iterate_primes         = init_flag("iterate_primes",         FALSE);
  opt->iterate_nonprimes      = init_flag("iterate_nonprimes",      FALSE);
  opt->skolems_last           = init_flag("skolems_last",           FALSE);
  opt->return_models          = init_flag("return_models",          FALSE);

  opt->checkpoint_exit    = init_flag("checkpoint_exit", FALSE);
  opt->checkpoint_minutes = init_parm("checkpoint_minutes", -1, -1, INT_MAX);
  opt->checkpoint_keep    = init_parm("checkpoint_keep",     3,  1, 100);

  opt->iterate = init_stringparm("iterate", 5,
				 "all",
				 "evens",
				 "odds",
				 "primes",
				 "nonprimes");

  /* dependencies */

  flag_flag_dependency(opt->print_models_tabular,TRUE,opt->print_models,FALSE);
  flag_flag_dependency(opt->print_models,TRUE,opt->print_models_tabular,FALSE);

  flag_flag_dependency(opt->iterate_primes, TRUE,opt->iterate_nonprimes,FALSE);
  flag_flag_dependency(opt->iterate_nonprimes, TRUE,opt->iterate_primes,FALSE);

  parm_parm_dependency(opt->domain_size, opt->start_size, 1, TRUE);
  parm_parm_dependency(opt->domain_size, opt->end_size, 1, TRUE);

  parm_parm_dependency(opt->iterate_up_to, opt->end_size, 1, TRUE);

  flag_stringparm_dependency(opt->iterate_primes,TRUE,opt->iterate,"primes");
  flag_stringparm_dependency(opt->iterate_nonprimes,TRUE,opt->iterate,"nonprimes");

  flag_flag_dependency(opt->integer_ring, TRUE, opt->lnh, FALSE);
  flag_flag_dependency(opt->order_domain, TRUE, opt->lnh, FALSE);
  flag_flag_dependency(opt->arithmetic, TRUE, opt->lnh, FALSE);

  flag_parm_dependency(opt->arithmetic,TRUE,opt->selection_order,0);

}  /* init_mace_options */

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
  case MAX_MODELS_EXIT:   message = "max_models";    break;
  case ALL_MODELS_EXIT:   message = "all_models";    break;
  case EXHAUSTED_EXIT:    message = "exhausted";     break;
  case MAX_MEGS_YES_EXIT: message = "max_megs_yes";  break;
  case MAX_MEGS_NO_EXIT:  message = "max_megs_no" ;  break;
  case MAX_SEC_YES_EXIT:  message = "max_sec_yes";   break;
  case MAX_SEC_NO_EXIT:   message = "max_sec_no";    break;
  case MACE_SIGINT_EXIT:  message = "mace_sigint";   break;
  case MACE_SIGTERM_EXIT:      message = "mace_sigterm";      break;
  case MACE_SIGSEGV_EXIT:      message = "mace_sigsegv";      break;
  case MACE_CHECKPOINT_EXIT:   message = "mace_checkpoint";   break;
  default: message = "???";
  }
  return message;
}  /* exit_string */

/*************
 *
 *   mace4_szs_status()
 *
 *************/

static
char *mace4_szs_status(int exit_code)
{
  BOOL found = (exit_code == MAX_MODELS_EXIT ||
                exit_code == ALL_MODELS_EXIT ||
                exit_code == MAX_SEC_YES_EXIT ||
                exit_code == MAX_MEGS_YES_EXIT);

  if (found)
    return Mace4_has_goals ? "CounterSatisfiable" : "Satisfiable";

  switch (exit_code) {
  case EXHAUSTED_EXIT:       return "GaveUp";
  case MAX_SEC_NO_EXIT:      return "Timeout";
  case MAX_MEGS_NO_EXIT:     return "MemoryOut";
  case MACE_SIGINT_EXIT:     return "User";
  case MACE_SIGTERM_EXIT:    return "User";
  case MACE_SIGSEGV_EXIT:    return "Error";
  case MACE_CHECKPOINT_EXIT: return "User";  /* checkpoint is user-initiated */
  default:                   return "Error";
  }
}  /* mace4_szs_status */

/*************
 *
 *   mace4_exit()
 *
 *************/

void mace4_exit(int exit_code)
{
  if (Mace4_tptp_mode) {
    /* SZS status line */
    const char *szs = mace4_szs_status(exit_code);
    if (Mace4_problem_name)
      printf("\n%% SZS status %s for %s\n", szs, Mace4_problem_name);
    else
      printf("\n%% SZS status %s\n", szs);
    fflush(stdout);

    /* Print memory logging summary if logging was enabled */
    memory_logging_summary(stderr);

    exit(exit_code);
  }

  /* Native LADR output path */

  if (Opt && flag(Opt->verbose))
    p_mem();

  if (Opt && parm(Opt->report_stderr) > 0)
    fprintf(stderr, "Domain_size=%d. Models=%d. Selections=%u. CPU=%.2fs.\n",
	    Domain_size, Total_models, Mstats.selections, user_seconds());

  printf("\nUser_CPU=%.2f, System_CPU=%.2f, Wall_clock=%d.\n",
	 user_seconds(), system_seconds(), wallclock());

  if (Total_models == 0)
    printf("\nExiting with failure.\n");
  else
    printf("\nExiting with %d model%s.\n",
	    Total_models, Total_models == 1 ? "" : "s");

  fprintf(stderr, "\n------ process %d exit (%s) ------\n",
	  my_process_id(), exit_string(exit_code));
  printf("\nProcess %d exit (%s) %s",
	  my_process_id(), exit_string(exit_code), get_date());

  printf("The process finished %s", get_date());

  /* Print memory logging summary if logging was enabled */
  memory_logging_summary(stderr);

  exit(exit_code);
}  /* mace4_exit */

/*************
 *
 *   initialize_for_search()
 *
 *   This is the initialization that has to be done only once
 *   for a given set of clauses.  It is independent of the
 *   domain size.
 *
 *************/

static
void initialize_for_search(Plist clauses)
{
  int max, i;
  Symbol_data s;

  Mace4_clock = clock_init("Mace4");

  /* In ground clauses, VARIABLEs represent domain elements,
     so from here on, print variables as integers. */

  // set_variable_style(INTEGER_STYLE);

  /* These flags are for ground clause (mclause) literals. */

  Relation_flag = claim_term_flag();
  Negation_flag = claim_term_flag();

  /* Cache some symbol numbers. */

  Eq_sn  = str_to_sn(eq_sym(), 2);
  Or_sn  = str_to_sn(or_sym(), 2);
  Not_sn = str_to_sn(not_sym(), 1);

  /* Set up Symbols list. */

  init_built_in_symbols();  /* =/2 (and maybe others) */

  /* Maybe initialize for arithmetic. */

  if (flag(Opt->arithmetic))
    init_arithmetic();

  Skolems_last = flag(Opt->skolems_last);

  /* Collect data for each symbol. */

  Max_domain_element_in_input = -1;
  i = collect_mace4_syms(clauses, flag(Opt->arithmetic));
  Max_domain_element_in_input = MAX(Max_domain_element_in_input, i);

  if (!Mace4_tptp_mode) {
    if (Max_domain_element_in_input == -1)
      printf("\n%% There are no natural numbers in the input.\n");
    else
      printf("\n%% The largest natural number in the input is %d.\n",
             Max_domain_element_in_input);
  }

  /* Set up map from ordinary symnums to mace symnums. */

  max = 0;
  i = 0;

  for (s = Symbols; s != NULL; s = s->next) {
    s->mace_sn = i++;
    /* printf("mace symbol: %s/%d\n", sn_to_str(s->sn), sn_to_arity(s->sn)); */
    max = (s->sn > max ? s->sn : max);
  }

  Sn_map_size = max+1;

  Sn_to_mace_sn = safe_malloc(Sn_map_size * sizeof(void *));

  for (i = 0; i < Sn_map_size; i++)
    Sn_to_mace_sn[i] = NULL;

  for (s = Symbols; s != NULL; s = s->next) {
    Sn_to_mace_sn[s->sn] = s;
  }
}  /* initialize_for_search */

/*************
 *
 *   init_for_domain_size()
 *
 *   Given the list of (general) clauses, set up the various data
 *   structures that will be needed for a given domain size.
 *
 *************/

/* Returns TRUE on success, FALSE if cells overflow (domain too large). */
static
BOOL init_for_domain_size(void)
{
  int i, j, nextbase, id;
  Symbol_data s;

  /* Give each symbol its "base" value, which is used to index cells.  */

  nextbase = 0;
  for (s = Symbols; s != NULL; s = s->next) {
    int cells = int_power(Domain_size, s->arity);
    if (cells == INT_MAX || nextbase > INT_MAX - cells) {
      fprintf(stderr,
              "\n%% Mace4: too many cells for domain size %d "
              "(symbol %s/%d, arity too high)\n",
              Domain_size, sn_to_str(s->sn), s->arity);
      return FALSE;
    }
    s->base = nextbase;
    nextbase += cells;
  }

  /* Set up the array of domain terms.  All ground terms refer to these. */

  Domain = safe_malloc(Domain_size * sizeof(void *));
  for (i = 0; i < Domain_size; i++)
    Domain[i] = get_variable_term(i);
  
  /* Set up the table of cells. */

  Number_of_cells = nextbase;
  Cells           = safe_malloc(Number_of_cells * sizeof(struct cell));
  Ordered_cells   = safe_malloc(Number_of_cells * sizeof(void *));

  for (id = 0; id < Number_of_cells; id++) {
    struct cell *c = Cells + id;
    int n;
    c->id = id;
    c->occurrences = NULL;
    c->value = NULL;
    c->symbol = find_symbol_node(id);
    c->eterm = decode_eterm_id(id);
    c->max_index = max_index(id, c->symbol);
    n = id_to_domain_size(id);
    c->possible = safe_malloc(n * sizeof(void *));
    for (j = 0; j < n; j++)
      c->possible[j] = Domain[j];  /* really just a flag */
  }

  order_cells(flag(Opt->verbose));
  
  if (flag(Opt->negprop))
    init_negprop_index();
  return TRUE;
} /* init_for_domain_size */

/*************
 *
 *   built_in_assignments()
 *
 *************/

static
void built_in_assignments(void)
{
  Symbol_data s;
  for (s = Symbols; s != NULL; s = s->next) {
    if (s->attribute == EQUALITY_SYMBOL) {
      int i, j;
      for (i = 0; i < Domain_size; i++)
	for (j = 0; j < Domain_size; j++)
          Cells[X2(s->base,i,j)].value = (Domain[i==j ? 1 : 0]);
    }
  }
}  /* built_in_assignments */

/*************
 *
 *   special_assignments()
 *
 *************/

static
void special_assignments(void)
{
  if (flag(Opt->integer_ring)) {
    /* Fix [+,-,*] as the ring of integers mod domain_size. */
    /* If any of those operations doesn't exist, then ignore it.*/
    Symbol_data s;
    for (s = Symbols; s != NULL; s = s->next) {
      int i, j;
      if (is_symbol(s->sn, "+", 2)) {
	for (i = 0; i < Domain_size; i++)
	  for (j = 0; j < Domain_size; j++)
	    Cells[X2(s->base,i,j)].value = Domain[(i + j) % Domain_size];
      }
      else if (is_symbol(s->sn, "*", 2)) {
	for (i = 0; i < Domain_size; i++)
	  for (j = 0; j < Domain_size; j++)
	    Cells[X2(s->base,i,j)].value = Domain[(i * j) % Domain_size];
      }
      else if (is_symbol(s->sn, "-", 1)) {
	for (i = 0; i < Domain_size; i++)
	  Cells[X1(s->base,i)].value = Domain[(Domain_size - i) % Domain_size];
      }
      else if (is_symbol(s->sn, "--", 2)) {
	for (i = 0; i < Domain_size; i++)
	  for (j = 0; j < Domain_size; j++)
	    Cells[X2(s->base,i,j)].value = Domain[((i + Domain_size) - j) %
						  Domain_size];
      }
    }
  }
  if (flag(Opt->order_domain)) {
    Symbol_data s;
    for (s = Symbols; s != NULL; s = s->next) {
      int i, j;
      if (is_symbol(s->sn, "<", 2)) {
	for (i = 0; i < Domain_size; i++)
	  for (j = 0; j < Domain_size; j++)
	    Cells[X2(s->base,i,j)].value = (Domain[i<j ? 1 : 0]);
      }
      if (is_symbol(s->sn, "<=", 2)) {
	for (i = 0; i < Domain_size; i++)
	  for (j = 0; j < Domain_size; j++)
	    Cells[X2(s->base,i,j)].value = (Domain[i<=j ? 1 : 0]);
      }
    }
  }
}  /* special_assignments */

/*************
 *
 *   check_that_ground_clauses_are_true()
 *
 *************/

static
BOOL check_that_ground_clauses_are_true(void)
{
  Plist g;
  BOOL ok = TRUE;
  for (g = Ground_clauses; g != NULL; g = g->next) {
    Mclause c = g->v;
    if (!c->subsumed) {
      fprintf(stderr, "ERROR, model reported, but clause not true!\n");
      fprintf(stdout, "ERROR, model reported, but clause not true! ");
      p_mclause(c);
      ok = FALSE;
    }
  }
  return ok;
}  /* check_that_ground_clauses_are_true */

/*************
 *
 *   possible_model()
 *
 *************/

static
int possible_model(void)
{
  if (flag(Opt->arithmetic)) {
    if (!check_with_arithmetic(Ground_clauses))
      return SEARCH_GO_NO_MODELS;
  }
  else if (!check_that_ground_clauses_are_true())
    fatal_error("possible_model, bad model found");

  {
    static int next_message = 1;
    Total_models++;
    Mstats.current_models++;

    if (flag(Opt->return_models)) {
      Term modelterm = interp_term();
      Interp model = compile_interp(modelterm, FALSE);
      zap_term(modelterm);
      Models = plist_append(Models, model);
    }

    if (Mace4_tptp_mode && !Mace4_ladr_output)
      print_model_tptp(stdout);
    else if (flag(Opt->print_models))
      print_model_standard(stdout, !Mace4_ladr_output);
    else if (flag(Opt->print_models_tabular))
      p_model(FALSE);
    else if (next_message == Total_models) {
      printf("\nModel %d has been found.\n", Total_models);
      next_message *= 10;
    }
    fflush(stdout);
    if (parm(Opt->max_models) != -1 && Total_models >= parm(Opt->max_models))
      return SEARCH_MAX_MODELS;
    else
      return SEARCH_GO_MODELS;
  }
}  /* possible_model */

/*************
 *
 *   mace_megs()
 *
 *************/

static
int mace_megs(void)
{
  return (megs_malloced() - Start_megs) + (estack_bytes() / (1024*1024));
}  /* mace_megs */

/*************
 *
 *   check_time_memory()
 *
 *************/

static
int check_time_memory(void)
{
  static int Next_report;

  double seconds;
  int max_seconds;
  int max_seconds_per;
  int max_megs;
  int report;

#ifdef __EMSCRIPTEN__
  {
    double now_ms = emscripten_get_now();
    if (Wasm_deadline_ms > 0 && now_ms > Wasm_deadline_ms)
      return SEARCH_MAX_TOTAL_SECONDS;
    if (Wasm_domain_deadline_ms > 0 && now_ms > Wasm_domain_deadline_ms)
      return SEARCH_MAX_DOMAIN_SECONDS;
  }
#endif

  seconds = user_seconds();
  max_seconds = parm(Opt->max_seconds);
  max_seconds_per = parm(Opt->max_seconds_per);
  max_megs = parm(Opt->max_megs);
  report = parm(Opt->report_stderr);

  if (max_seconds != -1 && seconds - Start_seconds > max_seconds)
    return SEARCH_MAX_TOTAL_SECONDS;
  else if (max_seconds_per != -1 &&
	   seconds - Start_domain_seconds > parm(Opt->max_seconds_per))
    return SEARCH_MAX_DOMAIN_SECONDS;
  else if (max_megs != -1 && mace_megs() > parm(Opt->max_megs))
    return SEARCH_MAX_MEGS;
  else {
    if (report > 0) {
      if (Next_report == 0)
	Next_report = report;
      if (seconds >= Next_report) {
	if (Current_depth >= 0)
	  fprintf(stderr,
	    "Domain_size=%d. Models=%d. Selections=%u. Top=%d/%d. CPU=%.2fs.\n",
	    Domain_size, Total_models, Mstats.selections,
	    Search_stack[0].value_index, Search_stack[0].last + 1,
	    seconds);
	else
	  fprintf(stderr,
	    "Domain_size=%d. Models=%d. Selections=%u. CPU=%.2fs.\n",
	    Domain_size, Total_models, Mstats.selections, seconds);
	fflush(stderr);
	while (seconds >= Next_report)
	  Next_report += report;
      }
    }
    return SEARCH_GO_NO_MODELS;
  }
}  /* check_time_memory */

/*************
 *
 *   mace4_skolem_check()
 *
 *************/

static
BOOL mace4_skolem_check(int id)
{
  /* Should we keep going w.r.t. the Skolem restriction? */
  if (!flag(Opt->skolems_last))
    return TRUE;
  else if (Cells[id].symbol->attribute == SKOLEM_SYMBOL) {
    printf("pruning\n");
    return FALSE;
  }
  else
    return TRUE;
}  /* mace4_skolem_check */

/*************
 *
 *   p_possible_values()
 *
 *************/

#if 0
static
void p_possible_values(void)
{
  int i;
  for (i = 0; i < Number_of_cells; i++) {
    if (Cells[i].symbol->attribute == ORDINARY_SYMBOL) {
      int j;
      printf("Cell %d: ", i);
      for (j = 0; j < id_to_domain_size(i); j++) {
	if (Cells[i].possible[j] != NULL)
	  printf(" %d", j);
      }
      printf("\n");
    }
  }
}  /* p_possible_values */
#endif

/* search() -- original recursive version, replaced by search_iterative().
   Kept as comment for reference.
*/

/*************
 *
 *   ensure_stack_capacity()
 *
 *************/

static
void ensure_stack_capacity(int needed)
{
  if (needed > Search_stack_capacity) {
    int new_cap = Search_stack_capacity * 2;
    struct search_frame *new_stack;
    if (new_cap < 256)
      new_cap = 256;
    if (needed > new_cap)
      new_cap = needed;
    new_stack = (struct search_frame *)
      safe_malloc(new_cap * sizeof(struct search_frame));
    if (Search_stack != NULL) {
      memcpy(new_stack, Search_stack,
             Search_stack_capacity * sizeof(struct search_frame));
      safe_free(Search_stack);
    }
    Search_stack = new_stack;
    Search_stack_capacity = new_cap;
  }
}  /* ensure_stack_capacity */

/*************
 *
 *   search_iterative()
 *
 *   Iterative version of search().  Produces identical behavior to
 *   the recursive version.  The explicit stack enables checkpointing.
 *
 *   Returns: SEARCH_GO_MODELS, SEARCH_GO_NO_MODELS, SEARCH_MAX_MODELS,
 *            SEARCH_MAX_MEGS, SEARCH_MAX_TOTAL_SECONDS,
 *            SEARCH_MAX_DOMAIN_SECONDS
 *
 *************/

static
int search_iterative(int initial_max_constrained)
{
  int depth;
  int rc;
  int id;
  int x, last, mc;
  struct search_frame *frame;

  /* Set up initial frame */
  ensure_stack_capacity(1);

  rc = check_time_memory();
  if (rc != SEARCH_GO_NO_MODELS)
    return rc;

  id = select_cell(initial_max_constrained);
  if (id == -1)
    return possible_model();

  x = Cells[id].max_index;
  mc = MAX(initial_max_constrained, x);
  Mstats.selections++;

  if (Cells[id].symbol->type == RELATION)
    last = 1;
  else if (flag(Opt->lnh))
    last = MIN(mc + 1, Domain_size - 1);
  else
    last = Domain_size - 1;

  Search_stack[0].cell_id = id;
  Search_stack[0].value_index = 0;
  Search_stack[0].last = last;
  Search_stack[0].max_constrained = mc;
  Search_stack[0].stk = NULL;

  depth = 0;
  rc = SEARCH_GO_NO_MODELS;

  while (depth >= 0) {
    Current_depth = depth;
    frame = &Search_stack[depth];

    /* --- Checkpoint check --- */
    if (mace4_checkpoint_requested()) {
      write_mace4_checkpoint(Saved_clauses);
      mace4_clear_checkpoint_request();
      if (flag(Opt->checkpoint_exit)) {
        /* Unwind all estacks before returning */
        int d;
        for (d = depth; d >= 0; d--) {
          if (Search_stack[d].stk != NULL) {
            restore_from_stack(Search_stack[d].stk);
            Search_stack[d].stk = NULL;
          }
        }
        Current_depth = -1;
        return SEARCH_MAX_MODELS + 100;  /* sentinel: handled in mace4n */
      }
    }

    /* --- Periodic checkpoint check --- */
    if (parm(Opt->checkpoint_minutes) > 0) {
      time_t now = time(NULL);
      if (Last_auto_ckpt_time == 0)
        Last_auto_ckpt_time = now;
      if (now - Last_auto_ckpt_time >=
          (time_t)parm(Opt->checkpoint_minutes) * 60) {
        fprintf(stderr,
                "\nPeriodic checkpoint at selections=%u...\n",
                Mstats.selections);
        write_mace4_checkpoint(Saved_clauses);
        Last_auto_ckpt_time = now;
      }
    }

    /* --- Time/memory check --- */
    {
      int tmrc = check_time_memory();
      if (tmrc != SEARCH_GO_NO_MODELS) {
        /* Unwind all estacks */
        int d;
        for (d = depth; d >= 0; d--) {
          if (Search_stack[d].stk != NULL) {
            restore_from_stack(Search_stack[d].stk);
            Search_stack[d].stk = NULL;
          }
        }
        Current_depth = -1;
        return tmrc;
      }
    }

    /* --- Frame exhausted (tried all values)? --- */
    if (frame->value_index > frame->last) {
      if (depth == 0) {
        Current_depth = -1;
        return rc;
      }
      /* Pop: undo the parent's assignment */
      depth--;
      if (Search_stack[depth].stk != NULL) {
        restore_from_stack(Search_stack[depth].stk);
        Search_stack[depth].stk = NULL;
      }
      /* Propagate rc to parent */
      if (rc == SEARCH_GO_MODELS) {
        if (!mace4_skolem_check(Search_stack[depth].cell_id))
          Search_stack[depth].value_index = Search_stack[depth].last + 1;
        else
          Search_stack[depth].value_index++;
      }
      else if (rc == SEARCH_GO_NO_MODELS)
        Search_stack[depth].value_index++;
      else
        Search_stack[depth].value_index = Search_stack[depth].last + 1;
      continue;
    }

    /* --- Try current value --- */
    if (flag(Opt->trace)) {
      printf("assign: ");
      fwrite_term(stdout, Cells[frame->cell_id].eterm);
      printf("=%d (%d) depth=%d\n",
             frame->value_index, frame->last, depth);
    }

    Mstats.assignments++;
    {
      Estack stk = assign_and_propagate(frame->cell_id,
                                         Domain[frame->value_index]);
      if (stk != NULL) {
        int new_mc, new_id, new_last;
        frame->stk = stk;

        /* Push new frame */
        new_mc = MAX(frame->max_constrained, frame->value_index);
        depth++;
        ensure_stack_capacity(depth + 1);

        /* check_time_memory at new depth */
        rc = check_time_memory();
        if (rc != SEARCH_GO_NO_MODELS) {
          /* Unwind */
          int d;
          depth--;
          for (d = depth; d >= 0; d--) {
            if (Search_stack[d].stk != NULL) {
              restore_from_stack(Search_stack[d].stk);
              Search_stack[d].stk = NULL;
            }
          }
          Current_depth = -1;
          return rc;
        }

        new_id = select_cell(new_mc);
        if (new_id == -1) {
          /* All cells assigned -- possible model */
          rc = possible_model();
          /* Pop back: undo the assignment we just made */
          depth--;
          if (Search_stack[depth].stk != NULL) {
            restore_from_stack(Search_stack[depth].stk);
            Search_stack[depth].stk = NULL;
          }
          /* Propagate rc */
          if (rc == SEARCH_GO_MODELS) {
            if (!mace4_skolem_check(Search_stack[depth].cell_id))
              Search_stack[depth].value_index = Search_stack[depth].last + 1;
            else
              Search_stack[depth].value_index++;
          }
          else if (rc == SEARCH_GO_NO_MODELS)
            Search_stack[depth].value_index++;
          else
            Search_stack[depth].value_index = Search_stack[depth].last + 1;
        }
        else {
          /* New cell selected at new depth */
          x = Cells[new_id].max_index;
          new_mc = MAX(new_mc, x);
          Mstats.selections++;

          if (flag(Opt->trace)) {
            printf("select: ");
            p_model(FALSE);
          }

          if (Cells[new_id].symbol->type == RELATION)
            new_last = 1;
          else if (flag(Opt->lnh))
            new_last = MIN(new_mc + 1, Domain_size - 1);
          else
            new_last = Domain_size - 1;

          Search_stack[depth].cell_id = new_id;
          Search_stack[depth].value_index = 0;
          Search_stack[depth].last = new_last;
          Search_stack[depth].max_constrained = new_mc;
          Search_stack[depth].stk = NULL;
        }
      }
      else {
        /* Contradiction during propagation, try next value */
        frame->value_index++;
      }
    }
  }

  Current_depth = -1;
  return rc;
}  /* search_iterative */

/*************
 *
 *   search_iterative_resume()
 *
 *   Continue iterative search from a resumed position.
 *   The search stack is already set up with depths 0..start_depth.
 *   Depths 0..start_depth-1 have live estacks from replay.
 *   Depth start_depth is the leaf frame where search continues.
 *
 *************/

static
int search_iterative_resume(int start_depth)
{
  int depth;
  int rc;
  struct search_frame *frame;

  depth = start_depth;
  rc = SEARCH_GO_NO_MODELS;

  /* The while loop is identical to search_iterative's main loop */
  while (depth >= 0) {
    int x;
    Current_depth = depth;
    frame = &Search_stack[depth];

    /* --- Checkpoint check --- */
    if (mace4_checkpoint_requested()) {
      write_mace4_checkpoint(Saved_clauses);
      mace4_clear_checkpoint_request();
      if (flag(Opt->checkpoint_exit)) {
        int d;
        for (d = depth; d >= 0; d--) {
          if (Search_stack[d].stk != NULL) {
            restore_from_stack(Search_stack[d].stk);
            Search_stack[d].stk = NULL;
          }
        }
        Current_depth = -1;
        return SEARCH_MAX_MODELS + 100;
      }
    }

    /* --- Periodic checkpoint check --- */
    if (parm(Opt->checkpoint_minutes) > 0) {
      time_t now = time(NULL);
      if (Last_auto_ckpt_time == 0)
        Last_auto_ckpt_time = now;
      if (now - Last_auto_ckpt_time >=
          (time_t)parm(Opt->checkpoint_minutes) * 60) {
        fprintf(stderr,
                "\nPeriodic checkpoint at selections=%u...\n",
                Mstats.selections);
        write_mace4_checkpoint(Saved_clauses);
        Last_auto_ckpt_time = now;
      }
    }

    /* --- Time/memory check --- */
    rc = check_time_memory();
    if (rc != SEARCH_GO_NO_MODELS) {
      int d;
      for (d = depth; d >= 0; d--) {
        if (Search_stack[d].stk != NULL) {
          restore_from_stack(Search_stack[d].stk);
          Search_stack[d].stk = NULL;
        }
      }
      Current_depth = -1;
      return rc;
    }

    /* --- Frame exhausted? --- */
    if (frame->value_index > frame->last) {
      if (depth == 0) {
        Current_depth = -1;
        return rc;
      }
      depth--;
      if (Search_stack[depth].stk != NULL) {
        restore_from_stack(Search_stack[depth].stk);
        Search_stack[depth].stk = NULL;
      }
      if (rc == SEARCH_GO_MODELS) {
        if (!mace4_skolem_check(Search_stack[depth].cell_id))
          Search_stack[depth].value_index = Search_stack[depth].last + 1;
        else
          Search_stack[depth].value_index++;
      }
      else if (rc == SEARCH_GO_NO_MODELS)
        Search_stack[depth].value_index++;
      else
        Search_stack[depth].value_index = Search_stack[depth].last + 1;
      continue;
    }

    /* --- Try current value --- */
    if (flag(Opt->trace)) {
      printf("assign: ");
      fwrite_term(stdout, Cells[frame->cell_id].eterm);
      printf("=%d (%d) depth=%d\n",
             frame->value_index, frame->last, depth);
    }

    Mstats.assignments++;
    {
      Estack stk = assign_and_propagate(frame->cell_id,
                                         Domain[frame->value_index]);
      if (stk != NULL) {
        int new_mc, new_id, new_last;
        frame->stk = stk;

        new_mc = MAX(frame->max_constrained, frame->value_index);
        depth++;
        ensure_stack_capacity(depth + 1);

        rc = check_time_memory();
        if (rc != SEARCH_GO_NO_MODELS) {
          int d;
          depth--;
          for (d = depth; d >= 0; d--) {
            if (Search_stack[d].stk != NULL) {
              restore_from_stack(Search_stack[d].stk);
              Search_stack[d].stk = NULL;
            }
          }
          Current_depth = -1;
          return rc;
        }

        new_id = select_cell(new_mc);
        if (new_id == -1) {
          rc = possible_model();
          depth--;
          if (Search_stack[depth].stk != NULL) {
            restore_from_stack(Search_stack[depth].stk);
            Search_stack[depth].stk = NULL;
          }
          if (rc == SEARCH_GO_MODELS) {
            if (!mace4_skolem_check(Search_stack[depth].cell_id))
              Search_stack[depth].value_index = Search_stack[depth].last + 1;
            else
              Search_stack[depth].value_index++;
          }
          else if (rc == SEARCH_GO_NO_MODELS)
            Search_stack[depth].value_index++;
          else
            Search_stack[depth].value_index = Search_stack[depth].last + 1;
        }
        else {
          x = Cells[new_id].max_index;
          new_mc = MAX(new_mc, x);
          Mstats.selections++;

          if (flag(Opt->trace)) {
            printf("select: ");
            p_model(FALSE);
          }

          if (Cells[new_id].symbol->type == RELATION)
            new_last = 1;
          else if (flag(Opt->lnh))
            new_last = MIN(new_mc + 1, Domain_size - 1);
          else
            new_last = Domain_size - 1;

          Search_stack[depth].cell_id = new_id;
          Search_stack[depth].value_index = 0;
          Search_stack[depth].last = new_last;
          Search_stack[depth].max_constrained = new_mc;
          Search_stack[depth].stk = NULL;
        }
      }
      else {
        frame->value_index++;
      }
    }
  }

  Current_depth = -1;
  return rc;
}  /* search_iterative_resume */

/*************
 *
 *   mace4n() -- look for a model of a specific size
 *
 *************/

static
int mace4n(Plist clauses, int order)
{
  Plist p, g;
  int i, rc;
  Mstate initial_state = get_mstate();

  Variable_style save_style = variable_style();
  set_variable_style(INTEGER_STYLE);

  if (Max_domain_element_in_input >= order) {
    if (flag(Opt->arithmetic)) {
      if (!ok_for_arithmetic(clauses, order))
	return SEARCH_DOMAIN_OUT_OF_RANGE;
    }
    else
      return SEARCH_DOMAIN_OUT_OF_RANGE;
  }

  Domain_size = order;

  if (!init_for_domain_size())
    return SEARCH_CELLS_OVERFLOW;  /* cells overflow — stop iterating */

  built_in_assignments();  /* Fill out equality table (and maybe others). */

  special_assignments();  /* assignments determined by options */

  /* Instantiate clauses over the domain.  This also 
     (1) makes any domain element constants into real domain elements,
     (2) applies OR, NOT, and EQ simplification, and
     (3) does unit propagation (which pushes events onto initial_state->stack).
     Do the units first, then the 2-clauses, then the rest. */

  for (p = clauses; initial_state->ok && p != NULL; p = p->next)
    if (number_of_literals(p->v) < 2)
      generate_ground_clauses(p->v, initial_state);

  for (p = clauses; initial_state->ok && p != NULL; p = p->next)
    if (number_of_literals(p->v) == 2)
      generate_ground_clauses(p->v, initial_state);

  for (p = clauses; initial_state->ok && p != NULL; p = p->next)
    if (number_of_literals(p->v) > 2)
      generate_ground_clauses(p->v, initial_state);

  /* The preceding calls push propagation events onto initial_state->stack.
     We won't have to undo those initial events during the search,
     but we can undo them after the search.
  */

  if (flag(Opt->verbose)) {
    printf("\nInitial partial model:\n");
    p_model(FALSE);
    fflush(stdout);
  }

  /* Here we go! */

  if (initial_state->ok)
    rc = search_iterative(Max_domain_element_in_input);
  else
    rc = SEARCH_GO_NO_MODELS;  /* contradiction in initial state */

  /* Handle checkpoint exit sentinel */
  if (rc == SEARCH_MAX_MODELS + 100)
    rc = SEARCH_MAX_MODELS + 100;  /* propagated to mace4() */

  /* Free all of the memory associated with the current domain size. */

  restore_from_stack(initial_state->stack);
  free_mstate(initial_state);

  if (flag(Opt->negprop))
    free_negprop_index();

  safe_free(Ordered_cells);
  Ordered_cells = NULL;

  for (i = 0; i < Number_of_cells; i++) {
    zap_mterm(Cells[i].eterm);
    safe_free(Cells[i].possible);
  }
  safe_free(Cells);
  Cells = NULL;

  for (i = 0; i < Domain_size; i++)
    zap_term(Domain[i]);
  safe_free(Domain);
  Domain = NULL;

  for (g = Ground_clauses; g != NULL; g = g->next)
    zap_mclause(g->v);
  zap_plist(Ground_clauses);
  Ground_clauses = NULL;

  set_variable_style(save_style);
  return rc;
}  /* mace4n */

/*************
 *
 *   iterate_ok()
 *
 *************/

static
BOOL iterate_ok(int n, char *class)
{
  if (str_ident(class, "all"))
    return TRUE;
  else if (str_ident(class, "evens"))
    return n % 2 == 0;
  else if (str_ident(class, "odds"))
    return n % 2 == 1;
  else if (str_ident(class, "primes"))
    return prime(n);
  else if (str_ident(class, "nonprimes"))
    return !prime(n);
  else {
    fatal_error("iterate_ok, unknown class");
    return FALSE;   /* to please compiler */
  }
}  /* iterate_ok */

/*************
 *
 *   next_domain_size()
 *
 *************/

static
int next_domain_size(int n)
{
  int top = (parm(Opt->end_size) == -1 ? INT_MAX : parm(Opt->end_size));
      
  if (n == 0)
    n = parm(Opt->start_size);  /* first call */
  else
    n += parm(Opt->increment);

  while (!iterate_ok(n, stringparm1(Opt->iterate))) {
    n += parm(Opt->increment);
    if (n > top)
      return -1;
  }

  return (n > top ? -1 : n);
}  /* next_domain_size */

/*************
 *
 *   mace4()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Mace_results mace4(Plist clauses, Mace_options opt)
{
  int n, rc;
  Mace_results results = safe_malloc(sizeof(struct mace_results));

  disable_max_megs();  /* mace4 does its own max_megs check */
  Start_seconds = user_seconds();
  Start_megs = megs_malloced();

#ifdef __EMSCRIPTEN__
  /* Set WASM total timeout deadline */
  {
    int max_sec = parm(opt->max_seconds);
    if (max_sec > 0)
      Wasm_deadline_ms = emscripten_get_now() + max_sec * 1000.0;
    else
      Wasm_deadline_ms = 0;
  }
#endif

  Opt = opt;  /* put options into a global variable */
  Saved_clauses = clauses;  /* save for checkpoint */
  initialize_for_search(clauses);

  if (Resuming) {
    /* Resume path: skip to saved domain size */
    Total_models = Saved_total_models;
    n = Saved_domain_size;
  }
  else {
    n = next_domain_size(0);  /* returns -1 if we're done */
  }
  rc = SEARCH_GO_NO_MODELS;

  while (n >= 2 && (rc == SEARCH_GO_NO_MODELS || rc == SEARCH_GO_MODELS)) {
    if (!Mace4_tptp_mode) {
      char str[24];
      sprintf(str, "DOMAIN SIZE %d", n);
      print_separator(stdout, str, TRUE);
      fflush(stdout);
      fprintf(stderr,"\n=== Mace4 starting on domain size %d. ===\n",n);
    }
    else {
      fprintf(stderr,"\n%% Mace4 starting on domain size %d.\n",n);
    }

    Start_domain_seconds = user_seconds();
#ifdef __EMSCRIPTEN__
    {
      int max_sec_per = parm(opt->max_seconds_per);
      if (max_sec_per > 0)
        Wasm_domain_deadline_ms = emscripten_get_now() + max_sec_per * 1000.0;
      else
        Wasm_domain_deadline_ms = 0;
    }
#endif
    clock_start(Mace4_clock);

    if (Resuming) {
      Resuming = FALSE;  /* only the first domain size is resumed */
      rc = mace4n_resume(clauses, n, Saved_trail, Saved_trail_depth);
    }
    else {
      rc = mace4n(clauses, n);
    }

    /* Handle checkpoint exit sentinel */
    if (rc == SEARCH_MAX_MODELS + 100) {
      clock_stop(Mace4_clock);
      /* Free search stack */
      if (Search_stack) {
        safe_free(Search_stack);
        Search_stack = NULL;
      }
      Search_stack_capacity = 0;
      /* free memory used for all domain sizes */
      free_estack_memory();
      safe_free(Sn_to_mace_sn);
      Sn_to_mace_sn = NULL;

      results->success = Total_models != 0;
      results->models = Models;
      results->user_seconds = user_seconds() - Start_seconds;
      results->return_code = MACE_CHECKPOINT_EXIT;
      enable_max_megs();
      return results;
    }

    if (rc == SEARCH_MAX_DOMAIN_SECONDS) {
      if (!Mace4_tptp_mode)
        printf("\n====== Domain size %d terminated by max_seconds_per. ======\n",n);
      rc = SEARCH_GO_NO_MODELS;
    }
    else if (rc == SEARCH_DOMAIN_OUT_OF_RANGE) {
      if (!Mace4_tptp_mode)
        printf("\n====== Domain size %d skipped because domain element too big. ======\n",n);
      rc = SEARCH_GO_NO_MODELS;
    }
    else if (rc == SEARCH_CELLS_OVERFLOW) {
      /* Cell count overflows at this domain size.  Larger sizes only
         make it worse (cells = domain_size^arity), so stop iterating. */
      if (!Mace4_tptp_mode)
        printf("\n====== Domain size %d: too many cells. Stopping. ======\n",n);
      break;
    }
    clock_stop(Mace4_clock);
    if (!Mace4_tptp_mode)
      p_stats();
    reset_current_stats();
    clock_reset(Mace4_clock);

    /* Check for checkpoint signal between domain sizes.
       Domain_size is set to the size we just finished; next_domain_size()
       will determine the next one. Write checkpoint with empty trail
       and the NEXT domain size (so resume starts there). */
    if (mace4_checkpoint_requested()) {
      int next_n = next_domain_size(n);
      Domain_size = (next_n >= 2) ? next_n : n;
      write_mace4_checkpoint(clauses);
      mace4_clear_checkpoint_request();
      if (flag(Opt->checkpoint_exit)) {
        /* Free search stack */
        if (Search_stack) {
          safe_free(Search_stack);
          Search_stack = NULL;
        }
        Search_stack_capacity = 0;
        free_estack_memory();
        safe_free(Sn_to_mace_sn);
        Sn_to_mace_sn = NULL;
        results->success = Total_models != 0;
        results->models = Models;
        results->user_seconds = user_seconds() - Start_seconds;
        results->return_code = MACE_CHECKPOINT_EXIT;
        enable_max_megs();
        return results;
      }
    }

    n = next_domain_size(n);  /* returns -1 if we're done */
  }

  /* Free search stack */
  if (Search_stack) {
    safe_free(Search_stack);
    Search_stack = NULL;
  }
  Search_stack_capacity = 0;

  /* free memory used for all domain sizes */
  free_estack_memory();
  safe_free(Sn_to_mace_sn);
  Sn_to_mace_sn = NULL;

  results->success = Total_models != 0;
  results->models = Models;  /* NULL if no models or not collecting models */
  results->user_seconds = user_seconds() - Start_seconds;

  if (rc == SEARCH_MAX_MODELS)
    results->return_code = MAX_MODELS_EXIT;
  else if (rc == SEARCH_GO_MODELS || rc == SEARCH_GO_NO_MODELS)
    results->return_code = Total_models==0 ? EXHAUSTED_EXIT : ALL_MODELS_EXIT;
  else if (rc == SEARCH_MAX_TOTAL_SECONDS)
    results->return_code = Total_models==0 ? MAX_SEC_NO_EXIT : MAX_SEC_YES_EXIT;
  else if (rc == SEARCH_MAX_MEGS)
    results->return_code = Total_models==0 ? MAX_MEGS_NO_EXIT : MAX_MEGS_YES_EXIT;
  else if (rc == SEARCH_CELLS_OVERFLOW)
    results->return_code = Total_models==0 ? EXHAUSTED_EXIT : ALL_MODELS_EXIT;
  else
    fatal_error("mace4: unknown return code");

  enable_max_megs();
  return results;
}  /* mace4 */

/*************
 *
 *   mace4_checkpoint_requested()
 *
 *************/

BOOL mace4_checkpoint_requested(void)
{
  /* Set from signal handler in mace4.c */
#ifndef __EMSCRIPTEN__
  extern volatile sig_atomic_t Mace4_checkpoint_requested_flag;
#else
  extern int Mace4_checkpoint_requested_flag;
#endif
  return Mace4_checkpoint_requested_flag != 0;
}  /* mace4_checkpoint_requested */

/*************
 *
 *   mace4_clear_checkpoint_request()
 *
 *************/

void mace4_clear_checkpoint_request(void)
{
#ifndef __EMSCRIPTEN__
  extern volatile sig_atomic_t Mace4_checkpoint_requested_flag;
#else
  extern int Mace4_checkpoint_requested_flag;
#endif
  Mace4_checkpoint_requested_flag = 0;
}  /* mace4_clear_checkpoint_request */

/*************
 *
 *   remove_checkpoint_dir()
 *
 *************/

#ifndef __EMSCRIPTEN__
static
void remove_checkpoint_dir(const char *dir)
{
  char cmd[1024];
  int rc;
  sprintf(cmd, "rm -rf %s", dir);
  rc = system(cmd);
  (void) rc;
}  /* remove_checkpoint_dir */
#endif

/*************
 *
 *   record_auto_checkpoint()
 *
 *************/

#ifndef __EMSCRIPTEN__
static
void record_auto_checkpoint(const char *dir)
{
  int keep = parm(Opt->checkpoint_keep);
  char *copy = (char *) safe_malloc(strlen(dir) + 1);
  strcpy(copy, dir);

  if (Auto_ckpt_count < keep) {
    Auto_ckpt_dirs[Auto_ckpt_count] = copy;
    Auto_ckpt_count++;
  }
  else {
    /* Remove oldest, replace in circular buffer */
    int idx = Auto_ckpt_head;
    if (Auto_ckpt_dirs[idx] != NULL) {
      fprintf(stderr, "Removing old checkpoint: %s\n", Auto_ckpt_dirs[idx]);
      remove_checkpoint_dir(Auto_ckpt_dirs[idx]);
      safe_free(Auto_ckpt_dirs[idx]);
    }
    Auto_ckpt_dirs[idx] = copy;
    Auto_ckpt_head = (Auto_ckpt_head + 1) % keep;
  }
}  /* record_auto_checkpoint */
#endif

/*************
 *
 *   write_mace4_checkpoint()
 *
 *************/

#ifdef __EMSCRIPTEN__
void write_mace4_checkpoint(Plist clauses)
{
  (void) clauses;
}
#else
void write_mace4_checkpoint(Plist clauses)
{
  char dir_name[256];
  char tmp_name[264];
  char path[512];
  FILE *fp;
  int d;
  int depth;

  /* Current_depth is maintained by the search loops (set to depth
     during active search, -1 between searches).  Add 1 to include
     the leaf frame currently being explored. */
  depth = (Current_depth >= 0) ? Current_depth + 1 : 0;

  sprintf(dir_name, "mace4_%d_ckpt_%u", my_process_id(), Mstats.selections);
  sprintf(tmp_name, "%s.tmp", dir_name);

  /* Create temp directory */
  if (mkdir(tmp_name, 0755) != 0) {
    fprintf(stderr, "WARNING: cannot create checkpoint dir %s: %s\n",
            tmp_name, strerror(errno));
    return;
  }

  /* --- metadata.txt --- */
  sprintf(path, "%s/metadata.txt", tmp_name);
  fp = fopen(path, "w");
  if (fp == NULL) {
    fprintf(stderr, "WARNING: cannot write %s\n", path);
    return;
  }
  fprintf(fp, "version mace4\n");
  fprintf(fp, "tptp_mode %d\n", Mace4_tptp_mode ? 1 : 0);
  fprintf(fp, "domain_size %d\n", Domain_size);
  fprintf(fp, "total_models %u\n", Total_models);
  fprintf(fp, "start_seconds %.2f\n", Start_seconds);
  fprintf(fp, "start_megs %lld\n", Start_megs);
  fprintf(fp, "selections %u\n", Mstats.selections);
  fprintf(fp, "assignments %u\n", Mstats.assignments);
  fprintf(fp, "propagations %u\n", Mstats.propagations);
  fprintf(fp, "cross_offs %u\n", Mstats.cross_offs);
  fprintf(fp, "ground_clauses_seen %u\n", Mstats.ground_clauses_seen);
  fprintf(fp, "ground_clauses_kept %u\n", Mstats.ground_clauses_kept);
  fprintf(fp, "search_depth %d\n", depth);
  fclose(fp);

  /* --- trail.txt --- */
  sprintf(path, "%s/trail.txt", tmp_name);
  fp = fopen(path, "w");
  if (fp == NULL) {
    fprintf(stderr, "WARNING: cannot write %s\n", path);
    return;
  }
  for (d = 0; d < depth; d++) {
    fprintf(fp, "%d %d %d %d %d\n",
            d,
            Search_stack[d].cell_id,
            Search_stack[d].value_index,
            Search_stack[d].last,
            Search_stack[d].max_constrained);
  }
  fclose(fp);

  /* --- saved_input.txt --- */
  sprintf(path, "%s/saved_input.txt", tmp_name);
  fp = fopen(path, "w");
  if (fp == NULL) {
    fprintf(stderr, "WARNING: cannot write %s\n", path);
    return;
  }
  fprintf(fp, "set(ignore_option_dependencies).\n\n");
  fwrite_options_input(fp);
  fprintf(fp, "\n");
  if (clauses != NULL) {
    /* Switch to standard variable style for clause output */
    Variable_style save_vstyle = variable_style();
    set_variable_style(STANDARD_STYLE);
    fwrite_clause_list(fp, clauses, "mace4_clauses", CL_FORM_BARE);
    set_variable_style(save_vstyle);
  }
  fclose(fp);

  /* --- options.txt (human-readable, not used on resume) --- */
  sprintf(path, "%s/options.txt", tmp_name);
  fp = fopen(path, "w");
  if (fp != NULL) {
    fprint_options(fp);
    fclose(fp);
  }

  /* Atomic rename */
  if (rename(tmp_name, dir_name) != 0) {
    fprintf(stderr, "WARNING: cannot rename %s to %s: %s\n",
            tmp_name, dir_name, strerror(errno));
    return;
  }

  fprintf(stderr, "Checkpoint written: %s (depth=%d, selections=%u)\n",
          dir_name, depth, Mstats.selections);

  /* Record for auto-rotation if this is a periodic checkpoint */
  if (parm(Opt->checkpoint_minutes) > 0 &&
      !mace4_checkpoint_requested()) {
    record_auto_checkpoint(dir_name);
  }
}  /* write_mace4_checkpoint */
#endif /* !__EMSCRIPTEN__ */

/*************
 *
 *   mace4n_resume()
 *
 *   Resume search from a checkpoint.  The saved_trail contains
 *   the decision trail from the checkpoint.  We rebuild the
 *   domain-size structures, replay the trail, then continue search.
 *
 *************/

int mace4n_resume(Plist clauses, int order,
                  struct search_frame *saved_trail, int saved_depth)
{
  Plist p, g;
  int i, d, rc;
  Mstate initial_state = get_mstate();
  Variable_style save_style = variable_style();
  set_variable_style(INTEGER_STYLE);

  if (Max_domain_element_in_input >= order) {
    if (flag(Opt->arithmetic)) {
      if (!ok_for_arithmetic(clauses, order))
        return SEARCH_DOMAIN_OUT_OF_RANGE;
    }
    else
      return SEARCH_DOMAIN_OUT_OF_RANGE;
  }

  Domain_size = order;
  if (!init_for_domain_size())
    return SEARCH_CELLS_OVERFLOW;
  built_in_assignments();
  special_assignments();

  for (p = clauses; initial_state->ok && p != NULL; p = p->next)
    if (number_of_literals(p->v) < 2)
      generate_ground_clauses(p->v, initial_state);

  for (p = clauses; initial_state->ok && p != NULL; p = p->next)
    if (number_of_literals(p->v) == 2)
      generate_ground_clauses(p->v, initial_state);

  for (p = clauses; initial_state->ok && p != NULL; p = p->next)
    if (number_of_literals(p->v) > 2)
      generate_ground_clauses(p->v, initial_state);

  if (!initial_state->ok) {
    fatal_error("mace4 resume: contradiction during initial state rebuild");
  }

  /* === REPLAY THE DECISION TRAIL === */
  ensure_stack_capacity(saved_depth + 1);

  /* Replay depths 0 .. saved_depth-2: these are assignments in effect */
  for (d = 0; d < saved_depth - 1; d++) {
    int id = saved_trail[d].cell_id;
    int val = saved_trail[d].value_index;
    Estack stk;

    stk = assign_and_propagate(id, Domain[val]);
    if (stk == NULL)
      fatal_error("mace4 resume: contradiction during trail replay");

    Search_stack[d].cell_id = id;
    Search_stack[d].value_index = val;
    Search_stack[d].last = saved_trail[d].last;
    Search_stack[d].max_constrained = saved_trail[d].max_constrained;
    Search_stack[d].stk = stk;
    Mstats.assignments++;
  }

  /* Set up the leaf frame (where search continues) */
  if (saved_depth > 0) {
    d = saved_depth - 1;
    Search_stack[d].cell_id = saved_trail[d].cell_id;
    Search_stack[d].value_index = saved_trail[d].value_index;
    Search_stack[d].last = saved_trail[d].last;
    Search_stack[d].max_constrained = saved_trail[d].max_constrained;
    Search_stack[d].stk = NULL;  /* not yet assigned */
  }

  fprintf(stderr, "Trail replay complete: %d depths replayed\n", saved_depth);

  /* Continue search from the leaf frame */
  if (saved_depth > 0)
    rc = search_iterative_resume(saved_depth - 1);
  else
    rc = search_iterative(Max_domain_element_in_input);

  /* Handle checkpoint exit sentinel */
  if (rc == SEARCH_MAX_MODELS + 100)
    rc = SEARCH_MAX_MODELS + 100;

  /* Free domain-size memory (same as mace4n) */
  restore_from_stack(initial_state->stack);
  free_mstate(initial_state);

  if (flag(Opt->negprop))
    free_negprop_index();

  safe_free(Ordered_cells);
  Ordered_cells = NULL;

  for (i = 0; i < Number_of_cells; i++) {
    zap_mterm(Cells[i].eterm);
    safe_free(Cells[i].possible);
  }
  safe_free(Cells);
  Cells = NULL;

  for (i = 0; i < Domain_size; i++)
    zap_term(Domain[i]);
  safe_free(Domain);
  Domain = NULL;

  for (g = Ground_clauses; g != NULL; g = g->next)
    zap_mclause(g->v);
  zap_plist(Ground_clauses);
  Ground_clauses = NULL;

  set_variable_style(save_style);
  return rc;
}  /* mace4n_resume */
