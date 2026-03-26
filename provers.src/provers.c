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

#include "provers.h"
#include "../ladr/memory.h"
#include "../ladr/tptp_parse.h"
#include "../ladr/cnf.h"
#include "../ladr/sine.h"

#include <unistd.h>  /* for getopt */
#ifdef __APPLE__
#include <sys/sysctl.h>  /* for sysctlbyname (physical core count) */
#endif
#ifndef __EMSCRIPTEN__
#include <signal.h>
#include <sys/time.h>  /* for setitimer */

/* execinfo.h: backtrace() available on macOS 10.5+ and glibc Linux.
   Not available on macOS 10.4 (Tiger) or non-glibc systems. */
#if defined(__APPLE__)
#  include <AvailabilityMacros.h>
#  if defined(MAC_OS_X_VERSION_10_5) && \
      MAC_OS_X_VERSION_MAX_ALLOWED >= MAC_OS_X_VERSION_10_5
#    include <execinfo.h>
#    define HAVE_BACKTRACE 1
#  endif
#elif defined(__linux__)
#  include <execinfo.h>
#  define HAVE_BACKTRACE 1
#endif
#endif /* !__EMSCRIPTEN__ */

/* Private definitions and types */

#ifndef __EMSCRIPTEN__
static volatile sig_atomic_t Checkpoint_requested = 0;
static volatile sig_atomic_t No_kill = 0;
static volatile sig_atomic_t Pending_kill = 0;  /* 1 = SIGALRM, 2 = SIGTERM */
static volatile sig_atomic_t Tptp_mode_for_sig = 0;
#endif

#ifdef __EMSCRIPTEN__
/* WASM stubs: no signals, no process control */
void setup_timeout_signal(int seconds) { (void)seconds; }
void set_no_kill(void) { }
void clear_no_kill_and_check(void) { }
void set_tptp_mode_for_sig(void) { }
void enable_sigusr1_report(void) { }
void enable_sigusr2_checkpoint(void) { }
BOOL checkpoint_requested(void) { return FALSE; }
void clear_checkpoint_request(void) { }

#else /* native signal-based code */

/*************
 *
 *   timeout_handler()
 *
 *   Async-signal-safe handler for SIGALRM (timer expiry) and
 *   SIGTERM (parent requesting graceful shutdown).  If No_kill is
 *   set (proof output in progress), defers the kill by setting
 *   Pending_kill.  Only write() and _exit() are used (both are
 *   async-signal-safe per POSIX).
 *
 *   SIGALRM -> "Timeout" (exit MAX_SECONDS_EXIT)
 *   SIGTERM -> "User"    (exit SIGTERM_EXIT)
 *
 *************/

static
void timeout_handler(int sig)
{
  ssize_t wr;
  if (No_kill) { Pending_kill = (sig == SIGTERM ? 2 : 1); return; }
  if (Tptp_mode_for_sig) {
    if (sig == SIGTERM)
      wr = write(STDOUT_FILENO, "\n% SZS status User\n", 19);
    else
      wr = write(STDOUT_FILENO, "\n% SZS status Timeout\n", 22);
    (void) wr;
  }
  _exit(sig == SIGTERM ? SIGTERM_EXIT : MAX_SECONDS_EXIT);
}  /* timeout_handler */

/*************
 *
 *   setup_timeout_signal()
 *
 *   Arm an ITIMER_REAL timer to fire SIGALRM after `seconds` wall-clock
 *   seconds.  Also registers timeout_handler for both SIGALRM and SIGTERM
 *   via sigaction (SA_RESTART so syscalls are not interrupted).
 *   If seconds <= 0, no timer is armed (but SIGTERM handler is still
 *   installed for graceful shutdown).
 *
 *************/

/* PUBLIC */
void setup_timeout_signal(int seconds)
{
  struct sigaction sa;
  sa.sa_handler = timeout_handler;
  sa.sa_flags = SA_RESTART;
  sigemptyset(&sa.sa_mask);

  /* Only install timeout_handler for SIGALRM when seconds > 0.
     Cores children set max_seconds=-1 and use SIGALRM for suspend/wake
     (arm_suspend_timer), so we must not overwrite their handler. */
  if (seconds > 0) {
    struct itimerval itv;
    sigaction(SIGALRM, &sa, NULL);
    itv.it_value.tv_sec = seconds;
    itv.it_value.tv_usec = 0;
    itv.it_interval.tv_sec = 0;
    itv.it_interval.tv_usec = 0;
    setitimer(ITIMER_REAL, &itv, NULL);
  }

  /* Always install SIGTERM handler for graceful shutdown. */
  sigaction(SIGTERM, &sa, NULL);
}  /* setup_timeout_signal */

/*************
 *
 *   set_no_kill()
 *
 *   Defer signal-based termination (protect proof output from truncation).
 *
 *************/

/* PUBLIC */
void set_no_kill(void)
{
  No_kill = 1;
#ifdef SIGXCPU
  {
    sigset_t block;
    sigemptyset(&block);
    sigaddset(&block, SIGXCPU);
    sigprocmask(SIG_BLOCK, &block, NULL);
  }
#endif
}  /* set_no_kill */

/*************
 *
 *   clear_no_kill_and_check()
 *
 *   Re-enable signal-based termination.  If a signal arrived while
 *   No_kill was set, terminate now.
 *
 *************/

/* PUBLIC */
void clear_no_kill_and_check(void)
{
  int pk = Pending_kill;
  No_kill = 0;
#ifdef SIGXCPU
  {
    sigset_t unblock;
    sigemptyset(&unblock);
    sigaddset(&unblock, SIGXCPU);
    sigprocmask(SIG_UNBLOCK, &unblock, NULL);
  }
#endif
  if (pk == 2) {
    if (Tptp_mode_for_sig) {
      ssize_t wr = write(STDOUT_FILENO, "\n% SZS status User\n", 19);
      (void) wr;
    }
    _exit(SIGTERM_EXIT);
  }
  else if (pk) {
    if (Tptp_mode_for_sig) {
      ssize_t wr = write(STDOUT_FILENO, "\n% SZS status Timeout\n", 22);
      (void) wr;
    }
    _exit(MAX_SECONDS_EXIT);
  }
}  /* clear_no_kill_and_check */

/*************
 *
 *   set_tptp_mode_for_sig()
 *
 *   Tell the signal handler that TPTP output mode is active,
 *   so it can emit SZS status lines on timeout/kill.
 *
 *************/

/* PUBLIC */
void set_tptp_mode_for_sig(void)
{
  Tptp_mode_for_sig = 1;
}  /* set_tptp_mode_for_sig */

#endif /* __EMSCRIPTEN__ stubs vs native signal code */

static char Help_string[] =
"\nUsage: prover9 [-h] [-x] [-p] [-t <n>] [-m] [-r <dir>] [-f <files>]\n"
"       prover9 [-tptp] [-tptp_out] [-ladr_out] [-x] [-p] [-t <n>] [-m] problem.p\n"
"\n"
"  -h         Help.  Also see http://www.cs.unm.edu/~mccune/prover9/\n"
"  -x         set(auto2).  (enhanced auto mode)\n"
"  -p         Fully parenthesize output.\n"
"  -t n       assign(max_seconds, n).  (overrides ordinary input)\n"
"  -m         Enable memory logging (logs allocations/frees to stderr).\n"
"  -r dir     Resume from checkpoint directory (experimental).\n"
"  -f files   Take input from files instead of from standard input.\n"
"  -tptp      Force TPTP input mode (read from stdin).\n"
"  -tptp_out  TPTP/TSTP output mode (SZS status + TSTP proofs).\n"
"  -ladr_out  Native Prover9 output on TPTP input (override TSTP).\n"
"  -fastPE   5-second timeout on predicate elimination.\n"
"  -strategy N  Force portfolio strategy N (0-indexed, single-core).\n"
"  -cores N    Sliding-window scheduler: N concurrent children.\n"
"  -comp n   Competition mode: -cores <cpus> -fastPE -t n.\n"
"  -nomem    Disable memory limit (no max_megs callback).\n"
"  -stdin    Read LADR option overrides from stdin (with -f).\n"
"  file.p     Read TPTP input from file (auto-detected by .p extension).\n"
"\n";

struct arg_options {
  BOOL parenthesize_output;
  BOOL auto2;
  int  max_seconds;
  BOOL memory_log;
  BOOL files;
  BOOL resume;
  char *resume_dir;
  BOOL tptp_mode;
  char *tptp_file;    /* NULL means read from stdin */
  BOOL tptp_out;      /* TPTP/TSTP output mode */
  BOOL ladr_out;      /* native Prover9 output on TPTP input */
  BOOL fast_pred_elim;  /* 5-second pred elim timeout */
  int  cores;              /* sliding-window cores (-1 = use parm default) */
  BOOL read_stdin;         /* read LADR overrides from stdin (-stdin flag) */
};

/*************
 *
 *   get_command_line_args()
 *
 * This gets the command-line options and stores them in a structure
 * for later processing.  If an option is not recognized, the help
 * string is printed and then exit(1).
 *
 *************/

/*************
 *
 *   physical_cores()
 *
 *   Return number of physical CPU cores (not hyperthreads).
 *
 *************/

static
int physical_cores(void)
{
  int n;
#ifdef __APPLE__
  {
    int phys = 0;
    size_t sz = sizeof(phys);
    if (sysctlbyname("hw.physicalcpu", &phys, &sz, NULL, 0) == 0 && phys > 0)
      n = phys;
    else
      n = 4;
  }
#elif defined(_SC_NPROCESSORS_ONLN)
  /* Linux: logical / 2 as approximation (most CPUs have 2-way SMT) */
  n = (int) sysconf(_SC_NPROCESSORS_ONLN);
  if (n > 1) n = n / 2;
#else
  n = 4;
#endif
  if (n > 64) n = 64;
  return n;
}  /* physical_cores */

static
int performance_cores(void)
{
#ifdef __APPLE__
  {
    int perf = 0;
    size_t sz = sizeof(perf);
    /* hw.perflevel0.physicalcpu = P-cores on Apple Silicon.
       Falls back to physical_cores() on Intel Macs (no perflevel). */
    if (sysctlbyname("hw.perflevel0.physicalcpu", &perf, &sz, NULL, 0) == 0
        && perf > 0)
      return perf > 64 ? 64 : perf;
  }
#endif
  return physical_cores();
}  /* performance_cores */

static
struct arg_options get_command_line_args(int argc, char **argv)
{
  extern char *optarg;
  int c, i;
  BOOL has_cores = FALSE;
  struct arg_options opts = {FALSE, FALSE, INT_MAX, FALSE, FALSE, FALSE,
                             NULL, FALSE, NULL, FALSE, FALSE, FALSE, -1, FALSE};

  /* Pre-scan: -cores overrides -comp's core count if both present */
  for (i = 1; i < argc; i++)
    if (strcmp(argv[i], "-cores") == 0) { has_cores = TRUE; break; }

  /* Pre-scan for -tptp, -tptp_out (long options) and positional .p files.
     getopt only handles single-char options, so we handle these manually. */
  for (i = 1; i < argc; i++) {
    if (strcmp(argv[i], "-tptp") == 0) {
      opts.tptp_mode = TRUE;
      argv[i] = "-_";  /* neutralize so getopt skips it */
    }
    else if (strcmp(argv[i], "-tptp_out") == 0) {
      opts.tptp_out = TRUE;
      argv[i] = "-_";  /* neutralize so getopt skips it */
    }
    else if (strcmp(argv[i], "-ladr_out") == 0 ||
             strcmp(argv[i], "-ladr-out") == 0) {
      opts.ladr_out = TRUE;
      argv[i] = "-_";  /* neutralize so getopt skips it */
    }
    else if (strcmp(argv[i], "-fastPE") == 0) {
      opts.fast_pred_elim = TRUE;
      argv[i] = "-_";  /* neutralize so getopt skips it */
    }
    else if (strcmp(argv[i], "-stdin") == 0) {
      opts.read_stdin = TRUE;
      argv[i] = "-_";
    }
    else if (strcmp(argv[i], "-cores") == 0) {
      if (i + 1 < argc) {
        int max_cores = physical_cores();
        if (max_cores < 2) {
          fprintf(stderr, "Error: -cores requires at least 2 physical cores.\n");
          exit(1);
        }
        opts.cores = atoi(argv[i + 1]);
        if (opts.cores < 2) {
          fprintf(stderr, "%% WARNING: -cores %d too small, using 2.\n", opts.cores);
          opts.cores = 2;
        }
        if (opts.cores > max_cores) {
          fprintf(stderr, "%% WARNING: -cores %d exceeds %d physical cores, using %d.\n",
                  opts.cores, max_cores, max_cores);
          opts.cores = max_cores;
        }
        argv[i] = "-_";
        argv[i + 1] = "-_";
        i++;  /* skip value */
      }
      else {
        argv[i] = "-_";
      }
    }
    else if (strcmp(argv[i], "-comp") == 0) {
      if (!has_cores) {
        int pc = performance_cores();
        if (pc < 2) {
          fprintf(stderr, "Error: -comp requires at least 2 physical cores.\n");
          exit(1);
        }
        opts.cores = pc;
      }
      opts.tptp_mode = TRUE;
      opts.fast_pred_elim = TRUE;
      if (i + 1 < argc) {
        opts.max_seconds = atoi(argv[i + 1]);
        argv[i] = "-t";  /* convert to -t so re-parsing finds it */
        /* leave argv[i+1] as the number for getopt */
      }
      else {
        argv[i] = "-_";
      }
    }
    else if (argv[i][0] != '-') {
      /* Positional arg: check for .p or .tptp extension */
      int len = strlen(argv[i]);
      if ((len >= 2 && strcmp(argv[i] + len - 2, ".p") == 0) ||
          (len >= 5 && strcmp(argv[i] + len - 5, ".tptp") == 0)) {
        opts.tptp_mode = TRUE;
        opts.tptp_file = argv[i];
        argv[i] = "-_";  /* neutralize */
      }
    }
  }

  /* getopt() option string

     Initial colon: unrecognized options will not cause errors.

     No colons after option:  no argument.
     One colon after option:  argument required.
     Two colon after options: argument optional. (GNU extension! Don't use it!)
  */

  optind = 1;  /* reset getopt */
  while ((c = getopt(argc, argv,":hapxmt:r:f")) != EOF) {
    switch (c) {
    case 'x':
      opts.auto2 = TRUE;
      break;
    case 'p':
      opts.parenthesize_output = TRUE;
      break;
    case 't':
      opts.max_seconds = atoi(optarg);
      break;
    case 'm':
      opts.memory_log = TRUE;
      break;
    case 'r':
      opts.resume = TRUE;
      opts.resume_dir = optarg;
      break;
    case 'f':  /* input files */
      opts.files = TRUE;
      break;
    case 'h':
      printf("%s", Help_string);
      exit(1);
      break;
    default:
      /* Silently ignore neutralized args and unknown single-char opts */
      break;
    }
  }

  /* If -tptp was given but no file captured yet, use the -f argument.
     Accept any extension (.p, .tptp, etc.) when -tptp is explicit. */
  if (opts.tptp_mode && opts.tptp_file == NULL && opts.files) {
    int n = which_string_member("-f", argv, argc);
    if (n != -1 && n + 1 < argc)
      opts.tptp_file = argv[n + 1];
    else {
      fprintf(stderr, "Error: -f requires a filename argument.\n");
      exit(1);
    }
  }

  return opts;
}  /* get_command_line_args */

/*************
 *
 *   max_megs_exit()
 *
 *   This is intended to be called from the memory package.
 *
 *************/

static
void max_megs_exit(void)
{
  fprint_all_stats(stdout, "all");
  exit_with_message(stdout, MAX_MEGS_EXIT);
}  /* max_megs_exit */

/*************
 *
 *   process_command_line_args_1()
 *
 *   This is called BEFORE the input (clauses, etc) are read.  This is
 *   intended for high-level options that affect how input is read.
 *
 *************/

static
void process_command_line_args_1(struct arg_options command_opt,
				 Prover_options prover_opt)
{
  if (command_opt.auto2) {
    printf("\n%% From the command line: set(auto2).\n");
    set_flag(prover_opt->auto2, TRUE);
  }

  if (command_opt.parenthesize_output) {
    printf("\n%% From the command line: parenthesize output.\n");
    parenthesize(TRUE);  /* tell the parsing/printing package */
  }

  if (command_opt.tptp_out) {
    set_flag(prover_opt->tptp_output, FALSE);  // FALSE = no echo
    set_tptp_mode_for_sig();
  }

  if (command_opt.fast_pred_elim) {
    set_flag(prover_opt->fast_pred_elim, FALSE);  // FALSE = no echo
  }

  if (command_opt.cores > 0) {
    assign_parm(prover_opt->cores, command_opt.cores, FALSE);
  }

}  /* process_command_line_args_1 */

/*************
 *
 *   process_command_line_args_2()
 *
 * This is called AFTER the input (clauses, etc) are read.  This allows
 * command-line args to override settings in the ordinary input.
 *
 *************/

static
void process_command_line_args_2(struct arg_options command_opt,
				 Prover_options prover_opt)
{
  if (command_opt.max_seconds != INT_MAX) {
    int n = command_opt.max_seconds;
    int id = prover_opt->max_seconds;
    printf("\n%% From the command line: assign(%s, %d).\n",
	   parm_id_to_str(id), n);
    assign_parm(id, n, TRUE);
  }

  set_max_megs(parm(prover_opt->max_megs));
  set_max_megs_proc(max_megs_exit);

  // Re-apply CNF settings after all input has been read, so that
  // user options from the input file take effect.
  set_cnf_clause_limit(parm(prover_opt->cnf_clause_limit));
  set_cnf_def_threshold(parm(prover_opt->definitional_cnf));
  {
    int ms = parm(prover_opt->max_seconds);
    set_cnf_timeout(ms > 0 ? ms : 0);
  }

}  /* process_command_line_args_2 */

#ifndef __EMSCRIPTEN__

/*************
 *
 *   prover_sig_handler()
 *
 *************/

static
void prover_sig_handler(int condition)
{
  static volatile sig_atomic_t in_handler = 0;

  /* Prevent recursive entry (e.g., SIGSEGV during SIGINT handler) */
  if (in_handler) {
    _exit(condition == SIGSEGV ? SIGSEGV_EXIT : 1);
  }
  in_handler = 1;

  if (condition == SIGUSR2)
    fprintf(stderr, "\nCheckpoint requested.\n");
  else
    printf("\nProver catching signal %d.\n", condition);
  fflush(condition == SIGUSR2 ? stderr : stdout);
  if (condition == SIGSEGV || condition == SIGBUS) {
#ifdef HAVE_BACKTRACE
    /* Print backtrace for crash debugging */
    {
      void *bt_buf[200];
      int bt_size = backtrace(bt_buf, 200);
      fprintf(stderr, "--- backtrace (%d frames) ---\n", bt_size);
      backtrace_symbols_fd(bt_buf, bt_size, 2);
      fprintf(stderr, "--- end backtrace ---\n");
    }
#endif
    fflush(stderr);
  }
  switch (condition) {
  case SIGSEGV:
    fprint_all_stats(stdout, "all");
    exit_with_message(stdout, SIGSEGV_EXIT);
    break;
  case SIGINT:
    fprint_all_stats(stdout, "all");
    exit_with_message(stdout, SIGINT_EXIT);
    break;
  case SIGUSR1:
    report(stdout, "");
    report(stderr, "");
    break;
  case SIGUSR2:
    Checkpoint_requested = 1;
    break;
#ifdef SIGXCPU
  case SIGXCPU:
    fprint_all_stats(stdout, "all");
    exit_with_message(stdout, MAX_SECONDS_EXIT);
    break;
#endif
  default: fatal_error("prover_sig_handler, unknown signal");
  }
}  /* prover_sig_handler */

/*************
 *
 *   enable_sigusr1_report()
 *
 *   Install the SIGUSR1 handler for report().  This must not be
 *   called until Opt and Glob are initialized, because report()
 *   dereferences Opt.  SIGUSR1 is ignored (SIG_IGN) until this
 *   is called.
 *
 *************/

/* PUBLIC */
void enable_sigusr1_report(void)
{
  signal(SIGUSR1, prover_sig_handler);
}  /* enable_sigusr1_report */

/*************
 *
 *   enable_sigusr2_checkpoint()
 *
 *   Install the SIGUSR2 handler for checkpoint.  This must not be
 *   called until Opt and Glob are initialized.  SIGUSR2 is ignored
 *   (SIG_IGN) until this is called.
 *
 *************/

/* PUBLIC */
void enable_sigusr2_checkpoint(void)
{
  signal(SIGUSR2, prover_sig_handler);
}  /* enable_sigusr2_checkpoint */

/*************
 *
 *   checkpoint_requested()
 *
 *************/

/* PUBLIC */
BOOL checkpoint_requested(void)
{
  return Checkpoint_requested != 0;
}  /* checkpoint_requested */

/*************
 *
 *   clear_checkpoint_request()
 *
 *************/

/* PUBLIC */
void clear_checkpoint_request(void)
{
  Checkpoint_requested = 0;
}  /* clear_checkpoint_request */

#endif /* !__EMSCRIPTEN__ */

/*************
 *
 *   std_prover_init_and_input()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
Prover_input std_prover_init_and_input(int argc, char **argv,
				       BOOL clausify,
				       BOOL echo,
				       int unknown_action)
{
  Prover_input pi = safe_calloc(1, sizeof(struct prover_input));
  BOOL sine_done = FALSE;  /* set TRUE if scan-based SInE was already applied */

  struct arg_options opts = get_command_line_args(argc, argv);

  if (opts.memory_log)
    enable_memory_logging();

  init_standard_ladr();

  pi->options = init_prover_options();

  init_prover_attributes();

#ifndef __EMSCRIPTEN__
  /* Set up alternate signal stack so SIGSEGV/SIGBUS from stack overflow
     can still run the signal handler. */
  {
    static char alt_stack_mem[SIGSTKSZ];
    stack_t ss;
    ss.ss_sp = alt_stack_mem;
    ss.ss_size = SIGSTKSZ;
    ss.ss_flags = 0;
    sigaltstack(&ss, NULL);
  }

  signal(SIGINT,  prover_sig_handler);
#ifdef SIGXCPU
  signal(SIGXCPU, prover_sig_handler);
#endif
  signal(SIGUSR1, SIG_IGN);  /* ignore until search starts (Opt/Glob ready) */
  signal(SIGUSR2, SIG_IGN);  /* ignore until search starts (Opt/Glob ready) */
  /* Use sigaction for SIGSEGV/SIGBUS to enable SA_ONSTACK (alternate stack) */
  {
    struct sigaction sa;
    sa.sa_handler = prover_sig_handler;
    sa.sa_flags = SA_ONSTACK;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
  }

  /* Register SIGTERM handler early so fork children inherit it.
     No timer armed yet -- just the handler for graceful shutdown. */
  setup_timeout_signal(0);
#endif /* !__EMSCRIPTEN__ */

  if (opts.tptp_mode) {
    /*=========================================================================
     * TPTP input path: read native TPTP FOF/CNF via dedicated parser.
     * For large inputs with SInE, uses scan-first optimization:
     *   1. Fast scan pass (no Formula/Term trees, no symbol table)
     *   2. SInE filter on scan data
     *   3. Parse only selected formulas from saved text
     *=========================================================================*/
    Tptp_input tptp = NULL;
    Scan_result scan = NULL;
    Plist p;

    process_command_line_args_1(opts, pi->options);  // high-level, e.g., auto2

    // Auto-enable tptp_output EARLY in TPTP input mode (before any output).
    // This is done before processing magic comments so that
    // "% prover9: clear(tptp_output)." can override it.
    // -ladr_out overrides: keep native Prover9 output on TPTP input.
    if (!opts.ladr_out) {
      set_flag(pi->options->tptp_output, FALSE);  // FALSE = no echo
      set_tptp_mode_for_sig();
    }
    set_flag(pi->options->multi_order_trial, FALSE);  // auto-enable for TPTP

    // tptp_output dependencies suppress echo_input; update local echo.
    echo = flag(pi->options->echo_input);

    if (echo)
      print_separator(stdout, "INPUT (TPTP)", TRUE);

    // Install memory limit handler early.
    set_max_megs(parm(pi->options->max_megs));
    set_max_megs_proc(max_megs_exit);

    // Set TPTP defaults for CNF parameters.  Use assign_parm to set the
    // parm value itself, so that magic comments can override, and
    // process_command_line_args_2 reads the final value.
    if (parm(pi->options->cnf_clause_limit) == 0)
      assign_parm(pi->options->cnf_clause_limit, 100000, FALSE);
    set_cnf_clause_limit(parm(pi->options->cnf_clause_limit));

    if (parm(pi->options->definitional_cnf) == 0)
      assign_parm(pi->options->definitional_cnf, 1000, FALSE);
    set_cnf_def_threshold(parm(pi->options->definitional_cnf));

    {
      /* Use command-line -t if given (parm not set until process_command_line_args_2). */
      int ms = (opts.max_seconds != INT_MAX) ? opts.max_seconds
               : parm(pi->options->max_seconds);
      set_cnf_timeout(ms > 0 ? ms : 0);
    }

    // Set TPTP variable convention: uppercase = variable
    set_variable_style(PROLOG_STYLE);

    if (echo) {
      printf("\nset(prolog_style_variables).\n");
      printf("\n%% TPTP input mode: variables are uppercase (Prolog convention).\n");
    }

    // Phase 1: Fast scan pass -- always do this first.
    // Collects per-formula symbols and saves body text for later parsing.
    if (opts.tptp_file != NULL) {
      if (echo)
        printf("%% Scanning TPTP file %s\n", opts.tptp_file);
      scan = scan_tptp_formulas(opts.tptp_file);
    }
    else {
      if (echo)
        printf("%% Scanning TPTP input from stdin\n");
      scan = scan_tptp_stream(stdin, "<stdin>");
    }

#ifdef DEBUG
    fprintf(stderr, "%% Scan: %d formulas (%d axioms, %d goals), %d symbols\n",
            scan->n_entries, scan->n_axioms, scan->n_goals, scan->n_symbols);
#endif

    // Process magic comments from scan (before deciding SInE params).
    for (p = scan->magic_commands; p; p = p->next) {
      char *cmd = (char *) p->v;
      int len = strlen(cmd);
      if (len > 0) {
        if (echo)
          printf("%% From TPTP comment: %s\n", cmd);

        if (strncmp(cmd, "set(", 4) == 0) {
          char name[256];
          int ni = 0;
          const char *cp = cmd + 4;
          while (*cp && *cp != ')' && ni < 255)
            name[ni++] = *cp++;
          name[ni] = '\0';
          if (ni > 0) {
            int id = str_to_flag_id(name);
            if (id != -1)
              update_flag(stdout, id, TRUE, echo);
            else
              fprintf(stderr, "%% Warning: unknown flag '%s' in TPTP comment\n", name);
          }
        }
        else if (strncmp(cmd, "clear(", 6) == 0) {
          char name[256];
          int ni = 0;
          const char *cp = cmd + 6;
          while (*cp && *cp != ')' && ni < 255)
            name[ni++] = *cp++;
          name[ni] = '\0';
          if (ni > 0) {
            int id = str_to_flag_id(name);
            if (id != -1)
              update_flag(stdout, id, FALSE, echo);
            else
              fprintf(stderr, "%% Warning: unknown flag '%s' in TPTP comment\n", name);
          }
        }
        else if (strncmp(cmd, "assign(", 7) == 0) {
          char name[256];
          int ni = 0, val;
          const char *cp = cmd + 7;
          while (*cp && *cp != ',' && *cp != ')' && ni < 255)
            name[ni++] = *cp++;
          name[ni] = '\0';
          if (*cp == ',') cp++;
          while (*cp == ' ') cp++;
          val = atoi(cp);
          if (ni > 0) {
            int id = str_to_parm_id(name);
            if (id != -1)
              assign_parm(id, val, echo);
            else
              fprintf(stderr, "%% Warning: unknown parm '%s' in TPTP comment\n", name);
          }
        }
        else {
          fprintf(stderr, "%% Warning: unrecognized TPTP command: %s\n", cmd);
        }
      }
    }

    // Re-check echo after magic comments may have changed tptp_output
    echo = flag(pi->options->echo_input);

    // Phase 2: Decide if scan-based SInE applies.
    // If n_axioms > 5000 and SInE is active, do SInE on scan data and
    // parse only selected formulas (huge speedup for 38k-axiom problems).
    {
      int sine_val = parm(pi->options->sine);
      int scan_n_axioms = scan->n_axioms;
      int eff_tolerance = 0;

      if (sine_val == -1) {
        if (scan_n_axioms > 128 &&
            (scan->n_goals > 0 || scan->has_neg_conj))
          eff_tolerance = 200;
      }
      else if (sine_val > 0 &&
               (scan->n_goals > 0 || scan->has_neg_conj)) {
        eff_tolerance = sine_val;
      }

      if (eff_tolerance > 0 && scan_n_axioms > 5000) {
        /* Scan-based SInE for large inputs */
        int eff_depth = parm(pi->options->sine_depth);
        int wide_tol = (eff_depth == 0) ? eff_tolerance : 0;
        int *sel_depth, *loose_depth;
        BOOL *keep;
        int i, n_sel = 0, n_usa = 0, n_zapped = 0;

        if (eff_depth == 0) {
          eff_tolerance = 150;  /* tight = 1.5x for depth-based mode */
          eff_depth = 3;        /* depth 1-2 tight->SOS, depth 3->usable */
        }

        sel_depth = safe_calloc(scan->n_entries, sizeof(int));
        loose_depth = safe_calloc(scan->n_entries, sizeof(int));

        sine_filter_scan(scan->entries, scan->n_entries, scan->n_symbols,
                         eff_tolerance, wide_tol, eff_depth,
                         parm(pi->options->sine_max_axioms),
                         sel_depth, loose_depth);

        /* Build keep[] array: parse tight + loose selected + goals */
        keep = safe_calloc(scan->n_entries, sizeof(BOOL));
        for (i = 0; i < scan->n_entries; i++) {
          if (scan->entries[i].role == SCAN_ROLE_GOAL) {
            keep[i] = TRUE;  /* always parse goals */
          }
          else if (sel_depth[i]) {
            keep[i] = TRUE;
            n_sel++;
          }
          else if (loose_depth[i]) {
            keep[i] = TRUE;
            n_usa++;
          }
          else {
            n_zapped++;
          }
        }


#ifdef DEBUG
        fprintf(stderr, "%% Scan SInE: parsing %d of %d formulas "
                "(%d tight + %d loose + %d goals, %d zapped)\n",
                n_sel + n_usa + scan->n_goals, scan->n_entries,
                n_sel, n_usa, scan->n_goals, n_zapped);
#endif

        /* Phase 3: Parse only selected formulas from saved text */
        tptp = parse_scanned_formulas(scan, keep);

        /* Set sine_depth attributes on parsed assumptions.
           Parse order matches scan order for kept entries, so we walk
           assumptions in parallel with the scan entries. */
        {
          Plist ap = tptp->assumptions;
          int attr_id = sine_depth_attr();
          for (i = 0; i < scan->n_entries && ap != NULL; i++) {
            if (!keep[i] || scan->entries[i].role == SCAN_ROLE_GOAL)
              continue;
            {
              int d = sel_depth[i] ? sel_depth[i] : loose_depth[i];
              if (d > 0) {
                Formula f = (Formula) ap->v;
                f->attributes = set_int_attribute(f->attributes, attr_id, d);
              }
            }
            ap = ap->next;
          }
        }

        /* Partition assumptions into sos/usable based on sel_depth/loose_depth */
        {
          Plist sos_result = NULL;
          Plist usable_result = NULL;
          Plist ap = tptp->assumptions;
          Plist nxt;
          for (i = 0; i < scan->n_entries && ap != NULL; i++) {
            if (!keep[i] || scan->entries[i].role == SCAN_ROLE_GOAL)
              continue;
            nxt = ap->next;
            ap->next = NULL;
            if (sel_depth[i] && sel_depth[i] <= 2) {
              sos_result = plist_cat(sos_result, ap);
            }
            else {
              usable_result = plist_cat(usable_result, ap);
            }
            ap = nxt;
          }
          pi->sos = sos_result;
          pi->usable = usable_result;
        }
        pi->goals = tptp->goals;
        pi->has_neg_conj = tptp->has_neg_conj;

        if (wide_tol > 0)
          fprintf(stdout, "\n%% SInE (scan): %d to sos (tol %.1fx), "
                  "%d to usable (tol %.1fx), %d zapped, of %d axioms "
                  "(depth %d).\n",
                  n_sel, eff_tolerance / 100.0,
                  n_usa, wide_tol / 100.0,
                  n_zapped, scan_n_axioms, eff_depth);
        else
          fprintf(stdout, "\n%% SInE (scan): %d to sos, %d to usable, "
                  "of %d axioms (tolerance %.2f, depth %d%s).\n",
                  n_sel, n_usa, scan_n_axioms,
                  eff_tolerance / 100.0, eff_depth,
                  eff_depth == 0 ? " fixpoint" : "");

        /* Auto-enable sine_weight tuning */
        if (parm(pi->options->sine_weight) == 0)
          assign_parm(pi->options->sine_weight, 100, FALSE);
        if (parm(pi->options->sine_weight) > 0) {
          if (parm(pi->options->weight_part) == 0)
            assign_parm(pi->options->weight_part, 2, FALSE);
          if (flag(pi->options->input_sos_first))
            clear_flag(pi->options->input_sos_first, FALSE);
        }

        sine_done = TRUE;
        safe_free(sel_depth);
        safe_free(loose_depth);
        safe_free(keep);

        /* Free scan but not magic_commands (transferred to tptp) */
        tptp->assumptions = NULL;
        tptp->goals = NULL;
        free_scan_result(scan);
        scan = NULL;
        safe_free(tptp);
        tptp = NULL;
      }
      else {
        /* Small input or SInE disabled: parse all from saved text */
        if (echo)
          printf("%% Parsing all %d formulas from scan data\n\n",
                 scan->n_entries);
        tptp = parse_scanned_formulas(scan, NULL);  /* keep=NULL: parse all */

        pi->sos = tptp->assumptions;
        pi->goals = tptp->goals;
        pi->has_neg_conj = tptp->has_neg_conj;

        /* Free scan and tptp shell */
        tptp->assumptions = NULL;
        tptp->goals = NULL;
        free_scan_result(scan);
        scan = NULL;
        zap_tptp_input(tptp);
        tptp = NULL;
      }
    }

    // TPTP provers exit on first proof.  Force max_proofs=1 to match.
    assign_parm(pi->options->max_proofs, 1, FALSE);

    // Echo formulas
    if (echo) {
      printf("\nformulas(assumptions).\n");
      for (p = pi->sos; p; p = p->next) {
        printf("        ");
        fprint_formula(stdout, (Formula) p->v);
        printf(".\n");
      }
      if (pi->usable != NULL) {
        printf("end_of_list.\n\nformulas(usable).\n");
        for (p = pi->usable; p; p = p->next) {
          printf("        ");
          fprint_formula(stdout, (Formula) p->v);
          printf(".\n");
        }
      }
      printf("end_of_list.\n");

      if (pi->goals != NULL) {
        printf("\nformulas(goals).\n");
        for (p = pi->goals; p; p = p->next) {
          printf("        ");
          fprint_formula(stdout, (Formula) p->v);
          printf(".\n");
        }
        printf("end_of_list.\n");
      }
    }

    // Gather symbols and declare functions/relations
    {
      int sn = greatest_symnum() + 1;
      int *rcounts = safe_calloc(sn, sizeof(int));
      int *fcounts = safe_calloc(sn, sizeof(int));
      Ilist rsyms, fsyms;
      gather_symbols_in_formulas(pi->sos, rcounts, fcounts);
      gather_symbols_in_formulas(pi->usable, rcounts, fcounts);
      gather_symbols_in_formulas(pi->goals, rcounts, fcounts);
      rsyms = counts_to_set(rcounts, sn);
      fsyms = counts_to_set(fcounts, sn);
      safe_free(rcounts);
      safe_free(fcounts);
      declare_functions_and_relations(fsyms, rsyms);
      zap_ilist(fsyms);
      zap_ilist(rsyms);
    }

    if (echo)
      print_separator(stdout, "end of input", TRUE);

    process_command_line_args_2(opts, pi->options);  // others, which override

    if (!option_dependencies_state()) {
      printf("\n%% Enabling option dependencies (ignore applies only on input).\n");
      enable_option_dependencies();
    }
  }
  else {
    /*=========================================================================
     * Standard LADR input path (unchanged)
     *=========================================================================*/

  // Tell the top_input package what lists to accept and where to put them.

  accept_list("sos",          FORMULAS, FALSE, &(pi->sos));
  accept_list("assumptions",  FORMULAS, FALSE, &(pi->sos));  // Synonym for sos
  accept_list("goals",        FORMULAS, FALSE, &(pi->goals));
  accept_list("usable",       FORMULAS, FALSE, &(pi->usable));
  accept_list("demodulators", FORMULAS, FALSE, &(pi->demods));
  accept_list("hints",        FORMULAS, TRUE,  &(pi->hints));
  accept_list("unused",       FORMULAS, TRUE,  &(pi->unused));

  accept_list("actions",         TERMS, FALSE, &(pi->actions));
  accept_list("weights",         TERMS, FALSE, &(pi->weights));
  accept_list("kbo_weights",     TERMS, FALSE, &(pi->kbo_weights));
  accept_list("interpretations", TERMS, FALSE, &(pi->interps));
  accept_list("given_selection", TERMS, FALSE, &(pi->given_selection));
  accept_list("keep",            TERMS, FALSE, &(pi->keep_rules));
  accept_list("delete",          TERMS, FALSE, &(pi->delete_rules));

  process_command_line_args_1(opts, pi->options);  // high-level, e.g., auto2

  // Update echo: -tptp_out may have suppressed echo_input via dependencies
  echo = echo && flag(pi->options->echo_input);

  if (echo)
    print_separator(stdout, "INPUT", TRUE);

  // Install memory limit handler early so we get stats if input blows memory.
  set_max_megs(parm(pi->options->max_megs));
  set_max_megs_proc(max_megs_exit);

  // Set CNF clause limit if configured.
  set_cnf_clause_limit(parm(pi->options->cnf_clause_limit));

  // Set definitional CNF threshold if configured.
  set_cnf_def_threshold(parm(pi->options->definitional_cnf));

  {
    /* Use command-line -t if given (parm not set until process_command_line_args_2). */
    int ms = (opts.max_seconds != INT_MAX) ? opts.max_seconds
             : parm(pi->options->max_seconds);
    set_cnf_timeout(ms > 0 ? ms : 0);
  }

  // Read commands such as set, clear, op, lex.
  // Read lists, filling in variables given to the accept_list calls.

  if (opts.resume && !opts.files &&
      which_string_member("-f", argv, argc) == -1) {
    /* Resume without -f: check if stdin has real input or is empty.
       If stdin is a terminal or at immediate EOF, use saved_input.txt
       from the checkpoint directory instead. */
    BOOL use_saved = FALSE;
    if (isatty(fileno(stdin))) {
      use_saved = TRUE;
    }
    else {
      /* Check for immediate EOF (e.g. /dev/null redirect) */
      int ch = fgetc(stdin);
      if (ch == EOF)
        use_saved = TRUE;
      else
        ungetc(ch, stdin);  /* push back — stdin has real input */
    }
    if (use_saved) {
      char saved_path[1024];
      snprintf(saved_path, sizeof(saved_path), "%s/saved_input.txt",
               opts.resume_dir);
      if (freopen(saved_path, "r", stdin) != NULL) {
        printf("\n%% Reading saved input from %s\n", saved_path);
      }
      else {
        fatal_error("Resume: no input file and no saved_input.txt in "
                    "checkpoint directory.  Provide input via stdin or -f.");
      }
    }
  }

  read_all_input(argc, argv, stdout, echo, unknown_action);

  // Update echo: set(tptp_output) in input may have suppressed echo_input
  echo = echo && flag(pi->options->echo_input);

  if (echo)
    print_separator(stdout, "end of input", TRUE);
  process_command_line_args_2(opts, pi->options);  // others, which override

  if (opts.resume) {
    pi->resume_dir = opts.resume_dir;
    printf("\n%% From the command line: resume from %s (experimental).\n", opts.resume_dir);
  }

  if (!option_dependencies_state()) {
    printf("\n%% Enabling option dependencies (ignore applies only on input).\n");
    enable_option_dependencies();
  }

  }  /* end of LADR path */

  /* SInE premise selection (before clausification).
     Skip if scan-based SInE was already applied in the TPTP scan path. */
  if (!sine_done)
  {
    int sine_val = parm(pi->options->sine);
    int n_axioms = plist_count(pi->sos);

    /* Resolve auto mode: -1 = auto-enable for TPTP with >128 axioms */
    int eff_tolerance = 0;
    if (sine_val == -1) {
      if (opts.tptp_mode && n_axioms > 128 && pi->goals != NULL)
        eff_tolerance = 200;
    } else if (sine_val > 0 && pi->goals != NULL) {
      eff_tolerance = sine_val;
    }

    if (eff_tolerance > 0) {
      int eff_depth = parm(pi->options->sine_depth);
      /* For large axiom sets (>5000): two-tolerance single-pass SInE.
         Tight tol (2.0x) -> SOS with sine_weight, wide tol (3.0x) -> usable,
         rest zapped.  BFS depth auto-limited to 3.
         For small axiom sets: single-tolerance soft filter (all selected
         -> SOS, unselected -> usable). */
      int wide_tol = (n_axioms > 5000 && eff_depth == 0)
                     ? eff_tolerance  /* wide = original 2.0x */
                     : 0;  /* disabled: single-threshold mode */
      Plist selected = NULL;
      Plist usable_add = NULL;
      Plist unselected = NULL;
      Plist p;
      int n_sel, n_usa, n_zapped;

      if (n_axioms > 5000 && eff_depth == 0) {
        eff_tolerance = 150;  /* tight = 1.5x for large axiom sets */
        eff_depth = 3;
      }

      sine_filter(pi->sos, pi->goals,
                  eff_tolerance, wide_tol, eff_depth,
                  &selected, &usable_add, &unselected);

      n_sel = plist_count(selected);
      n_usa = plist_count(usable_add);
      n_zapped = n_axioms - n_sel - n_usa;

      pi->sos = selected;
      pi->usable = plist_cat(pi->usable, usable_add);

      /* Zap unselected formulas */
      for (p = unselected; p; p = p->next)
        zap_formula((Formula) p->v);
      zap_plist(unselected);

      if (wide_tol > 0)
        fprintf(stdout, "\n%% SInE: %d to sos (tol %.1fx), "
                "%d to usable (tol %.1fx), %d zapped, of %d axioms "
                "(depth %d).\n",
                n_sel, eff_tolerance / 100.0,
                n_usa, wide_tol / 100.0,
                n_zapped, n_axioms, eff_depth);
      else
        fprintf(stdout, "\n%% SInE: %d to sos, %d to usable, of %d axioms "
                "(tolerance %.2f, depth %d%s).\n",
                n_sel, n_usa, n_axioms,
                eff_tolerance / 100.0, eff_depth,
                eff_depth == 0 ? " fixpoint" : "");

      /* Auto-enable sine_weight=100 (if not explicitly set by user) and
         tune the given-clause selector: add weight_part so the W selector
         fires, and disable input_sos_first so depth weighting takes
         effect immediately (the I selector picks by age, ignoring weight). */
      if (parm(pi->options->sine_weight) == 0)
        assign_parm(pi->options->sine_weight, 100, FALSE);
      if (parm(pi->options->sine_weight) > 0) {
        if (parm(pi->options->weight_part) == 0)
          assign_parm(pi->options->weight_part, 2, FALSE);
        if (flag(pi->options->input_sos_first))
          clear_flag(pi->options->input_sos_first, FALSE);
      }
    }
  }

  if (clausify) {
    Plist denials;

    pi->sos    = embed_formulas_in_topforms(pi->sos, TRUE);
    pi->usable = embed_formulas_in_topforms(pi->usable, TRUE);
    pi->demods = embed_formulas_in_topforms(pi->demods, TRUE);
    pi->hints  = embed_formulas_in_topforms(pi->hints, TRUE);
    pi->goals  = embed_formulas_in_topforms(pi->goals, FALSE);

    pi->has_goals = (pi->goals != NULL);

    /* Extract TPTP problem name from .p filename for SZS lines. */
    {
      const char *path = opts.tptp_file;  /* NULL if stdin or LADR mode */
      if (path == NULL && opts.files) {
	/* -f mode: use first -f argument if it's a .p file */
	int n = which_string_member("-f", argv, argc);
	if (n >= 0 && n + 1 < argc) {
	  int flen = strlen(argv[n + 1]);
	  if (flen >= 2 && strcmp(argv[n + 1] + flen - 2, ".p") == 0)
	    path = argv[n + 1];
	}
      }
      if (path != NULL) {
	const char *base = strrchr(path, '/');
	base = (base != NULL) ? base + 1 : path;
	int len = strlen(base);
	/* Strip .p extension */
	if (len >= 2 && strcmp(base + len - 2, ".p") == 0)
	  len -= 2;
	if (len > 0) {
	  char *name = safe_malloc(len + 1);
	  memcpy(name, base, len);
	  name[len] = '\0';
	  pi->problem_name = name;
	}
      }
    }

    /* Enable SZS status output in fatal_error() and signal handlers */
    if (flag(pi->options->tptp_output)) {
      set_fatal_tptp_mode(TRUE, pi->problem_name);
      set_tptp_mode_for_sig();
    }

    if (flag(pi->options->expand_relational_defs)) {
      Plist defs, nondefs, p;
      separate_definitions(pi->sos, &defs, &nondefs);
      pi->sos = NULL;
      if (echo)
        print_separator(stdout, "EXPAND RELATIONAL DEFINITIONS", TRUE);
      if (defs) {
	Plist results, rewritten, defs2;

	printf("\n%% Relational Definitions:\n");
	for (p = defs; p; p = p->next) {
	  Topform tf = p->v;
	  assign_clause_id(tf);
	  fwrite_clause(stdout, tf, CL_FORM_STD);
	}

	/* Expand definitions w.r.t. themselves. */
	process_definitions(defs, &results, &defs2, &rewritten);
	if (results != NULL)
	  fatal_error("Circular relational definitions");

	defs = defs2;

	if (rewritten) {
	  printf("\n%% Relational Definitions, Expanded:\n");
	  for (p = defs; p; p = p->next)
	    if (!has_input_just(p->v))
	      fwrite_clause(stdout, p->v, CL_FORM_STD);
	}

	results = NULL;
	expand_with_definitions(nondefs, defs, &results, &rewritten);
	pi->sos = reverse_plist(results);

	results = NULL;
	expand_with_definitions(pi->usable, defs, &results, &rewritten);
	pi->usable = reverse_plist(results);

	results = NULL;
	expand_with_definitions(pi->hints, defs, &results, &rewritten);
	pi->hints = reverse_plist(results);

	results = NULL;
	expand_with_definitions(pi->goals, defs, &results, &rewritten);
	pi->goals = reverse_plist(results);

	for (p = defs; p; p = p->next)
	  append_label_attribute(p->v, "non_clause");

	if (rewritten) {
	  printf("\n%% Formulas Being Expanded:\n");
	  rewritten = reverse_plist(rewritten);
	  for (p = rewritten; p; p = p->next) {
	    Topform tf = p->v;
	    fwrite_clause(stdout, tf, CL_FORM_STD);
	    append_label_attribute(tf, "non_clause");
	  }
	}
	/* After this point, the "defs" and "rewritten" formulas
	   will be accessible only from the Clause ID table, e.g.,
	   for inclusion in proofs.
	 */
      }
      else {
	printf("\n%% No relational definitions were found.\n");
	pi->sos = nondefs;
      }
      if (echo)
        print_separator(stdout, "end of expand relational definitions", TRUE);
    }

    if (echo)
      print_separator(stdout, "PROCESS NON-CLAUSAL FORMULAS", TRUE);
    {
      int echo_id = str_to_flag_id("echo_input");
      BOOL echo_clausify = echo && (echo_id == -1 ? TRUE : flag(echo_id));

      if (echo_clausify)
	printf("\n%% Formulas that are not ordinary clauses:\n");
      else if (echo)
	printf("\n%% Formulas that are not ordinary clauses: not echoed\n");

      /* Clausify can hit max_vars -- report as GaveUp, not Error */
      set_fatal_szs_status("GaveUp");

#ifdef DEBUG
      fprintf(stderr, "%% Clausifying sos (%d formulas)...\n",
              plist_count(pi->sos));
#endif
      pi->sos    = process_input_formulas(pi->sos, echo_clausify);
#ifdef DEBUG
      fprintf(stderr, "%% Clausifying usable (%d formulas)...\n",
              plist_count(pi->usable));
#endif
      pi->usable = process_input_formulas(pi->usable, echo_clausify);
      pi->demods = process_demod_formulas(pi->demods, echo_clausify);
      {
        /* Hints are auxiliary data, not the logical theory.  Temporarily
           disable the CNF clause limit so complex hint formulas don't
           trigger the blowup guard meant for the main input. */
        int saved_limit = cnf_clause_limit();
        set_cnf_clause_limit(0);
        pi->hints  = process_input_formulas(pi->hints, echo_clausify);
        set_cnf_clause_limit(saved_limit);
      }
#ifdef DEBUG
      fprintf(stderr, "%% Clausifying goals...\n");
#endif
      denials    = process_goal_formulas(pi->goals, echo_clausify);

      set_fatal_szs_status(NULL);  /* reset to default for search phase */
    }

    pi->goals = NULL;

    /* move to denials (negated goals) to the end of sos */

    pi->sos = plist_cat(pi->sos, denials);


#ifdef DEBUG
    fprintf(stderr, "%% Preprocessing done: %d sos, %d usable clauses.\n",
            plist_count(pi->sos), plist_count(pi->usable));
#endif

    if (echo)
      print_separator(stdout, "end of process non-clausal formulas", TRUE);
  }

  return pi;
}  /* std_prover_init_and_input */

/*************
 *
 *   std_prover_init_and_scan()
 *
 *   Phase 1 of two-phase TPTP entry: initialize, scan, process magic
 *   comments.  Returns a Prover_scan_result that can be passed to
 *   std_prover_from_scan().  This is used by the strategy scheduler
 *   to fork AFTER the scan but BEFORE SInE/parse/clausify, so each
 *   child can apply its own SInE parameters.
 *
 *   TPTP mode only.  For LADR mode, use std_prover_init_and_input().
 *
 *************/

/* PUBLIC */
Prover_scan_result std_prover_init_and_scan(int argc, char **argv)
{
  Prover_scan_result psr;
  Prover_options options;
  struct arg_options opts;
  BOOL echo;
  Scan_result scan;
  Plist p;

  psr = safe_calloc(1, sizeof(struct prover_scan_result));
  opts = get_command_line_args(argc, argv);

  if (opts.memory_log)
    enable_memory_logging();

  init_standard_ladr();

  options = init_prover_options();

  init_prover_attributes();

#ifndef __EMSCRIPTEN__
  /* Set up alternate signal stack */
  {
    static char alt_stack_mem[SIGSTKSZ];
    stack_t ss;
    ss.ss_sp = alt_stack_mem;
    ss.ss_size = SIGSTKSZ;
    ss.ss_flags = 0;
    sigaltstack(&ss, NULL);
  }

  signal(SIGINT,  prover_sig_handler);
#ifdef SIGXCPU
  signal(SIGXCPU, prover_sig_handler);
#endif
  signal(SIGUSR1, SIG_IGN);
  signal(SIGUSR2, SIG_IGN);
  {
    struct sigaction sa;
    sa.sa_handler = prover_sig_handler;
    sa.sa_flags = SA_ONSTACK;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
  }

  /* Register SIGTERM handler early so fork children inherit it. */
  setup_timeout_signal(0);
#endif /* !__EMSCRIPTEN__ */

  process_command_line_args_1(opts, options);

  /* Auto-enable TPTP mode flags */
  if (!opts.ladr_out)
    set_flag(options->tptp_output, FALSE);
  set_flag(options->multi_order_trial, FALSE);

  echo = flag(options->echo_input);

  if (echo)
    print_separator(stdout, "INPUT (TPTP)", TRUE);

  /* Install memory limit handler early */
  set_max_megs(parm(options->max_megs));
  set_max_megs_proc(max_megs_exit);

  /* TPTP defaults for CNF parameters */
  if (parm(options->cnf_clause_limit) == 0)
    assign_parm(options->cnf_clause_limit, 100000, FALSE);
  set_cnf_clause_limit(parm(options->cnf_clause_limit));

  if (parm(options->definitional_cnf) == 0)
    assign_parm(options->definitional_cnf, 1000, FALSE);
  set_cnf_def_threshold(parm(options->definitional_cnf));

  {
    /* Use command-line -t if given (parm not set until later). */
    int ms = (opts.max_seconds != INT_MAX) ? opts.max_seconds
             : parm(options->max_seconds);
    set_cnf_timeout(ms > 0 ? ms : 0);
  }

  set_variable_style(PROLOG_STYLE);

  if (echo) {
    printf("\nset(prolog_style_variables).\n");
    printf("\n%% TPTP input mode: variables are uppercase (Prolog convention).\n");
  }

  /* Read LADR option overrides from stdin when -stdin flag is given.
     This lets training scripts pipe set/clear/assign commands via stdin. */
  if (opts.tptp_file != NULL && opts.read_stdin) {
    char line[1024];
    while (fgets(line, sizeof(line), stdin) != NULL) {
      char *cp = line;
      int len;
      /* Strip leading whitespace */
      while (*cp == ' ' || *cp == '\t') cp++;
      /* Skip blank lines and comments */
      if (*cp == '\0' || *cp == '\n' || *cp == '%') continue;
      /* Strip trailing whitespace/newline */
      len = strlen(cp);
      while (len > 0 && (cp[len-1] == '\n' || cp[len-1] == '\r' ||
                         cp[len-1] == ' '  || cp[len-1] == '\t'))
        cp[--len] = '\0';
      if (len == 0) continue;

      if (strncmp(cp, "set(", 4) == 0) {
        char name[256];
        int ni = 0;
        const char *np = cp + 4;
        while (*np && *np != ')' && ni < 255)
          name[ni++] = *np++;
        name[ni] = '\0';
        if (ni > 0) {
          int id = str_to_flag_id(name);
          if (id != -1) {
            set_flag(id, echo);
            if (echo)
              fprintf(stderr, "%% stdin option: set(%s)\n", name);
          }
          else
            fprintf(stderr, "%% Warning: unknown flag '%s' from stdin\n", name);
        }
      }
      else if (strncmp(cp, "clear(", 6) == 0) {
        char name[256];
        int ni = 0;
        const char *np = cp + 6;
        while (*np && *np != ')' && ni < 255)
          name[ni++] = *np++;
        name[ni] = '\0';
        if (ni > 0) {
          int id = str_to_flag_id(name);
          if (id != -1) {
            clear_flag(id, echo);
            if (echo)
              fprintf(stderr, "%% stdin option: clear(%s)\n", name);
          }
          else
            fprintf(stderr, "%% Warning: unknown flag '%s' from stdin\n", name);
        }
      }
      else if (strncmp(cp, "assign(", 7) == 0) {
        char name[256];
        int ni = 0;
        int val;
        const char *np = cp + 7;
        while (*np && *np != ',' && *np != ')' && ni < 255)
          name[ni++] = *np++;
        name[ni] = '\0';
        if (*np == ',') np++;
        while (*np == ' ') np++;
        val = atoi(np);
        if (ni > 0) {
          int id = str_to_parm_id(name);
          if (id != -1) {
            assign_parm(id, val, echo);
            if (echo)
              fprintf(stderr, "%% stdin option: assign(%s, %d)\n", name, val);
          }
          else {
            int fid = str_to_floatparm_id(name);
            if (fid != -1) {
              assign_floatparm(fid, (double) val, echo);
              if (echo)
                fprintf(stderr, "%% stdin option: assign(%s, %d)\n", name, val);
            }
            else {
              int sid = str_to_stringparm_id(name);
              if (sid != -1) {
                /* For stringparm, value is a string, not int */
                char sval[256];
                int si = 0;
                while (*np && *np != ')' && *np != '.' && si < 255) {
                  if (*np != ' ') sval[si++] = *np;
                  np++;
                }
                sval[si] = '\0';
                assign_stringparm(sid, sval, echo);
                if (echo)
                  fprintf(stderr, "%% stdin option: assign(%s, %s)\n", name, sval);
              }
              else
                fprintf(stderr,
                  "%% Warning: unknown parm '%s' from stdin\n", name);
            }
          }
        }
      }
    }
  }

  /* Phase 1: Fast scan pass */
  if (opts.tptp_file != NULL) {
    if (echo)
      printf("%% Scanning TPTP file %s\n", opts.tptp_file);
    scan = scan_tptp_formulas(opts.tptp_file);
  }
  else {
    if (echo)
      printf("%% Scanning TPTP input from stdin\n");
    scan = scan_tptp_stream(stdin, "<stdin>");
  }
#ifdef DEBUG
  fprintf(stderr, "%% Scan: %d formulas (%d axioms, %d goals), %d symbols\n",
          scan->n_entries, scan->n_axioms, scan->n_goals, scan->n_symbols);
#endif

  /* Process magic comments from scan */
  for (p = scan->magic_commands; p; p = p->next) {
    char *cmd = (char *) p->v;
    int len = strlen(cmd);
    if (len > 0) {
      if (echo)
        printf("%% From TPTP comment: %s\n", cmd);

      if (strncmp(cmd, "set(", 4) == 0) {
        char name[256];
        int ni = 0;
        const char *cp = cmd + 4;
        while (*cp && *cp != ')' && ni < 255)
          name[ni++] = *cp++;
        name[ni] = '\0';
        if (ni > 0) {
          int id = str_to_flag_id(name);
          if (id != -1)
            update_flag(stdout, id, TRUE, echo);
          else
            fprintf(stderr, "%% Warning: unknown flag '%s' in TPTP comment\n", name);
        }
      }
      else if (strncmp(cmd, "clear(", 6) == 0) {
        char name[256];
        int ni = 0;
        const char *cp = cmd + 6;
        while (*cp && *cp != ')' && ni < 255)
          name[ni++] = *cp++;
        name[ni] = '\0';
        if (ni > 0) {
          int id = str_to_flag_id(name);
          if (id != -1)
            update_flag(stdout, id, FALSE, echo);
          else
            fprintf(stderr, "%% Warning: unknown flag '%s' in TPTP comment\n", name);
        }
      }
      else if (strncmp(cmd, "assign(", 7) == 0) {
        char name[256];
        int ni = 0, val;
        const char *cp = cmd + 7;
        while (*cp && *cp != ',' && *cp != ')' && ni < 255)
          name[ni++] = *cp++;
        name[ni] = '\0';
        if (*cp == ',') cp++;
        while (*cp == ' ') cp++;
        val = atoi(cp);
        if (ni > 0) {
          int id = str_to_parm_id(name);
          if (id != -1)
            assign_parm(id, val, echo);
          else
            fprintf(stderr, "%% Warning: unknown parm '%s' in TPTP comment\n", name);
        }
      }
      else {
        fprintf(stderr, "%% Warning: unrecognized TPTP command: %s\n", cmd);
      }
    }
  }

  /* Re-check echo after magic comments may have changed tptp_output */
  echo = flag(options->echo_input);

  /* Fill result struct */
  psr->scan = scan;
  psr->options = options;
  psr->echo = echo;
  psr->argc = argc;
  psr->argv = argv;
  psr->tptp_file = opts.tptp_file;
  psr->tptp_out = opts.tptp_out;
  psr->ladr_out = opts.ladr_out;

  return psr;
}  /* std_prover_init_and_scan */

/*************
 *
 *   std_prover_from_scan()
 *
 *   Phase 2 of two-phase TPTP entry: SInE filter, parse, clausify.
 *   Takes a Prover_scan_result from std_prover_init_and_scan() plus
 *   per-child SInE parameters.
 *
 *   sine_tolerance:  -1 = use adaptive default from options
 *   sine_depth:      -1 = use adaptive default from options
 *   sine_max_axioms: -1 = use adaptive default from options
 *
 *************/

/* PUBLIC */
Prover_input std_prover_from_scan(Prover_scan_result psr,
                                  int sine_tolerance,
                                  int sine_depth_val,
                                  int sine_max_axioms)
{
  Prover_input pi = safe_calloc(1, sizeof(struct prover_input));
  Scan_result scan = psr->scan;
  Prover_options options = psr->options;
  BOOL echo = psr->echo;
  int argc = psr->argc;
  char **argv = psr->argv;
  Tptp_input tptp = NULL;
  Plist p;
  BOOL sine_done = FALSE;

  pi->options = options;

  /* Phase 2: Decide if scan-based SInE applies. */
  {
    int sine_val = (sine_tolerance >= 0) ? sine_tolerance
                                         : parm(options->sine);
    int scan_n_axioms = scan->n_axioms;
    int eff_tolerance = 0;

    if (sine_val == -1) {
      if (scan_n_axioms > 128 &&
          (scan->n_goals > 0 || scan->has_neg_conj))
        eff_tolerance = 200;
    }
    else if (sine_val > 0 &&
             (scan->n_goals > 0 || scan->has_neg_conj)) {
      eff_tolerance = sine_val;
    }

    if (eff_tolerance > 0 && scan_n_axioms > 5000) {
      /* Scan-based SInE for large inputs */
      int eff_depth = (sine_depth_val >= 0) ? sine_depth_val
                                            : parm(options->sine_depth);
      int eff_max = (sine_max_axioms >= 0) ? sine_max_axioms
                                           : parm(options->sine_max_axioms);
      int wide_tol = (eff_depth == 0) ? eff_tolerance : 0;
      int *sel_depth, *loose_depth;
      BOOL *keep;
      int i, n_sel = 0, n_usa = 0, n_zapped = 0;

      if (eff_depth == 0) {
        eff_tolerance = 150;
        eff_depth = 3;
      }

      sel_depth = safe_calloc(scan->n_entries, sizeof(int));
      loose_depth = safe_calloc(scan->n_entries, sizeof(int));

      sine_filter_scan(scan->entries, scan->n_entries, scan->n_symbols,
                       eff_tolerance, wide_tol, eff_depth, eff_max,
                       sel_depth, loose_depth);

      /* Build keep[] array */
      keep = safe_calloc(scan->n_entries, sizeof(BOOL));
      for (i = 0; i < scan->n_entries; i++) {
        if (scan->entries[i].role == SCAN_ROLE_GOAL) {
          keep[i] = TRUE;
        }
        else if (sel_depth[i]) {
          keep[i] = TRUE;
          n_sel++;
        }
        else if (loose_depth[i]) {
          keep[i] = TRUE;
          n_usa++;
        }
        else {
          n_zapped++;
        }
      }

#ifdef DEBUG
      fprintf(stderr, "%% Scan SInE: parsing %d of %d formulas "
              "(%d tight + %d loose + %d goals, %d zapped)\n",
              n_sel + n_usa + scan->n_goals, scan->n_entries,
              n_sel, n_usa, scan->n_goals, n_zapped);
#endif

      tptp = parse_scanned_formulas(scan, keep);

      /* Set sine_depth attributes on parsed assumptions */
      {
        Plist ap = tptp->assumptions;
        int attr_id = sine_depth_attr();
        for (i = 0; i < scan->n_entries && ap != NULL; i++) {
          if (!keep[i] || scan->entries[i].role == SCAN_ROLE_GOAL)
            continue;
          {
            int d = sel_depth[i] ? sel_depth[i] : loose_depth[i];
            if (d > 0) {
              Formula f = (Formula) ap->v;
              f->attributes = set_int_attribute(f->attributes, attr_id, d);
            }
          }
          ap = ap->next;
        }
      }

      /* Partition assumptions into sos/usable */
      {
        Plist sos_result = NULL;
        Plist usable_result = NULL;
        Plist ap = tptp->assumptions;
        Plist nxt;
        for (i = 0; i < scan->n_entries && ap != NULL; i++) {
          if (!keep[i] || scan->entries[i].role == SCAN_ROLE_GOAL)
            continue;
          nxt = ap->next;
          ap->next = NULL;
          if (sel_depth[i] && sel_depth[i] <= 2) {
            sos_result = plist_cat(sos_result, ap);
          }
          else {
            usable_result = plist_cat(usable_result, ap);
          }
          ap = nxt;
        }
        pi->sos = sos_result;
        pi->usable = usable_result;
      }
      pi->goals = tptp->goals;
      pi->has_neg_conj = tptp->has_neg_conj;

      if (wide_tol > 0)
        fprintf(stdout, "\n%% SInE (scan): %d to sos (tol %.1fx), "
                "%d to usable (tol %.1fx), %d zapped, of %d axioms "
                "(depth %d).\n",
                n_sel, eff_tolerance / 100.0,
                n_usa, wide_tol / 100.0,
                n_zapped, scan_n_axioms, eff_depth);
      else
        fprintf(stdout, "\n%% SInE (scan): %d to sos, %d to usable, "
                "of %d axioms (tolerance %.2f, depth %d%s).\n",
                n_sel, n_usa, scan_n_axioms,
                eff_tolerance / 100.0, eff_depth,
                eff_depth == 0 ? " fixpoint" : "");

      /* Auto-enable sine_weight tuning */
      if (parm(options->sine_weight) == 0)
        assign_parm(options->sine_weight, 100, FALSE);
      if (parm(options->sine_weight) > 0) {
        if (parm(options->weight_part) == 0)
          assign_parm(options->weight_part, 2, FALSE);
        if (flag(options->input_sos_first))
          clear_flag(options->input_sos_first, FALSE);
      }

      sine_done = TRUE;
      safe_free(sel_depth);
      safe_free(loose_depth);
      safe_free(keep);

      tptp->assumptions = NULL;
      tptp->goals = NULL;
      free_scan_result(scan);
      psr->scan = NULL;
      safe_free(tptp);
      tptp = NULL;
    }
    else {
      /* Small input or SInE disabled: parse all from saved text */
      if (echo)
        printf("%% Parsing all %d formulas from scan data\n\n",
               scan->n_entries);
      tptp = parse_scanned_formulas(scan, NULL);

      pi->sos = tptp->assumptions;
      pi->goals = tptp->goals;
      pi->has_neg_conj = tptp->has_neg_conj;

      tptp->assumptions = NULL;
      tptp->goals = NULL;
      free_scan_result(scan);
      psr->scan = NULL;
      zap_tptp_input(tptp);
      tptp = NULL;
    }
  }

  /* TPTP provers exit on first proof */
  assign_parm(options->max_proofs, 1, FALSE);

  /* Echo formulas */
  if (echo) {
    printf("\nformulas(assumptions).\n");
    for (p = pi->sos; p; p = p->next) {
      printf("        ");
      fprint_formula(stdout, (Formula) p->v);
      printf(".\n");
    }
    if (pi->usable != NULL) {
      printf("end_of_list.\n\nformulas(usable).\n");
      for (p = pi->usable; p; p = p->next) {
        printf("        ");
        fprint_formula(stdout, (Formula) p->v);
        printf(".\n");
      }
    }
    printf("end_of_list.\n");

    if (pi->goals != NULL) {
      printf("\nformulas(goals).\n");
      for (p = pi->goals; p; p = p->next) {
        printf("        ");
        fprint_formula(stdout, (Formula) p->v);
        printf(".\n");
      }
      printf("end_of_list.\n");
    }
  }

  /* Gather symbols and declare functions/relations */
  {
    int sn = greatest_symnum() + 1;
    int *rcounts = safe_calloc(sn, sizeof(int));
    int *fcounts = safe_calloc(sn, sizeof(int));
    Ilist rsyms, fsyms;
    gather_symbols_in_formulas(pi->sos, rcounts, fcounts);
    gather_symbols_in_formulas(pi->usable, rcounts, fcounts);
    gather_symbols_in_formulas(pi->goals, rcounts, fcounts);
    rsyms = counts_to_set(rcounts, sn);
    fsyms = counts_to_set(fcounts, sn);
    safe_free(rcounts);
    safe_free(fcounts);
    declare_functions_and_relations(fsyms, rsyms);
    zap_ilist(fsyms);
    zap_ilist(rsyms);
  }

  if (echo)
    print_separator(stdout, "end of input", TRUE);

  /* Apply command-line overrides (max_seconds, max_megs, CNF limits) */
  {
    struct arg_options opts = get_command_line_args(argc, argv);
    process_command_line_args_2(opts, options);
  }

  if (!option_dependencies_state()) {
    printf("\n%% Enabling option dependencies (ignore applies only on input).\n");
    enable_option_dependencies();
  }

  /* SInE for small inputs (not already done by scan path) */
  if (!sine_done) {
    int sine_val = (sine_tolerance >= 0) ? sine_tolerance
                                         : parm(options->sine);
    int n_axioms = plist_count(pi->sos);
    int eff_tolerance = 0;

    if (sine_val == -1) {
      if (n_axioms > 128 && pi->goals != NULL)
        eff_tolerance = 200;
    }
    else if (sine_val > 0 && pi->goals != NULL) {
      eff_tolerance = sine_val;
    }

    if (eff_tolerance > 0) {
      int eff_depth = (sine_depth_val >= 0) ? sine_depth_val
                                            : parm(options->sine_depth);
      int wide_tol = (n_axioms > 5000 && eff_depth == 0)
                     ? eff_tolerance : 0;
      Plist selected = NULL;
      Plist usable_add = NULL;
      Plist unselected = NULL;
      int n_sel, n_usa, n_zapped;

      if (n_axioms > 5000 && eff_depth == 0) {
        eff_tolerance = 150;
        eff_depth = 3;
      }

      sine_filter(pi->sos, pi->goals,
                  eff_tolerance, wide_tol, eff_depth,
                  &selected, &usable_add, &unselected);

      n_sel = plist_count(selected);
      n_usa = plist_count(usable_add);
      n_zapped = n_axioms - n_sel - n_usa;

      pi->sos = selected;
      pi->usable = plist_cat(pi->usable, usable_add);

      for (p = unselected; p; p = p->next)
        zap_formula((Formula) p->v);
      zap_plist(unselected);

      if (wide_tol > 0)
        fprintf(stdout, "\n%% SInE: %d to sos (tol %.1fx), "
                "%d to usable (tol %.1fx), %d zapped, of %d axioms "
                "(depth %d).\n",
                n_sel, eff_tolerance / 100.0,
                n_usa, wide_tol / 100.0,
                n_zapped, n_axioms, eff_depth);
      else
        fprintf(stdout, "\n%% SInE: %d to sos, %d to usable, of %d axioms "
                "(tolerance %.2f, depth %d%s).\n",
                n_sel, n_usa, n_axioms,
                eff_tolerance / 100.0, eff_depth,
                eff_depth == 0 ? " fixpoint" : "");

      if (parm(options->sine_weight) == 0)
        assign_parm(options->sine_weight, 100, FALSE);
      if (parm(options->sine_weight) > 0) {
        if (parm(options->weight_part) == 0)
          assign_parm(options->weight_part, 2, FALSE);
        if (flag(options->input_sos_first))
          clear_flag(options->input_sos_first, FALSE);
      }
    }
  }

  /* Clausification */
  {
    Plist denials;

    pi->sos    = embed_formulas_in_topforms(pi->sos, TRUE);
    pi->usable = embed_formulas_in_topforms(pi->usable, TRUE);
    pi->demods = embed_formulas_in_topforms(pi->demods, TRUE);
    pi->hints  = embed_formulas_in_topforms(pi->hints, TRUE);
    pi->goals  = embed_formulas_in_topforms(pi->goals, FALSE);

    pi->has_goals = (pi->goals != NULL);

    /* Extract TPTP problem name */
    {
      const char *path = psr->tptp_file;
      if (path == NULL) {
        int n = which_string_member("-f", argv, argc);
        if (n >= 0 && n + 1 < argc) {
          int flen = strlen(argv[n + 1]);
          if (flen >= 2 && strcmp(argv[n + 1] + flen - 2, ".p") == 0)
            path = argv[n + 1];
        }
      }
      if (path != NULL) {
        const char *base = strrchr(path, '/');
        int len;
        base = (base != NULL) ? base + 1 : path;
        len = strlen(base);
        if (len >= 2 && strcmp(base + len - 2, ".p") == 0)
          len -= 2;
        if (len > 0) {
          char *name = safe_malloc(len + 1);
          memcpy(name, base, len);
          name[len] = '\0';
          pi->problem_name = name;
        }
      }
    }

    /* Enable SZS status output in fatal_error() and signal handlers */
    if (flag(pi->options->tptp_output)) {
      set_fatal_tptp_mode(TRUE, pi->problem_name);
      set_tptp_mode_for_sig();
    }

    if (echo)
      print_separator(stdout, "PROCESS NON-CLAUSAL FORMULAS", TRUE);
    {
      int echo_id = str_to_flag_id("echo_input");
      BOOL echo_clausify = echo && (echo_id == -1 ? TRUE : flag(echo_id));

      if (echo_clausify)
        printf("\n%% Formulas that are not ordinary clauses:\n");
      else if (echo)
        printf("\n%% Formulas that are not ordinary clauses: not echoed\n");

      /* Clausify can hit max_vars -- report as GaveUp, not Error */
      set_fatal_szs_status("GaveUp");

#ifdef DEBUG
      fprintf(stderr, "%% Clausifying sos (%d formulas)...\n",
              plist_count(pi->sos));
#endif
      pi->sos    = process_input_formulas(pi->sos, echo_clausify);
#ifdef DEBUG
      fprintf(stderr, "%% Clausifying usable (%d formulas)...\n",
              plist_count(pi->usable));
#endif
      pi->usable = process_input_formulas(pi->usable, echo_clausify);
      pi->demods = process_demod_formulas(pi->demods, echo_clausify);
      {
        int saved_limit = cnf_clause_limit();
        set_cnf_clause_limit(0);
        pi->hints  = process_input_formulas(pi->hints, echo_clausify);
        set_cnf_clause_limit(saved_limit);
      }
#ifdef DEBUG
      fprintf(stderr, "%% Clausifying goals...\n");
#endif
      denials    = process_goal_formulas(pi->goals, echo_clausify);

      set_fatal_szs_status(NULL);  /* reset to default for search phase */
    }

    pi->goals = NULL;
    pi->sos = plist_cat(pi->sos, denials);


#ifdef DEBUG
    fprintf(stderr, "%% Preprocessing done: %d sos, %d usable clauses.\n",
            plist_count(pi->sos), plist_count(pi->usable));
#endif

    if (echo)
      print_separator(stdout, "end of process non-clausal formulas", TRUE);
  }

  return pi;
}  /* std_prover_from_scan */


