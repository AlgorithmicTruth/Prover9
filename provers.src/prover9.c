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

#define PROVER_NAME     "Prover9"
#include "../VERSION_DATE.h"

#include "provers.h"
#include "features.h"
#include "dtree.h"
#include "strategy_config.h"

#include <unistd.h>
#include <sys/wait.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <signal.h>
#include <fcntl.h>

/*************
 *
 *   Strategy scheduling for TPTP mode.
 *
 *   Fork N children after clausification, each running search()
 *   with different options.  First child to find a proof wins.
 *
 *   Strategies come from the trained ML portfolio (strategy_data.h).
 *   The decision tree (dtree_data.h) picks the best strategy;
 *   remaining portfolio entries fill the other child slots.
 *
 *************/

/* Max array size for strategy arrays (compile-time). */
#define MAX_STRATEGY_CHILDREN NUM_PORTFOLIO_STRATS

/* auto_default is always the last portfolio entry */
#define AUTO_DEFAULT_IDX  (NUM_PORTFOLIO_STRATS - 1)  /* last entry */

/* Sliding-window (-cores N) constants */
#define CORES_MIN_SLICE   8   /* minimum seconds per child slice */
#define CHILD_OUTPUT_BUFSZ  (1024 * 1024)   /* 1 MB per strategy */

/* Suspended child record for sleep/wake scheduling */
struct suspended_child {
  pid_t pid;
  int   strat_idx;
  int   order_idx;     /* position in order[] (for hints_shm/output_shm lookup) */
};

/* Shared-memory output buffer for sleep/wake scheduler.
   One per strategy (indexed by order_idx, not slot).
   Children write stdout data here via fwopen/fopencookie callback. */
struct child_output {
  volatile int output_len;
  char buf[CHILD_OUTPUT_BUFSZ - 4];
};

/* Shared-memory progress hints for sleep/wake scheduler.
   One slot per possible child.  128 bytes = 2 Apple Silicon cache lines,
   avoids false sharing between adjacent child slots.
   All volatile int fields: single-word writes are atomic, no locks needed. */
struct child_hints {
  volatile int stage;            /* STAGE_* enum from search.h */
  volatile int given;            /* given clause count */
  volatile int kept;             /* kept clause count */
  volatile int sos_size;         /* SOS list length */
  volatile int usable_size;      /* usable list length */
  volatile int megs_used;        /* megs_malloced() value */
  volatile int prev_given;       /* given count at last suspend (set by parent) */
  int pad[25];                   /* pad to 128 bytes (32 ints x 4 = 128) */
};

/* File-scope pointer to this child's mmap slot (set in spawn_child) */
static volatile struct child_hints *my_hints = NULL;

/* File-scope pointer to this child's output buffer (set in spawn_child) */
static struct child_output *my_output = NULL;

/*************
 *
 *   child_exit()
 *
 *   Like exit_with_message() but uses _exit() instead of exit().
 *   Fork children must use _exit() to avoid flushing inherited
 *   stdio buffers and running parent atexit handlers.
 *
 *************/

static
void child_exit(int code)
{
  set_no_kill();  /* protect exit output from signal truncation */
  print_exit_message(stdout, code);
  _exit(code);
}

/*************
 *
 *   kill_child()
 *
 *   Gracefully kill a child process: wake if stopped (SIGCONT is a
 *   no-op on a running process), send SIGTERM (child can defer if
 *   mid-proof via no_kill), wait 100ms, then SIGKILL as a safety
 *   net if the child hasn't exited yet.
 *
 *************/

static
void kill_child(pid_t pid)
{
  kill(pid, SIGCONT);   /* wake if stopped, no-op if running */
  kill(pid, SIGTERM);
  usleep(100000);  /* 100ms grace for proof flush */
  if (waitpid(pid, NULL, WNOHANG) == 0) {
    kill(pid, SIGKILL);
    waitpid(pid, NULL, 0);
  }
}  /* kill_child */

/* File-scope slice duration for re-arming after SIGCONT resume. */
static int Suspend_slice_sec = 0;

/*************
 *
 *   suspend_handler()
 *
 *   SIGALRM handler for sleep/wake scheduling.
 *   Freezes the child process so the parent can resume it later.
 *   After SIGCONT resumes execution, re-arms a one-shot alarm for
 *   the next slice.  Uses alarm() which is async-signal-safe and
 *   only counts wall time while the child is actually running.
 *
 *************/

static
void suspend_handler(int sig)
{
  (void) sig;
  raise(SIGSTOP);
  /* Execution resumes here after parent sends SIGCONT.
     Re-arm one-shot alarm for the next slice. */
  alarm(Suspend_slice_sec);
}  /* suspend_handler */

/*************
 *
 *   arm_suspend_timer()
 *
 *   Register SIGALRM handler and arm a one-shot alarm for sleep/wake
 *   scheduling.  Uses wall-clock time (ITIMER_REAL / alarm()) because
 *   ITIMER_VIRTUAL is unreliable on some macOS versions.
 *
 *   One-shot (not repeating) so the timer does not fire while the
 *   child is SIGSTOP'd.  The handler re-arms after SIGCONT resume.
 *
 *   Safe in cores children because max_seconds=-1 prevents
 *   setup_timeout_signal() from arming its own ITIMER_REAL.
 *
 *************/

static
void arm_suspend_timer(int slice_sec)
{
  struct sigaction sa;

  Suspend_slice_sec = slice_sec;

  sa.sa_handler = suspend_handler;
  sa.sa_flags = SA_RESTART;
  sigemptyset(&sa.sa_mask);
  sigaction(SIGALRM, &sa, NULL);

  alarm(slice_sec);
}  /* arm_suspend_timer */

/*************
 *
 *   shm_progress_update()
 *
 *   Search_progress_fn callback: writes progress to this child's
 *   mmap slot.  Called from search.c at preprocessing stages and
 *   every 100th given clause.  NOT called from signal handlers.
 *
 *************/

static
void shm_progress_update(int stage, int given, int kept,
                          int sos_size, int usable_size, int megs)
{
  if (my_hints) {
    my_hints->stage       = stage;
    my_hints->given       = given;
    my_hints->kept        = kept;
    my_hints->sos_size    = sos_size;
    my_hints->usable_size = usable_size;
    my_hints->megs_used   = megs;
  }
}  /* shm_progress_update */

/*************
 *
 *   shm_write_fn()
 *
 *   Write callback for fwopen (macOS) / fopencookie (Linux).
 *   Copies data into the child's shared-memory output buffer.
 *   Silently stops copying when full, always returns len to
 *   prevent write errors in the child.
 *
 *************/

#ifdef __APPLE__

static
int shm_write_fn(void *cookie, const char *data, int len)
{
  struct child_output *out = (struct child_output *) cookie;
  int avail = (int) sizeof(out->buf) - out->output_len;
  if (avail > 0) {
    int n = len < avail ? len : avail;
    memcpy(out->buf + out->output_len, data, n);
    out->output_len += n;
  }
  return len;  /* always report success */
}

#else  /* Linux / glibc */

static
ssize_t shm_write_fn(void *cookie, const char *data, size_t len)
{
  struct child_output *out = (struct child_output *) cookie;
  int avail = (int) sizeof(out->buf) - out->output_len;
  if (avail > 0) {
    int n = (int) len < avail ? (int) len : avail;
    memcpy(out->buf + out->output_len, data, n);
    out->output_len += n;
  }
  return (ssize_t) len;
}

#endif

/*************
 *
 *   shm_stdout_open()
 *
 *   Create a write-only FILE* backed by the shared-memory output buffer.
 *   Portable: fwopen on macOS (BSD), fopencookie on Linux (glibc).
 *
 *************/

static
FILE *shm_stdout_open(struct child_output *out)
{
#ifdef __APPLE__
  return fwopen(out, shm_write_fn);
#else
  cookie_io_functions_t fns;
  memset(&fns, 0, sizeof(fns));
  fns.write = shm_write_fn;
  return fopencookie(out, "w", fns);
#endif
}

/*************
 *
 *   write_shm_to_fd()
 *
 *   Parent helper: write child's shared-memory output buffer to a
 *   file descriptor (typically saved_stdout).  Retry-safe write loop.
 *
 *************/

static
void write_shm_to_fd(struct child_output *out, int fd)
{
  int total = out->output_len;
  int written = 0;
  while (written < total) {
    ssize_t w = write(fd, out->buf + written, total - written);
    if (w <= 0)
      break;
    written += (int) w;
  }
}  /* write_shm_to_fd */

/*************
 *
 *   pick_best_suspended()
 *
 *   Choose the most productive suspended child to resume in Phase 2.
 *   Children making progress (high given/kept) get priority over
 *   children still in preprocessing.  Returns index into pool[],
 *   or -1 if pool is empty.
 *
 *************/

static
int pick_best_suspended(struct suspended_child *pool, int n,
                         struct child_hints *hints_shm,
                         int auto_default_idx)
{
  int best = -1;
  int best_score = -1;
  int j;
  for (j = 0; j < n; j++) {
    int oidx = pool[j].order_idx;
    int score;
    int stage = hints_shm[oidx].stage;
    int given = hints_shm[oidx].given;
    int delta = given - hints_shm[oidx].prev_given;

    if (stage < STAGE_SEARCHING) {
      /* Still in preprocessing -- lowest priority */
      score = 0;
      if (pool[j].strat_idx == auto_default_idx)
        score = 500;    /* beats other preprocessing-stuck children */
    }
    else {
      /* Score = progress since last resume (delta) + total given as tiebreak */
      score = 1000 + delta * 100 + given;
      if (pool[j].strat_idx == auto_default_idx)
        score += 10000; /* always highest priority */
    }
    if (score > best_score) {
      best_score = score;
      best = j;
    }
  }
  return best;
}  /* pick_best_suspended */

/*************
 *
 *   apply_strategy()
 *
 *   Modify options for portfolio strategy idx.
 *   All changes are silent (echo=FALSE).
 *
 *************/

static
void apply_strategy(Prover_options opt, int idx)
{
  const struct strategy_config *s = &Portfolio[idx];

  if (s->order == 0)
    assign_stringparm(opt->order, "lpo", FALSE);
  else if (s->order == 1)
    assign_stringparm(opt->order, "rpo", FALSE);
  else if (s->order == 2)
    assign_stringparm(opt->order, "kbo", FALSE);

  if (s->age_part >= 0)
    assign_parm(opt->age_part, s->age_part, FALSE);
  if (s->weight_part >= 0)
    assign_parm(opt->weight_part, s->weight_part, FALSE);
  if (s->max_weight >= 0)
    assign_floatparm(opt->max_weight, (double) s->max_weight, FALSE);
  if (s->sine_weight >= 0)
    assign_parm(opt->sine_weight, s->sine_weight, FALSE);

  if (s->binary_resolution == 1) set_flag(opt->binary_resolution, FALSE);
  else if (s->binary_resolution == 0) clear_flag(opt->binary_resolution, FALSE);

  if (s->hyper_resolution == 1) set_flag(opt->hyper_resolution, FALSE);
  else if (s->hyper_resolution == 0) clear_flag(opt->hyper_resolution, FALSE);

  if (s->ur_resolution == 1) set_flag(opt->ur_resolution, FALSE);
  else if (s->ur_resolution == 0) clear_flag(opt->ur_resolution, FALSE);

  if (s->paramodulation == 1) set_flag(opt->paramodulation, FALSE);
  else if (s->paramodulation == 0) clear_flag(opt->paramodulation, FALSE);

  if (s->multi_order_trial == 1) set_flag(opt->multi_order_trial, FALSE);
  else if (s->multi_order_trial == 0) clear_flag(opt->multi_order_trial, FALSE);

  if (s->process_initial_sos == 1) set_flag(opt->process_initial_sos, FALSE);
  else if (s->process_initial_sos == 0) clear_flag(opt->process_initial_sos, FALSE);

  if (s->back_subsume == 1) set_flag(opt->back_subsume, FALSE);
  else if (s->back_subsume == 0) clear_flag(opt->back_subsume, FALSE);

  if (s->lightest_first == 1) set_flag(opt->lightest_first, FALSE);
  else if (s->lightest_first == 0) clear_flag(opt->lightest_first, FALSE);

  if (s->breadth_first == 1) set_flag(opt->breadth_first, FALSE);
  else if (s->breadth_first == 0) clear_flag(opt->breadth_first, FALSE);

  if (s->safe_unit_conflict == 1) set_flag(opt->safe_unit_conflict, FALSE);
  else if (s->safe_unit_conflict == 0) clear_flag(opt->safe_unit_conflict, FALSE);

  if (s->factor == 1) set_flag(opt->factor, FALSE);
  else if (s->factor == 0) clear_flag(opt->factor, FALSE);

  if (s->unit_deletion == 1) set_flag(opt->unit_deletion, FALSE);
  else if (s->unit_deletion == 0) clear_flag(opt->unit_deletion, FALSE);

  if (s->para_units_only == 1) set_flag(opt->para_units_only, FALSE);
  else if (s->para_units_only == 0) clear_flag(opt->para_units_only, FALSE);

  if (s->back_demod == 1) set_flag(opt->back_demod, FALSE);
  else if (s->back_demod == 0) clear_flag(opt->back_demod, FALSE);

  if (s->ordered_res == 1) set_flag(opt->ordered_res, FALSE);
  else if (s->ordered_res == 0) clear_flag(opt->ordered_res, FALSE);

  if (s->ordered_para == 1) set_flag(opt->ordered_para, FALSE);
  else if (s->ordered_para == 0) clear_flag(opt->ordered_para, FALSE);

  if (s->literal_selection == 0)
    assign_stringparm(opt->literal_selection, "max_negative", FALSE);
  else if (s->literal_selection == 1)
    assign_stringparm(opt->literal_selection, "all_negative", FALSE);

  if (s->nest_penalty >= 0)
    assign_floatparm(opt->nest_penalty, (double) s->nest_penalty, FALSE);
  if (s->depth_penalty >= 0)
    assign_floatparm(opt->depth_penalty, (double) s->depth_penalty, FALSE);

  /* Disable periodic checkpoints in strategy children. */
  assign_parm(opt->checkpoint_minutes, -1, FALSE);
}  /* apply_strategy */

/*************
 *
 *   ml_classify()
 *
 *   Run ML decision tree on scan result to pick best portfolio strategy.
 *
 *************/

static
int ml_classify(Scan_result scan, const char *filename)
{
  int fv[NUM_FEATURES];
  int pick;
  extract_features(scan, fv);
  set_domain_hash(fv, filename);
  pick = dtree_classify(fv);
  if (pick < 0 || pick >= NUM_PORTFOLIO_STRATS) pick = 0;
  return pick;
}  /* ml_classify */

/*************
 *
 *   ml_rank()
 *
 *   Run ML decision tree on scan result to get full per-leaf strategy ranking.
 *   Sets *out_len to the number of strategies in the ranking.
 *   Returns NULL if ranking data is not available.
 *
 *************/

static
const short *ml_rank(Scan_result scan, const char *filename, int *out_len)
{
  int fv[NUM_FEATURES];
  extract_features(scan, fv);
  set_domain_hash(fv, filename);
  *out_len = dtree_num_strats();
  return dtree_rank(fv);
}  /* ml_rank */


/* [removed: ml_sweep_loop, ml_sweep_loop_from_scan, parent_poll_dual_track,
   strategy_schedule_search, strategy_schedule_from_scan, sweep_search,
   sweep_from_scan -- superseded by -cores N sliding-window scheduler] */


/*************
 *
 *   build_cores_order()
 *
 *   Build strategy execution order for -cores mode:
 *     order[0] = AUTO_DEFAULT_IDX (always first, never suspended)
 *     order[1..] = per-leaf ML ranking (problem-specific priority),
 *                  skipping AUTO_DEFAULT_IDX and duplicates.
 *     Fallback for remaining slots: Coverage_rank order.
 *
 *   ml_ranking: per-leaf ranking from dtree_rank() (may be NULL).
 *   ml_ranking_len: number of entries in ml_ranking.
 *   n = NUM_PORTFOLIO_STRATS.  order[] must have room for n entries.
 *
 *************/

static
void build_cores_order(const short *ml_ranking, int ml_ranking_len,
                       int *order, int n)
{
  int seen[NUM_PORTFOLIO_STRATS];
  int i, j, k;
  int best_rank, best_idx;

  if (n < 1) return;

  memset(seen, 0, sizeof(seen));

  /* Slot 0: auto_default (strongest single strategy, always first) */
  order[0] = AUTO_DEFAULT_IDX;
  seen[AUTO_DEFAULT_IDX] = 1;
  j = 1;

  /* Walk per-leaf ranking: problem-specific strategy priority */
  if (ml_ranking != NULL) {
    for (i = 0; i < ml_ranking_len && j < n; i++) {
      int s = (int) ml_ranking[i];
      if (s < 0 || s >= NUM_PORTFOLIO_STRATS) continue;
      if (seen[s]) continue;
      order[j++] = s;
      seen[s] = 1;
    }
  }

  /* Fill remaining slots from Coverage_rank (static fallback).
     Simple selection sort (n<=NUM_PORTFOLIO_STRATS). */
  for (k = 0; k < n && j < n; k++) {
    best_rank = INT_MAX;
    best_idx = -1;
    for (i = 0; i < NUM_PORTFOLIO_STRATS; i++) {
      if (seen[i]) continue;
      if (Coverage_rank[i] >= best_rank) continue;
      best_rank = Coverage_rank[i];
      best_idx = i;
    }
    if (best_idx < 0) break;
    order[j++] = best_idx;
    seen[best_idx] = 1;
  }
}  /* build_cores_order */

/*************
 *
 *   spawn_child()
 *
 *   Fork a child process to run strategy order[si] in the given slot.
 *   The child redirects stdout to a shared-memory buffer via
 *   fwopen/fopencookie, applies the strategy, disables internal
 *   timeout (max_seconds=-1), arms SIGALRM for sleep/wake slicing,
 *   and calls search().
 *
 *   mode: 0 = post-clausify (use input + search)
 *         1 = pre-SInE      (use psr + std_prover_from_scan + search)
 *
 *   Returns child PID to parent, or 0 on fork failure.
 *
 *************/

static
pid_t spawn_child(int slot, int si, int order_idx, int slice_sec,
                  int saved_stdout,
                  struct child_output *output_shm,
                  Prover_input input,
                  Prover_scan_result psr,
                  struct child_hints *hints_shm)
{
  pid_t cpid;

  fflush(stdout);
  fflush(stderr);

  cpid = fork();
  if (cpid < 0) {
    fprintf(stderr, "%% Cores: fork failed for slot %d\n", slot);
    return 0;
  }

  if (cpid == 0) {
    /* ---- Child process ---- */
    int devnull_fd;
    FILE *shm_fp;
    close(saved_stdout);

    /* Redirect fd 1 to /dev/null as safety net for stray raw writes */
    devnull_fd = open("/dev/null", O_WRONLY);
    if (devnull_fd >= 0) {
      dup2(devnull_fd, STDOUT_FILENO);
      close(devnull_fd);
    }

    /* Set up shared-memory output buffer (unbuffered so _exit() loses
       nothing; every fprintf/printf immediately invokes shm_write_fn) */
    if (output_shm) {
      my_output = &output_shm[order_idx];
      my_output->output_len = 0;
      shm_fp = shm_stdout_open(my_output);
      if (shm_fp) {
        setbuf(shm_fp, NULL);
        stdout = shm_fp;
      }
    }

    init_wallclock();

    /* Set up shared-memory progress reporting (indexed by order position).
       Always set callback: it also handles deferred ALRM arming. */
    if (hints_shm) {
      my_hints = &hints_shm[order_idx];
      memset((void *) my_hints, 0, sizeof(struct child_hints));
    }
    set_progress_callback(shm_progress_update);

    /* Arm SIGALRM for the full slice (includes preprocessing).
       Training used total wall time, so preprocessing counts.
       auto_default (slot 0) runs continuously -- no suspend timer.
       The parent's backstop handles its lifetime. */
    if (si != AUTO_DEFAULT_IDX)
      arm_suspend_timer(slice_sec);

    if (input != NULL) {
      /* Mode 0: post-clausify */
      Prover_results results;
      apply_strategy(input->options, si);
      assign_parm(input->options->max_seconds, -1, FALSE);
      assign_parm(input->options->cores, 0, FALSE);  /* child, not parent */
      results = search(input);
      child_exit(results->return_code);
    }
    else {
      /* Mode 1: pre-SInE */
      const struct strategy_config *s = &Portfolio[si];
      Prover_input child_input;
      Prover_results results;
      apply_strategy(psr->options, si);
      assign_parm(psr->options->max_seconds, -1, FALSE);
      assign_parm(psr->options->cores, 0, FALSE);  /* child, not parent */

      if (my_hints)
        my_hints->stage = STAGE_SINE_FILTER;

      child_input = std_prover_from_scan(psr,
                                         s->sine_tolerance,
                                         s->sine_depth,
                                         s->sine_max_axioms);

      if (my_hints)
        my_hints->stage = STAGE_INIT;

      results = search(child_input);
      child_exit(results->return_code);
    }
  }

  /* Parent */
  return cpid;
}  /* spawn_child */

/*************
 *
 *   cores_emit_no_proof()
 *
 *   Emit SZS status line for no-proof result and exit.
 *   Used by both cores_search() and cores_from_scan().
 *
 *************/

static
void cores_emit_no_proof(int saved_stdout, int best_code,
                         Prover_options options, const char *problem_name)
{
  const char *szs;
  FILE *fp;

  if (best_code < 0)
    best_code = MAX_SECONDS_EXIT;

  switch (best_code) {
  case SOS_EMPTY_EXIT:
  case MAX_GIVEN_EXIT:
  case MAX_KEPT_EXIT:
  case ACTION_EXIT:
    szs = "GaveUp"; break;
  case MAX_SECONDS_EXIT:
    szs = "Timeout"; break;
  case MAX_MEGS_EXIT:
    szs = "MemoryOut"; break;
  default:
    szs = "Error"; break;
  }

  fp = fdopen(saved_stdout, "w");
  if (fp != NULL) {
    if (flag(options->tptp_output)) {
      if (problem_name)
        fprintf(fp, "\n%% SZS status %s for %s\n", szs, problem_name);
      else
        fprintf(fp, "\n%% SZS status %s\n", szs);
    }
    else {
      fprintf(fp, "\nSEARCH FAILED\n");
    }
    fflush(fp);
    fclose(fp);
  }
  else {
    close(saved_stdout);
  }

#ifdef DEBUG
  fprintf(stderr, "%% Cores: no proof found (%s)\n", szs);
#endif
  exit(best_code);
}  /* cores_emit_no_proof */

/*************
 *
 *   cores_poll_loop()
 *
 *   Sleep/wake sliding-window scheduler.  Maintains up to N children
 *   running concurrently.  Children self-suspend via SIGALRM/SIGSTOP
 *   after each CPU-time slice, preserving search state.
 *
 *   Phase 1 (Breadth): Try every strategy with a short slice.
 *     When a child self-stops, move it to the suspended pool and
 *     launch the next unstarted strategy in that slot.
 *   Phase 2 (Depth): All strategies tried at least once.
 *     Resume suspended children round-robin for additional slices.
 *
 *   mode: 0 = post-clausify (use input + apply_strategy + search)
 *         1 = pre-SInE      (use psr + from_scan per child)
 *
 *   Returns: MAX_PROOFS_EXIT if proof found, otherwise best exit code.
 *   On proof, copies winner output to saved_stdout and kills all others.
 *
 *************/

static
int cores_poll_loop(int N, int *order, int num_strats, int phase1_limit,
                    int per_child_sec,
                    int saved_stdout,
                    Prover_input input,        /* non-NULL for mode 0 */
                    Prover_scan_result psr,     /* non-NULL for mode 1 */
                    int total_deadline,
                    struct child_hints *hints_shm,
                    int per_child_megs_budget,
                    struct child_output *output_shm)
{
  pid_t *slots;          /* PID in each slot (0 = empty) */
  int *slot_strat;       /* which strategy index each slot runs */
  int *slot_oidx;        /* order[] index for strategy in each slot */
  int next;              /* index into order[] for next strategy to launch */
  int best_code;
  int i;
  unsigned start_time;

  /* Suspended pool for sleep/wake scheduling (sized for phase1_limit) */
  struct suspended_child *suspended;
  int n_suspended;

  slots = calloc(N, sizeof(pid_t));
  slot_strat = calloc(N, sizeof(int));
  slot_oidx = calloc(N, sizeof(int));
  suspended = calloc(phase1_limit, sizeof(struct suspended_child));

  next = 0;
  best_code = -1;
  n_suspended = 0;
  start_time = absolute_wallclock();

  /* Initial fill: launch up to N children.
     auto_default gets full time budget (never self-suspends), keeping
     its dedicated slot for the entire run.  Other strategies get the
     normal per_child_sec slice and cycle through the remaining slots. */
  for (i = 0; i < N && next < phase1_limit; i++) {
    int si = order[next];
    int slice = (si == AUTO_DEFAULT_IDX) ? total_deadline : per_child_sec;
    pid_t cpid = spawn_child(i, si, next, slice, saved_stdout,
                             output_shm, input, psr, hints_shm);
    if (cpid > 0) {
      slots[i] = cpid;
      slot_strat[i] = si;
      slot_oidx[i] = next;

#ifdef DEBUG
      fprintf(stderr, "%% Cores slot %d [pid %d]: %s (%ds slice)\n",
              i, (int) cpid, Portfolio[si].name, slice);
#endif
    }
    next++;
  }

  /* Main polling loop */
  while (1) {
    int all_empty;
    int elapsed;

    /* Check backstop deadline */
    elapsed = (int)(absolute_wallclock() - start_time);
    if (total_deadline > 0 && elapsed >= total_deadline) {

#ifdef DEBUG
      fprintf(stderr, "%% Cores: backstop deadline (%ds) reached\n",
              total_deadline);
#endif
      /* Kill all running children */
      for (i = 0; i < N; i++) {
        if (slots[i] > 0) {
          kill_child(slots[i]);
          slots[i] = 0;
        }
      }
      /* Kill all suspended children */
      for (i = 0; i < n_suspended; i++)
        kill_child(suspended[i].pid);
      n_suspended = 0;
      break;
    }

    /* Poll each slot */
    for (i = 0; i < N; i++) {
      int status;
      pid_t wpid;

      if (slots[i] <= 0)
        continue;

      wpid = waitpid(slots[i], &status, WNOHANG | WUNTRACED);

      if (wpid == 0)
        continue;  /* still running */

      if (wpid < 0) {
        /* child already gone */
        slots[i] = 0;
        continue;
      }

      if (WIFSTOPPED(status)) {
        /* Child self-suspended (SIGALRM -> SIGSTOP) */
        int oidx = slot_oidx[i];

#ifdef DEBUG
        fprintf(stderr, "%% Cores slot %d (%s) [pid %d]: suspended"
                " (stage=%d given=%d kept=%d megs=%d)\n",
                i, Portfolio[slot_strat[i]].name, (int) slots[i],
                hints_shm ? hints_shm[oidx].stage : -1,
                hints_shm ? hints_shm[oidx].given : -1,
                hints_shm ? hints_shm[oidx].kept  : -1,
                hints_shm ? hints_shm[oidx].megs_used : -1);
#endif

        /* Memory ejection: kill children exceeding budget */
        if (hints_shm && per_child_megs_budget > 0 &&
            hints_shm[oidx].megs_used > per_child_megs_budget) {
#ifdef DEBUG
          fprintf(stderr, "%% Cores: killed s%d (slot %d): "
                  "%d MB > %d MB budget\n",
                  slot_strat[i], i,
                  hints_shm[oidx].megs_used, per_child_megs_budget);
#endif
          kill_child(slots[i]);
          slots[i] = 0;
          /* Don't add to suspended pool -- fall through to fill slot */
        }
        else {
          /* Move to suspended pool */
          if (n_suspended < phase1_limit) {
            /* Snapshot progress at suspend time */
            if (hints_shm)
              hints_shm[oidx].prev_given = hints_shm[oidx].given;
            suspended[n_suspended].pid = slots[i];
            suspended[n_suspended].strat_idx = slot_strat[i];
            suspended[n_suspended].order_idx = oidx;
            n_suspended++;
          }
          else {
            /* Pool full -- kill this child */
            kill_child(slots[i]);
          }
        }
        slots[i] = 0;

        /* Fill slot: Phase 1 (new strategy) or Phase 2 (resume suspended) */
        if (next < phase1_limit) {
          /* Phase 1: launch next unstarted strategy */
          int si = order[next];
          pid_t cpid = spawn_child(i, si, next, per_child_sec, saved_stdout,
                                   output_shm, input, psr, hints_shm);
          if (cpid > 0) {
            slots[i] = cpid;
            slot_strat[i] = si;
            slot_oidx[i] = next;

#ifdef DEBUG
            fprintf(stderr, "%% Cores slot %d [pid %d]: %s (%ds slice)\n",
                    i, (int) cpid, Portfolio[si].name, per_child_sec);
#endif
          }
          next++;
        }
        else if (n_suspended > 0) {
          /* Phase 2: resume best suspended child (priority-based) */
          int pick;
          int j;
          pid_t rpid;
          int rsi, roidx;

          if (hints_shm)
            pick = pick_best_suspended(suspended, n_suspended, hints_shm,
                                       AUTO_DEFAULT_IDX);
          else
            pick = 0;  /* FIFO fallback */

          if (pick < 0)
            pick = 0;

          rpid  = suspended[pick].pid;
          rsi   = suspended[pick].strat_idx;
          roidx = suspended[pick].order_idx;

          /* Remove from pool by shifting elements after pick */
          for (j = pick + 1; j < n_suspended; j++)
            suspended[j-1] = suspended[j];
          n_suspended--;

          slots[i] = rpid;
          slot_strat[i] = rsi;
          slot_oidx[i] = roidx;
          kill(rpid, SIGCONT);
#ifdef DEBUG
          fprintf(stderr, "%% Cores slot %d [pid %d]: resumed %s"
                  " (given=%d)\n",
                  i, (int) rpid, Portfolio[rsi].name,
                  hints_shm ? hints_shm[roidx].given : -1);
#endif
        }
        continue;
      }

      /* Child exited normally */
      {
        int child_code;
        if (WIFEXITED(status))
          child_code = WEXITSTATUS(status);
        else
          child_code = FATAL_EXIT;


#ifdef DEBUG
        fprintf(stderr, "%% Cores slot %d (%s): exit %d (%s)\n",
                i, Portfolio[slot_strat[i]].name, child_code,
                child_code == MAX_PROOFS_EXIT ? "proof" :
                child_code == SOS_EMPTY_EXIT ? "sos_empty" : "other");
#endif

        if (child_code == MAX_PROOFS_EXIT) {
          /* Proof found -- kill all others + suspended, copy output */
          int j;
          for (j = 0; j < N; j++) {
            if (j != i && slots[j] > 0) {
              kill_child(slots[j]);
              slots[j] = 0;
            }
          }
          for (j = 0; j < n_suspended; j++)
            kill_child(suspended[j].pid);
          n_suspended = 0;

          if (output_shm)
            write_shm_to_fd(&output_shm[slot_oidx[i]], saved_stdout);

#ifdef DEBUG
          fprintf(stderr, "%% Cores winner: slot %d (%s)\n",
                  i, Portfolio[slot_strat[i]].name);
#endif

          free(slots);
          free(slot_strat);
          free(slot_oidx);
          free(suspended);
          return MAX_PROOFS_EXIT;
        }

        /* Track best non-proof exit code */
        if (best_code < 0)
          best_code = child_code;
        else if (child_code == SOS_EMPTY_EXIT)
          best_code = SOS_EMPTY_EXIT;
        else if (child_code == MAX_SECONDS_EXIT &&
                 best_code != SOS_EMPTY_EXIT)
          best_code = MAX_SECONDS_EXIT;

        slots[i] = 0;

        /* Fill slot: Phase 1 (new strategy) or Phase 2 (resume) */
        if (next < phase1_limit) {
          int si = order[next];
          pid_t cpid = spawn_child(i, si, next, per_child_sec, saved_stdout,
                                   output_shm, input, psr, hints_shm);
          if (cpid > 0) {
            slots[i] = cpid;
            slot_strat[i] = si;
            slot_oidx[i] = next;

#ifdef DEBUG
            fprintf(stderr, "%% Cores slot %d [pid %d]: %s (%ds slice)\n",
                    i, (int) cpid, Portfolio[si].name, per_child_sec);
#endif
          }
          next++;
        }
        else if (n_suspended > 0) {
          /* Phase 2: resume best suspended child (priority-based) */
          int pick;
          int j;
          pid_t rpid;
          int rsi, roidx;

          if (hints_shm)
            pick = pick_best_suspended(suspended, n_suspended, hints_shm,
                                       AUTO_DEFAULT_IDX);
          else
            pick = 0;

          if (pick < 0)
            pick = 0;

          rpid  = suspended[pick].pid;
          rsi   = suspended[pick].strat_idx;
          roidx = suspended[pick].order_idx;

          for (j = pick + 1; j < n_suspended; j++)
            suspended[j-1] = suspended[j];
          n_suspended--;

          slots[i] = rpid;
          slot_strat[i] = rsi;
          slot_oidx[i] = roidx;
          kill(rpid, SIGCONT);
#ifdef DEBUG
          fprintf(stderr, "%% Cores slot %d [pid %d]: resumed %s"
                  " (given=%d)\n",
                  i, (int) rpid, Portfolio[rsi].name,
                  hints_shm ? hints_shm[roidx].given : -1);
#endif
        }
      }
    }

    /* Check if all slots are empty and no more work */
    all_empty = 1;
    for (i = 0; i < N; i++) {
      if (slots[i] > 0) { all_empty = 0; break; }
    }
    if (all_empty && next >= phase1_limit && n_suspended == 0)
      break;

    usleep(10000);  /* 10ms poll */
  }

  free(slots);
  free(slot_strat);
  free(slot_oidx);
  free(suspended);
  return best_code;
}  /* cores_poll_loop */

/*************
 *
 *   cores_search()
 *
 *   Entry point for -cores N with small inputs (<=5000 axioms).
 *   Parent does SInE + clausify once, then runs sliding-window.
 *   Does not return (calls exit()).
 *
 *************/

static
void cores_search(Prover_input input, const short *ml_ranking,
                  int ml_ranking_len, int max_strats_arg, int slice_arg)
{
  int N = parm(input->options->cores);
  int total_time = parm(input->options->max_seconds);
  int max_megs_val = parm(input->options->max_megs);
  int num_strats = NUM_PORTFOLIO_STRATS;
  int min_slice = (slice_arg > 0) ? slice_arg : CORES_MIN_SLICE;
  int phase1_limit;
  int per_child_sec;
  int per_child_megs;
  int *order;
  int saved_stdout;
  int result;
  struct child_hints *hints_shm;
  struct child_output *output_shm;

  if (total_time <= 0 || N <= 0)
    return;  /* fall through to single strategy */

  /* Phase 1 limit: -strategies N overrides, else automatic formula */
  if (max_strats_arg > 0) {
    phase1_limit = max_strats_arg;
    if (phase1_limit > num_strats)
      phase1_limit = num_strats;
  }
  else {
    /* Default: use half the wall-clock budget for breadth, half for depth */
    phase1_limit = (total_time * N) / (2 * min_slice);
    if (phase1_limit > num_strats)
      phase1_limit = num_strats;
  }
  if (phase1_limit < N)
    phase1_limit = N;

  /* Compute per-child time slice: short slices for Phase 1 breadth,
     full time only when all strategies fit in parallel. */
  if (phase1_limit <= N)
    per_child_sec = total_time;  /* all fit in parallel, no time-slicing */
  else
    per_child_sec = min_slice;

  /* Per-child memory budget: only enforce when max_megs is explicitly
     set to a competition-appropriate value (<=8192 MB). */
  if (max_megs_val > 0 && max_megs_val <= 8192)
    per_child_megs = max_megs_val / (num_strats > N ? num_strats : N);
  else
    per_child_megs = 0;  /* no budget enforcement */

  order = malloc(num_strats * sizeof(int));
  build_cores_order(ml_ranking, ml_ranking_len, order, num_strats);

  saved_stdout = dup(STDOUT_FILENO);

  /* Allocate shared-memory progress hints (sized for phase1_limit) */
  hints_shm = (struct child_hints *) mmap(NULL,
      phase1_limit * sizeof(struct child_hints),
      PROT_READ | PROT_WRITE,
      MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (hints_shm == MAP_FAILED)
    hints_shm = NULL;
  else
    memset(hints_shm, 0, phase1_limit * sizeof(struct child_hints));

  /* Allocate shared-memory output buffers (1 MB per strategy) */
  output_shm = (struct child_output *) mmap(NULL,
      phase1_limit * sizeof(struct child_output),
      PROT_READ | PROT_WRITE,
      MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (output_shm == MAP_FAILED)
    output_shm = NULL;


#ifdef DEBUG
  fprintf(stderr, "%% Cores: %d slots, %d/%d strategies, %ds slice, %ds total\n",
          N, phase1_limit, num_strats, per_child_sec, total_time);
#endif
  fflush(stdout);
  fflush(stderr);

  /* Disarm parent's SIGALRM so the poll loop manages its own timing.
     Children re-arm their own timers via setup_timeout_signal(). */
  {
    struct itimerval disarm;
    memset(&disarm, 0, sizeof(disarm));
    setitimer(ITIMER_REAL, &disarm, NULL);
  }

  result = cores_poll_loop(N, order, num_strats, phase1_limit, per_child_sec,
                           saved_stdout, input, NULL,
                           total_time + 2,
                           hints_shm, per_child_megs, output_shm);
  free(order);

  if (hints_shm)
    munmap(hints_shm, phase1_limit * sizeof(struct child_hints));
  if (output_shm)
    munmap(output_shm, phase1_limit * sizeof(struct child_output));

  if (result == MAX_PROOFS_EXIT) {
    close(saved_stdout);
    exit(MAX_PROOFS_EXIT);
  }

  cores_emit_no_proof(saved_stdout, result,
                      input->options, input->problem_name);
  /* Does not return */
}  /* cores_search */

/*************
 *
 *   cores_from_scan()
 *
 *   Entry point for -cores N with large inputs (>5000 axioms).
 *   Fork before SInE/parse/clausify so each child can apply its own
 *   SInE parameters.  Does not return (calls exit()).
 *
 *************/

static
void cores_from_scan(Prover_scan_result psr, const short *ml_ranking,
                     int ml_ranking_len, int max_strats_arg, int slice_arg)
{
  int N = parm(psr->options->cores);
  int total_time = parm(psr->options->max_seconds);
  int max_megs_val = parm(psr->options->max_megs);
  int num_strats = NUM_PORTFOLIO_STRATS;
  int min_slice = (slice_arg > 0) ? slice_arg : CORES_MIN_SLICE;
  int phase1_limit;
  int per_child_sec;
  int per_child_megs;
  int *order;
  int saved_stdout;
  int result;
  const char *pname = NULL;
  char pname_buf[256];
  struct child_hints *hints_shm;
  struct child_output *output_shm;

  if (total_time <= 0 || N <= 0)
    return;  /* fall through to single strategy */

  /* Phase 1 limit: -strategies N overrides, else automatic formula */
  if (max_strats_arg > 0) {
    phase1_limit = max_strats_arg;
    if (phase1_limit > num_strats)
      phase1_limit = num_strats;
  }
  else {
    /* Default: use half the wall-clock budget for breadth, half for depth */
    phase1_limit = (total_time * N) / (2 * min_slice);
    if (phase1_limit > num_strats)
      phase1_limit = num_strats;
  }
  if (phase1_limit < N)
    phase1_limit = N;

  /* Compute per-child time slice: short slices for Phase 1 breadth,
     full time only when all strategies fit in parallel. */
  if (phase1_limit <= N)
    per_child_sec = total_time;  /* all fit in parallel, no time-slicing */
  else
    per_child_sec = min_slice;

  /* Per-child memory budget: only enforce when max_megs is explicitly
     set to a competition-appropriate value (<=8192 MB). */
  if (max_megs_val > 0 && max_megs_val <= 8192)
    per_child_megs = max_megs_val / (num_strats > N ? num_strats : N);
  else
    per_child_megs = 0;  /* no budget enforcement */

  order = malloc(num_strats * sizeof(int));
  build_cores_order(ml_ranking, ml_ranking_len, order, num_strats);

  saved_stdout = dup(STDOUT_FILENO);

  /* Extract problem name for SZS output */
  if (psr->tptp_file != NULL) {
    const char *base = strrchr(psr->tptp_file, '/');
    int len;
    base = (base != NULL) ? base + 1 : psr->tptp_file;
    len = strlen(base);
    if (len >= 2 && strcmp(base + len - 2, ".p") == 0)
      len -= 2;
    if (len > 0 && len < (int) sizeof(pname_buf)) {
      memcpy(pname_buf, base, len);
      pname_buf[len] = '\0';
      pname = pname_buf;
    }
  }

  /* Allocate shared-memory progress hints (sized for phase1_limit) */
  hints_shm = (struct child_hints *) mmap(NULL,
      phase1_limit * sizeof(struct child_hints),
      PROT_READ | PROT_WRITE,
      MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (hints_shm == MAP_FAILED)
    hints_shm = NULL;
  else
    memset(hints_shm, 0, phase1_limit * sizeof(struct child_hints));

  /* Allocate shared-memory output buffers (1 MB per strategy) */
  output_shm = (struct child_output *) mmap(NULL,
      phase1_limit * sizeof(struct child_output),
      PROT_READ | PROT_WRITE,
      MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (output_shm == MAP_FAILED)
    output_shm = NULL;


#ifdef DEBUG
  fprintf(stderr, "%% Cores (from scan): %d slots, %d/%d strategies, "
          "%ds slice, %ds total\n",
          N, phase1_limit, num_strats, per_child_sec, total_time);
#endif
  fflush(stdout);
  fflush(stderr);

  /* Disarm parent's SIGALRM so the poll loop manages its own timing. */
  {
    struct itimerval disarm;
    memset(&disarm, 0, sizeof(disarm));
    setitimer(ITIMER_REAL, &disarm, NULL);
  }

  result = cores_poll_loop(N, order, num_strats, phase1_limit, per_child_sec,
                           saved_stdout, NULL, psr,
                           total_time + 2,
                           hints_shm, per_child_megs, output_shm);
  free(order);

  if (hints_shm)
    munmap(hints_shm, phase1_limit * sizeof(struct child_hints));
  if (output_shm)
    munmap(output_shm, phase1_limit * sizeof(struct child_output));

  if (result == MAX_PROOFS_EXIT) {
    close(saved_stdout);
    exit(MAX_PROOFS_EXIT);
  }

  cores_emit_no_proof(saved_stdout, result, psr->options, pname);
  /* Does not return */
}  /* cores_from_scan */

/*************
 *
 *    main -- basic prover
 *
 *************/

int main(int argc, char **argv)
{
  Prover_input input;
  Prover_results results;
  char *saved_command;
  BOOL tptp_mode = FALSE;
  BOOL nosine = FALSE;
  BOOL nomem = FALSE;
  int force_strategy = -1;  /* -strategy N: force portfolio index */
  int max_strategies = -1;  /* -strategies N: cap Phase 1 breadth */
  int slice_sec = -1;       /* -slice N: per-child time slice override */

  /* Save original command line before any argv mutation. */
  saved_command = build_command_string(argc, argv);

  /* Pre-scan for -strategy/-strategies N (neutralizes argv entries) */
  {
    int i;
    for (i = 1; i < argc; i++) {
      if (strcmp(argv[i], "-strategy") == 0 && i + 1 < argc) {
        force_strategy = atoi(argv[i + 1]);
        if (force_strategy < 0 || force_strategy >= NUM_PORTFOLIO_STRATS)
          force_strategy = 0;
        argv[i] = "-_";
        argv[i + 1] = "-_";
        i++;
      }
      else if (strcmp(argv[i], "-strategies") == 0 && i + 1 < argc) {
        max_strategies = atoi(argv[i + 1]);
        if (max_strategies < 1)
          max_strategies = 1;
        if (max_strategies > NUM_PORTFOLIO_STRATS)
          max_strategies = NUM_PORTFOLIO_STRATS;
        argv[i] = "-_";
        argv[i + 1] = "-_";
        i++;
      }
      else if (strcmp(argv[i], "-slice") == 0 && i + 1 < argc) {
        slice_sec = atoi(argv[i + 1]);
        if (slice_sec < 1)
          slice_sec = 1;
        argv[i] = "-_";
        argv[i + 1] = "-_";
        i++;
      }
    }
  }

  /* Quick pre-scan for TPTP indicators to decide banner format.
     -ladr_out overrides: use native banner even with TPTP input. */
  {
    int i;
    BOOL ladr_out = FALSE;
    for (i = 1; i < argc; i++) {
      if (strcmp(argv[i], "-ladr_out") == 0 ||
          strcmp(argv[i], "-ladr-out") == 0) {
        ladr_out = TRUE;
      }
    }
    if (!ladr_out) {
      for (i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-tptp") == 0 || strcmp(argv[i], "-tptp_out") == 0) {
          tptp_mode = TRUE;
          break;
        }
        if (strcmp(argv[i], "-f") == 0 && i + 1 < argc) {
          int len = strlen(argv[i+1]);
          if (len >= 2 && strcmp(argv[i+1] + len - 2, ".p") == 0)
            tptp_mode = TRUE;
        }
        /* Bare positional .p file (no -f flag) */
        if (argv[i][0] != '-') {
          int len = strlen(argv[i]);
          if (len >= 2 && strcmp(argv[i] + len - 2, ".p") == 0)
            tptp_mode = TRUE;
        }
      }
    }
  }

  /* Check for -nosine flag */
  {
    int i;
    for (i = 1; i < argc; i++) {
      if (strcmp(argv[i], "-nosine") == 0 ||
          strcmp(argv[i], "-no-sine") == 0 ||
          strcmp(argv[i], "-no_sine") == 0) {
        nosine = TRUE;
        break;
      }
    }
  }

  /* Check for -nomem flag (disable memory limit) */
  {
    int i;
    for (i = 1; i < argc; i++) {
      if (strcmp(argv[i], "-nomem") == 0) {
        nomem = TRUE;
        break;
      }
    }
  }

  print_banner(saved_command, PROVER_NAME, PROGRAM_VERSION, PROGRAM_DATE, tptp_mode);
  set_program_name(PROVER_NAME);   /* for conditional input */

  /* Arm wall-clock timeout as early as possible so it covers
     clausification, SInE, and other preprocessing.  Children will
     re-arm with their own slice via setup_timeout_signal() or via
     the search() call.  Uses -t N from the command line. */
  {
    int i;
    int cmd_timeout = -1;
    for (i = 1; i < argc; i++) {
      if (strcmp(argv[i], "-t") == 0 && i + 1 < argc) {
        cmd_timeout = atoi(argv[i + 1]);
        break;
      }
    }
    if (cmd_timeout > 0)
      setup_timeout_signal(cmd_timeout);
  }

  /***************** Initialize and read the input ***************************/

  if (tptp_mode) {
    /*=======================================================================
     * TPTP mode: use two-phase entry so strategy scheduler can fork
     * BEFORE SInE/parse/clausify for large inputs.
     *=======================================================================*/
    Prover_scan_result psr = std_prover_init_and_scan(argc, argv);
    const short *ml_ranking = NULL;
    int ml_ranking_len = 0;
    int ml_pick = 0;

    if (nosine) {
      assign_parm(psr->options->sine, 0, FALSE);
      clear_flag(psr->options->multi_order_trial, FALSE);
    }

    if (nomem)
      disable_max_megs();

    /* ML classification: pick best strategy from portfolio */
    if (force_strategy >= 0) {
      ml_pick = force_strategy;
    }
    else if (psr->scan != NULL) {
      ml_ranking = ml_rank(psr->scan, psr->tptp_file, &ml_ranking_len);
      if (ml_ranking != NULL && ml_ranking_len > 0)
        ml_pick = (int) ml_ranking[0];
      else
        ml_pick = ml_classify(psr->scan, psr->tptp_file);
    }
#ifdef DEBUG
    if (force_strategy >= 0)
      fprintf(stderr, "%% Forced strategy: %s (id=%d)\n",
              Portfolio[ml_pick].name, ml_pick);
    else if (psr->scan != NULL)
      fprintf(stderr, "%% ML strategy: %s (id=%d, ranking=%s)\n",
              Portfolio[ml_pick].name, ml_pick,
              ml_ranking != NULL ? "yes" : "no");
#else
    (void) ml_pick;
#endif

    /* Fork-before-SInE scheduling: only for large inputs where
       per-child SInE diversity matters.
       Note: max_seconds from -t flag is not yet applied to options
       (that happens in process_command_line_args_2 inside from_scan).
       Check the command line directly for -t. */
    {
      int cmd_max_sec = -1;
      int ci;
      for (ci = 1; ci < argc; ci++) {
        if (strcmp(argv[ci], "-t") == 0 && ci + 1 < argc) {
          cmd_max_sec = atoi(argv[ci + 1]);
          break;
        }
      }
      /* Use cmd_max_sec if given, else fall back to option value */
      if (cmd_max_sec < 0)
        cmd_max_sec = parm(psr->options->max_seconds);

      /* Sliding-window cores (from scan) for large inputs */
      if (force_strategy < 0 &&
          parm(psr->options->cores) > 0 &&
          cmd_max_sec > 0 &&
          psr->scan != NULL &&
          psr->scan->n_axioms > 5000) {
        if (cmd_max_sec > 0)
          assign_parm(psr->options->max_seconds, cmd_max_sec, FALSE);
        cores_from_scan(psr, ml_ranking, ml_ranking_len, max_strategies, slice_sec);
        /* Does not return on success. Falls through on fork failure. */
      }
    }

    /* Single-strategy or small input: complete phase 2 normally. */
    input = std_prover_from_scan(psr, -1, -1, -1);

    /* Sliding-window cores (post-clausify) for small inputs */
    if (force_strategy < 0 &&
        parm(input->options->cores) > 0 &&
        parm(input->options->max_seconds) > 0) {
      cores_search(input, ml_ranking, ml_ranking_len, max_strategies, slice_sec);
      /* Does not return on success. */
    }

    /* Single-strategy: apply forced or auto_default strategy. */
    apply_strategy(input->options,
                   force_strategy >= 0 ? force_strategy : AUTO_DEFAULT_IDX);
  }
  else {
    /*=======================================================================
     * LADR mode: unchanged single-phase entry.
     *=======================================================================*/
    input = std_prover_init_and_input(argc, argv,
                                      TRUE, TRUE, KILL_UNKNOWN);

    if (nosine) {
      assign_parm(input->options->sine, 0, FALSE);
      clear_flag(input->options->multi_order_trial, FALSE);
    }

    if (nomem)
      disable_max_megs();

    if (parm(input->options->cores) > 0 &&
        parm(input->options->max_seconds) > 0) {
      cores_search(input, NULL, 0, max_strategies, slice_sec);
    }
  }

  /***************** Echo effective options to stderr (DEBUG only) ************/

#ifdef DEBUG
  {
    Prover_options opt = input->options;
    fprintf(stderr, "%% Effective strategy options:\n");
    fprintf(stderr, "%%   order=%s\n", stringparm1(opt->order));
    fprintf(stderr, "%%   age_part=%d  weight_part=%d\n",
            parm(opt->age_part), parm(opt->weight_part));
    fprintf(stderr, "%%   max_weight=%.0f\n", floatparm(opt->max_weight));
    fprintf(stderr, "%%   binary_resolution=%d  hyper_resolution=%d"
                    "  ur_resolution=%d  paramodulation=%d\n",
            flag(opt->binary_resolution), flag(opt->hyper_resolution),
            flag(opt->ur_resolution), flag(opt->paramodulation));
    fprintf(stderr, "%%   process_initial_sos=%d  back_subsume=%d"
                    "  safe_unit_conflict=%d\n",
            flag(opt->process_initial_sos), flag(opt->back_subsume),
            flag(opt->safe_unit_conflict));
    fprintf(stderr, "%%   lightest_first=%d  breadth_first=%d"
                    "  input_sos_first=%d  default_parts=%d\n",
            flag(opt->lightest_first), flag(opt->breadth_first),
            flag(opt->input_sos_first), flag(opt->default_parts));
    fprintf(stderr, "%%   multi_order_trial=%d  cores=%d\n",
            flag(opt->multi_order_trial), parm(opt->cores));
    fprintf(stderr, "%%   max_seconds=%d  max_megs=%d\n",
            parm(opt->max_seconds), parm(opt->max_megs));
  }
#endif

  /***************** Search for a proof **************************************/

  results = search(input);

  /***************** Print result message and exit ***************************/

  if (!flag(input->options->tptp_output)) {
    /* Native Prover9 output */
    if (results->return_code == MAX_PROOFS_EXIT) {
      printf("\nTHEOREM PROVED\n");
      if (!flag(input->options->quiet))
        fprintf(stderr, "\nTHEOREM PROVED\n");
    }
    else if (results->return_code == CHECKPOINT_EXIT) {
      printf("\nCHECKPOINT SAVED\n");
      if (!flag(input->options->quiet))
        fprintf(stderr, "\nCHECKPOINT SAVED\n");
    }
    else {
      printf("\nSEARCH FAILED\n");
      if (!flag(input->options->quiet))
        fprintf(stderr, "\nSEARCH FAILED\n");
    }
  }

  exit_with_message(stdout, results->return_code);
  exit(1);
}  /* main */
