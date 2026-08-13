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

/* fopencookie() for shared-memory stdout capture requires _GNU_SOURCE
   on glibc.  Must precede all #includes (before <stdio.h>). */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#define PROVER_NAME     "Prover9"
#include "../VERSION_DATE.h"

#include "provers.h"
#include "features.h"
#include "dtree.h"
#include "strategy_config.h"
#include "../ladr/nonport.h"

#ifndef __EMSCRIPTEN__
#include <unistd.h>
#include <sys/wait.h>
#include <sys/time.h>
#include <sys/mman.h>
#include <errno.h>
#include <string.h>
/* Portability: older BSD/macOS uses MAP_ANON instead of MAP_ANONYMOUS */
#ifndef MAP_ANONYMOUS
#define MAP_ANONYMOUS MAP_ANON
#endif
#include <signal.h>
#include <fcntl.h>
#ifdef __APPLE__
#ifndef NO_LIBPROC
#include <libproc.h>
#endif
#include <sys/sysctl.h>
#endif
#endif /* !__EMSCRIPTEN__ */

#ifndef __EMSCRIPTEN__
/* Everything from here to cores_from_scan() uses fork/mmap/signals
   which are unavailable in WebAssembly.  WASM mode runs single-strategy. */

#ifndef NO_OPEN_MEMSTREAM
/* Signal-safe child PID tracking for cleanup on parent death.
   Tombstone array: slots are 0 (empty) or a live child PID.
   Signal handler scans the full array - no counter needed.
   Only used by the -cores N sliding-window scheduler (requires
   open_memstream), so guarded by NO_OPEN_MEMSTREAM. */
#define MAX_CHILD_PIDS 128
static volatile pid_t Child_pids[MAX_CHILD_PIDS];

/* Async-signal-safe SZS status for the parent death handler.  When the
   competition infrastructure kills the parent externally (SIGXCPU on the
   CPU limit, SIGTERM on the wall limit), the parent must still report a
   status instead of exiting silently.  The line is pre-formatted here in
   normal context; the signal handler only write()s it (async-safe). */
static char Death_szs_line[300];
static volatile sig_atomic_t Death_szs_len   = 0;
static volatile sig_atomic_t Death_stdout_fd = -1;
static volatile sig_atomic_t Szs_emitted     = 0;  /* single-status guard */

/* Pre-format the death-handler status line.  Call before the poll loop
   installs the death handler, once saved_stdout and the problem name are
   known.  fd is the real stdout (the parent redirects nothing, but a dup
   is safe).  A non-TPTP run emits no SZS line. */
static void cores_arm_death_status(int fd, BOOL tptp, const char *pname)
{
  Death_stdout_fd = fd;
  if (tptp) {
    int n;
    if (pname && pname[0])
      n = snprintf(Death_szs_line, sizeof(Death_szs_line),
                   "\n%% SZS status Timeout for %s\n", pname);
    else
      n = snprintf(Death_szs_line, sizeof(Death_szs_line),
                   "\n%% SZS status Timeout\n");
    if (n < 0)
      n = 0;
    else if (n > (int) sizeof(Death_szs_line))
      n = (int) sizeof(Death_szs_line);
    Death_szs_len = n;
  }
  else {
    Death_szs_len = 0;
  }
}

static void track_child(pid_t pid)
{
  int i;
  for (i = 0; i < MAX_CHILD_PIDS; i++) {
    if (Child_pids[i] == 0) {
      Child_pids[i] = pid;
      return;
    }
  }
}

static void untrack_child(pid_t pid)
{
  int i;
  for (i = 0; i < MAX_CHILD_PIDS; i++) {
    if (Child_pids[i] == pid) {
      Child_pids[i] = 0;
      return;
    }
  }
}

/* Parent death handler: kill all tracked children and exit.
   Called on SIGTERM, SIGXCPU, SIGINT from competition infrastructure. */
static void parent_death_handler(int sig)
{
  int i;
  (void)sig;
  for (i = 0; i < MAX_CHILD_PIDS; i++) {
    if (Child_pids[i] > 0) {
      kill(Child_pids[i], SIGCONT);  /* wake stopped children */
      kill(Child_pids[i], SIGKILL);
    }
  }
  /* Report a timeout status so an external kill (CPU/wall limit) is never
     silent.  Children write to /dev/null, so only the parent emits; the
     Szs_emitted guard prevents a double status if cores_emit_no_proof was
     already mid-write.  write() and _exit() are async-signal-safe. */
  if (!Szs_emitted && Death_szs_len > 0 && Death_stdout_fd >= 0) {
    ssize_t wr;
    Szs_emitted = 1;
    wr = write((int) Death_stdout_fd, Death_szs_line, (size_t) Death_szs_len);
    (void) wr;
  }
  _exit(MAX_SECONDS_EXIT);
}

static void install_parent_death_handler(void)
{
  struct sigaction sa;
  memset(&sa, 0, sizeof(sa));
  sa.sa_handler = parent_death_handler;
  sa.sa_flags = 0;
  sigaction(SIGTERM, &sa, NULL);
  sigaction(SIGXCPU, &sa, NULL);
  sigaction(SIGINT, &sa, NULL);
  /* SIGALRM too: -t N's own internal deadline (armed early in main() via
     setup_timeout_signal(), before -cores is even known to be active)
     fires SIGALRM, not SIGTERM. Without this, an -t N timeout reaching
     zero while -cores children are still running (or SIGSTOP'd mid-
     slice, mid sliding-window scheduling) falls through to provers.c's
     generic timeout_handler() instead -- which has no knowledge of
     cores children at all and just _exit()s, orphaning them. Found via
     a real 950-problem concurrent sweep (6-way process concurrency,
     -cores 8, -t 90, no external "timeout" wrapper -- termination
     relied entirely on this alarm): genuine kernel OOM kills of
     multiple simultaneous prover9 processes, clustered in time, after
     ~230 problems -- consistent with orphaned children silently
     accumulating run over run rather than any single runaway search.
     This overrides setup_timeout_signal()'s earlier SIGALRM handler
     the moment -cores actually starts (this function is only called
     from inside cores_search()/cores_search_ladr(), never before), so
     the internal-alarm and external-kill paths now behave identically:
     both go through parent_death_handler(), which kills every tracked
     child before the parent exits. */
  sigaction(SIGALRM, &sa, NULL);
}
#endif /* !NO_OPEN_MEMSTREAM */

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
#define CHILD_OUTPUT_BUFSZ  (16 * 1024 * 1024)   /* 16 MB per slot */

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

#ifndef NO_OPEN_MEMSTREAM
/* Re-arm the death-handler line with the WINNER's own status line,
   extracted from its captured output (its status is the last line of the
   buffer).  From this point a kill landing before or during the relay
   yields exactly one, correct status: pre-relay or mid-relay the handler
   writes this line (the buffer's own copy has not been written yet --
   it is at the very end); after the relay Szs_emitted suppresses the
   handler entirely.  Falls back to the armed Timeout line if the buffer
   has no status (non-TPTP run). */
static void cores_arm_death_from_winner(struct child_output *out)
{
  int len = out->output_len;
  const char *b = out->buf;
  int i, start = -1, end, n;
  if (len > (int) sizeof(((struct child_output *)0)->buf))
    len = (int) sizeof(((struct child_output *)0)->buf);
  for (i = 0; i + 12 <= len; i++)
    if (memcmp(b + i, "% SZS status", 12) == 0)
      start = i;                       /* last occurrence wins */
  if (start < 0)
    return;
  end = start;
  while (end < len && b[end] != '\n')
    end++;
  n = end - start;
  if (n > (int) sizeof(Death_szs_line) - 3)
    n = (int) sizeof(Death_szs_line) - 3;
  Death_szs_len = 0;
  Death_szs_line[0] = '\n';
  memcpy(Death_szs_line + 1, b + start, n);
  Death_szs_line[n + 1] = '\n';
  Death_szs_len = n + 2;
}

/* Retry-safe blocking write of a byte range to a descriptor. */
static void fd_write_all(int fd, const char *b, int n)
{
  int off = 0;
  while (off < n) {
    ssize_t w = write(fd, b + off, (size_t) (n - off));
    if (w <= 0)
      break;
    off += (int) w;
  }
}

/* Publish the winning child's captured output to the real stdout, SZS
   status line first.  search.c now writes the child's status line ahead of
   the proof body, so the buffer already begins with it.  We publish the
   status prefix (everything up to and including that line) under a signal
   block, claiming the single-status slot (Szs_emitted) so a concurrent
   external kill cannot emit a second status line; then we relay the proof
   body.  A kill during the body relay finds Szs_emitted set and adds
   nothing -- the status is already out, which is the point of status-first:
   the solve is credited even if the (possibly large) proof print is cut
   off.  A kill before the block is handled by parent_death_handler, which
   emits the status armed by cores_arm_death_from_winner. */
static void cores_publish_winner(struct child_output *out, int fd)
{
  int len = out->output_len;
  const char *b = out->buf;
  int cap = (int) sizeof(((struct child_output *)0)->buf);
  int i, sstart = -1, send, prefix;
  sigset_t block, old;

  if (len > cap)
    len = cap;

  for (i = 0; i + 12 <= len; i++)
    if (memcmp(b + i, "% SZS status", 12) == 0) { sstart = i; break; }

  if (sstart < 0) {
    /* No status line (non-TPTP run): relay verbatim, claim the slot. */
    Szs_emitted = 1;
    fd_write_all(fd, b, len);
    return;
  }

  send = sstart;
  while (send < len && b[send] != '\n')
    send++;
  if (send < len)
    send++;                       /* include the status line's newline */
  prefix = send;

  sigemptyset(&block);
  sigaddset(&block, SIGTERM);
  sigaddset(&block, SIGINT);
#ifdef SIGXCPU
  sigaddset(&block, SIGXCPU);
#endif
  sigprocmask(SIG_BLOCK, &block, &old);
  if (!Szs_emitted) {
    Szs_emitted = 1;
    fd_write_all(fd, b, prefix);
  }
  sigprocmask(SIG_SETMASK, &old, NULL);

  fd_write_all(fd, b + prefix, len - prefix);
}

#endif /* !NO_OPEN_MEMSTREAM */


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

#ifndef NO_OPEN_MEMSTREAM
/* The sliding-window scheduler and its helpers require fork/mmap/signals
   and open_memstream.  Compiled out on older macOS (NO_OPEN_MEMSTREAM). */

/* File-scope pointer to this child's mmap slot (set in spawn_child) */
static volatile struct child_hints *my_hints = NULL;

/* File-scope pointer to this child's output buffer (set in spawn_child) */
static struct child_output *my_output = NULL;

/* open_memstream buffer for child stdout capture */
static char *Memstream_buf = NULL;
static size_t Memstream_len = 0;

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
  /* Block SIGALRM to prevent suspend timer from freezing us mid-write.
     Also defer SIGTERM (set_no_kill) to protect proof output. */
  {
    sigset_t block;
    sigemptyset(&block);
    sigaddset(&block, SIGALRM);
    sigprocmask(SIG_BLOCK, &block, NULL);
  }
  set_no_kill();
  print_exit_message(stdout, code);

  /* Flush open_memstream and copy captured output to shared memory.
     Parent reads the shm buffer for the winning child. */
  if (my_output && Memstream_buf) {
    int n;
    fflush(stdout);
    fclose(stdout);
    n = (int) Memstream_len;
    if (n > (int) sizeof(my_output->buf))
      n = (int) sizeof(my_output->buf);
    memcpy(my_output->buf, Memstream_buf, n);
    my_output->output_len = n;
  }

  _exit(code);
}

/*************
 *
 *   child_rss_megs()
 *
 *   Read a child's current resident-set size (RSS), in megabytes,
 *   directly from the OS -- used for -cores's per-child memory-budget
 *   enforcement instead of the child's own self-reported megs_used (an
 *   in-process palloc counter written via shared memory at a handful of
 *   checkpoints -- see shm_progress_update()). That IPC-reported figure
 *   can go stale for large-theory problems: preprocessing functions
 *   like index_and_process_initial_clauses() and predicate_elimination()
 *   have no progress checkpoints of their own, only calls bracketing
 *   them, so a child that self-suspends WHILE inside one of them (a
 *   large SInE-selected theory can occupy an entire Phase-1 slice there)
 *   reports whatever megs_used was at its last checkpoint -- understating
 *   real usage by however much that one call has consumed since. Found
 *   live, 2026-08-11, via an independently-developed prover: an explicit
 *   8000MB budget was exceeded by 6-7x on a large-theory problem for
 *   exactly this reason, even though
 *   the budget arithmetic and the -tptp magic-comment plumbing that sets
 *   it were both independently confirmed correct.
 *
 *   Reading the OS's own RSS accounting sidesteps the gap: it reflects
 *   ALL memory the process holds, however it was allocated (not just
 *   palloc-tracked allocations), at the exact moment this is called --
 *   and since the caller only calls this after confirming WIFSTOPPED,
 *   the child is genuinely frozen by the time this runs, so the read is
 *   a true snapshot, not an estimate racing a still-running process.
 *
 *   Returns -1 if unavailable (unsupported platform, or the read
 *   failed -- e.g. the child exited between waitpid() and this call) so
 *   callers treat "unknown" as "don't kill" rather than misreading -1
 *   as a real, tiny memory figure.
 *
 *************/

static
long child_rss_megs(pid_t pid)
{
#if defined(__linux__)
  char path[64];
  FILE *fp;
  long rss_kb = -1;
  snprintf(path, sizeof(path), "/proc/%d/status", (int) pid);
  fp = fopen(path, "r");
  if (fp != NULL) {
    char line[256];
    while (fgets(line, sizeof(line), fp) != NULL) {
      if (strncmp(line, "VmRSS:", 6) == 0) {
        sscanf(line + 6, "%ld", &rss_kb);
        break;
      }
    }
    fclose(fp);
  }
  return (rss_kb >= 0) ? (rss_kb / 1024) : -1;
#elif defined(__APPLE__) && !defined(NO_LIBPROC)
  struct proc_taskinfo info;
  int n = proc_pidinfo(pid, PROC_PIDTASKINFO, 0, &info, sizeof(info));
  return (n == (int) sizeof(info))
         ? (long) (info.pti_resident_size / (1024 * 1024))
         : -1;
#else
  /* No RSS source available on this platform (e.g. an old Darwin/
     PowerPC SDK predating libproc.h) -- -1 means "unknown", which
     every caller already treats as "don't kill", not as 0 MB. This
     only degrades the RSS-based per-child kill check on such a
     platform; system_ram_megs()'s sysctlbyname-based default budget
     (below) is unaffected, since it's unrelated to libproc. */
  (void) pid;
  return -1;
#endif
}  /* child_rss_megs */

/*************
 *
 *   system_ram_megs()
 *
 *   Return this machine's total physical RAM, in megabytes, or -1 if
 *   it can't be determined.  Used only to give -cores a machine-aware
 *   DEFAULT memory budget instead of the fixed 48GB compiled-in
 *   default (ladr/memory.c's DEFAULT_MAX_MEGS) -- that fixed value is
 *   fine for an ordinary single-strategy run, but for -cores it's
 *   backwards on both ends of the hardware range: meaningless on a
 *   small box (e.g. a 1.9GB Lightsail instance -- 48GB "protection"
 *   never engages before the box is already in trouble) and needlessly
 *   conservative on a large one (a 503GB machine could safely allow
 *   far more per instance).  An explicit assign(max_megs,N) always
 *   wins over this -- see the parm_is_user_set() check at each call
 *   site below; this function only feeds the case where the user
 *   never asked for a specific figure at all. */

static
long system_ram_megs(void)
{
#if defined(__linux__)
  long pages = sysconf(_SC_PHYS_PAGES);
  long page_size = sysconf(_SC_PAGE_SIZE);
  return (pages > 0 && page_size > 0) ? (pages * page_size) / (1024 * 1024) : -1;
#elif defined(__APPLE__)
  uint64_t bytes = 0;
  size_t sz = sizeof(bytes);
  return (sysctlbyname("hw.memsize", &bytes, &sz, NULL, 0) == 0 && bytes > 0)
         ? (long) (bytes / (1024 * 1024))
         : -1;
#else
  return -1;
#endif
}  /* system_ram_megs */

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
  /* Straight SIGKILL: kill_child is only ever used on LOSERS (the
     winner is never killed), whose captured output is discarded -- so
     the old SIGTERM + 100ms "proof flush" grace bought nothing and
     cost two things: ~100ms per loser of publish latency, and a
     handler execution in any child still inside its startup window
     (the Job7086 double-status race).  SIGKILL runs no handler, so a
     loser can never write anything, at any scheduling. */
  kill(pid, SIGCONT);   /* wake if stopped, no-op if running */
  kill(pid, SIGKILL);
  waitpid(pid, NULL, 0);
  untrack_child(pid);
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

#endif /* !NO_OPEN_MEMSTREAM  (cores-only helpers above) */

/*************
 *
 *   apply_strategy()
 *
 *   Modify options for portfolio strategy idx.
 *   All changes are silent (echo=FALSE).
 *
 *   Additive, not overriding: every field below is skipped when the
 *   user has already set the corresponding option explicitly (input
 *   file, TPTP magic comment, stdin, or command line -- see options.c's
 *   user_set field and *_is_user_set() accessors).  The portfolio was
 *   trained on general FOL problems and knows nothing about a specific
 *   problem's own hand-tuning (e.g. assign(max_weight, 35) chosen for a
 *   delicate equational derivation); stomping such a choice on 95 of 96
 *   -cores workers left only the untouched "auto_default" slot doing
 *   useful work, so -cores N showed real CPU usage on N cores but no
 *   speedup over N=1.  Only fields
 *   still at their compiled-in default get the strategy's variation.
 *
 *************/

static
void apply_strategy(Prover_options opt, int idx)
{
  const struct strategy_config *s = &Portfolio[idx];

  if (!stringparm_is_user_set(opt->order)) {
    if (s->order == 0)
      assign_stringparm(opt->order, "lpo", FALSE);
    else if (s->order == 1)
      assign_stringparm(opt->order, "rpo", FALSE);
    else if (s->order == 2)
      assign_stringparm(opt->order, "kbo", FALSE);
  }

  if (s->age_part >= 0 && !parm_is_user_set(opt->age_part))
    assign_parm(opt->age_part, s->age_part, FALSE);
  if (s->weight_part >= 0 && !parm_is_user_set(opt->weight_part))
    assign_parm(opt->weight_part, s->weight_part, FALSE);
  if (s->max_weight >= 0 && !floatparm_is_user_set(opt->max_weight))
    assign_floatparm(opt->max_weight, (double) s->max_weight, FALSE);
  if (s->sine_weight >= 0 && !parm_is_user_set(opt->sine_weight))
    assign_parm(opt->sine_weight, s->sine_weight, FALSE);

  if (!flag_is_user_set(opt->binary_resolution)) {
    if (s->binary_resolution == 1) set_flag(opt->binary_resolution, FALSE);
    else if (s->binary_resolution == 0) clear_flag(opt->binary_resolution, FALSE);
  }

  if (!flag_is_user_set(opt->hyper_resolution)) {
    if (s->hyper_resolution == 1) set_flag(opt->hyper_resolution, FALSE);
    else if (s->hyper_resolution == 0) clear_flag(opt->hyper_resolution, FALSE);
  }

  if (!flag_is_user_set(opt->ur_resolution)) {
    if (s->ur_resolution == 1) set_flag(opt->ur_resolution, FALSE);
    else if (s->ur_resolution == 0) clear_flag(opt->ur_resolution, FALSE);
  }

  if (!flag_is_user_set(opt->paramodulation)) {
    if (s->paramodulation == 1) set_flag(opt->paramodulation, FALSE);
    else if (s->paramodulation == 0) clear_flag(opt->paramodulation, FALSE);
  }

  if (!flag_is_user_set(opt->multi_order_trial)) {
    if (s->multi_order_trial == 1) set_flag(opt->multi_order_trial, FALSE);
    else if (s->multi_order_trial == 0) clear_flag(opt->multi_order_trial, FALSE);
  }

  if (!flag_is_user_set(opt->process_initial_sos)) {
    if (s->process_initial_sos == 1) set_flag(opt->process_initial_sos, FALSE);
    else if (s->process_initial_sos == 0) clear_flag(opt->process_initial_sos, FALSE);
  }

  if (!flag_is_user_set(opt->back_subsume)) {
    if (s->back_subsume == 1) set_flag(opt->back_subsume, FALSE);
    else if (s->back_subsume == 0) clear_flag(opt->back_subsume, FALSE);
  }

  if (!flag_is_user_set(opt->lightest_first)) {
    if (s->lightest_first == 1) set_flag(opt->lightest_first, FALSE);
    else if (s->lightest_first == 0) clear_flag(opt->lightest_first, FALSE);
  }

  if (!flag_is_user_set(opt->breadth_first)) {
    if (s->breadth_first == 1) set_flag(opt->breadth_first, FALSE);
    else if (s->breadth_first == 0) clear_flag(opt->breadth_first, FALSE);
  }

  if (!flag_is_user_set(opt->safe_unit_conflict)) {
    if (s->safe_unit_conflict == 1) set_flag(opt->safe_unit_conflict, FALSE);
    else if (s->safe_unit_conflict == 0) clear_flag(opt->safe_unit_conflict, FALSE);
  }

  if (!flag_is_user_set(opt->factor)) {
    if (s->factor == 1) set_flag(opt->factor, FALSE);
    else if (s->factor == 0) clear_flag(opt->factor, FALSE);
  }

  if (!flag_is_user_set(opt->unit_deletion)) {
    if (s->unit_deletion == 1) set_flag(opt->unit_deletion, FALSE);
    else if (s->unit_deletion == 0) clear_flag(opt->unit_deletion, FALSE);
  }

  if (!flag_is_user_set(opt->para_units_only)) {
    if (s->para_units_only == 1) set_flag(opt->para_units_only, FALSE);
    else if (s->para_units_only == 0) clear_flag(opt->para_units_only, FALSE);
  }

  if (!flag_is_user_set(opt->back_demod)) {
    if (s->back_demod == 1) set_flag(opt->back_demod, FALSE);
    else if (s->back_demod == 0) clear_flag(opt->back_demod, FALSE);
  }

  if (!flag_is_user_set(opt->ordered_res)) {
    if (s->ordered_res == 1) set_flag(opt->ordered_res, FALSE);
    else if (s->ordered_res == 0) clear_flag(opt->ordered_res, FALSE);
  }

  if (!flag_is_user_set(opt->ordered_para)) {
    if (s->ordered_para == 1) set_flag(opt->ordered_para, FALSE);
    else if (s->ordered_para == 0) clear_flag(opt->ordered_para, FALSE);
  }

  if (!stringparm_is_user_set(opt->literal_selection)) {
    if (s->literal_selection == 0)
      assign_stringparm(opt->literal_selection, "max_negative", FALSE);
    else if (s->literal_selection == 1)
      assign_stringparm(opt->literal_selection, "all_negative", FALSE);
  }

  if (s->nest_penalty >= 0 && !floatparm_is_user_set(opt->nest_penalty))
    assign_floatparm(opt->nest_penalty, (double) s->nest_penalty, FALSE);
  if (s->depth_penalty >= 0 && !floatparm_is_user_set(opt->depth_penalty))
    assign_floatparm(opt->depth_penalty, (double) s->depth_penalty, FALSE);

  /* Disable periodic checkpoints in strategy children -- internal
     scheduler bookkeeping, not a search-tuning choice, so this one is
     NOT conditioned on user_set (a user's own checkpoint_minutes setting
     is for the top-level run, not per-worker children). */
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
int ml_classify(Scan_result scan)
{
  int fv[NUM_FEATURES];
  int pick;
  extract_features(scan, fv);
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
const short *ml_rank(Scan_result scan, int *out_len)
{
  int fv[NUM_FEATURES];
  extract_features(scan, fv);
  *out_len = dtree_num_strats();
  return dtree_rank(fv);
}  /* ml_rank */


/* [removed: ml_sweep_loop, ml_sweep_loop_from_scan, parent_poll_dual_track,
   strategy_schedule_search, strategy_schedule_from_scan, sweep_search,
   sweep_from_scan -- superseded by -cores N sliding-window scheduler] */

#ifndef NO_OPEN_MEMSTREAM
/* Cores-only: sliding-window scheduler and helpers (through cores_from_scan) */

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
                  struct child_hints *hints_shm,
                  BOOL force_single_proof)
{
  pid_t cpid;
  sigset_t fork_block, fork_old;

  fflush(stdout);
  fflush(stderr);

  /* Block the status-writing signals across the fork.  Resetting the
     handlers as the child's first instruction (below) is NOT enough:
     a SIGTERM delivered between fork() and the child first being
     scheduled fires the INHERITED handler, which writes a Timeout line
     to fd 1 -- still the real stdout at that point.  On a loaded node
     the fork-to-schedule window is milliseconds wide (StarExec Job7086:
     3 of 158 MGT pairs doubled that way).  With the mask inherited
     blocked, such a signal stays pending until the child has installed
     SIG_DFL and unblocks -- and then it just dies, silently. */
  sigemptyset(&fork_block);
  sigaddset(&fork_block, SIGTERM);
  sigaddset(&fork_block, SIGALRM);
  sigaddset(&fork_block, SIGINT);
#ifdef SIGXCPU
  sigaddset(&fork_block, SIGXCPU);
#endif
  sigprocmask(SIG_BLOCK, &fork_block, &fork_old);

  cpid = fork();
  if (cpid < 0) {
    sigprocmask(SIG_SETMASK, &fork_old, NULL);
    fprintf(stderr, "%% Cores: fork failed for slot %d\n", slot);
    return 0;
  }

  if (cpid == 0) {
    /* ---- Child process ---- */
    int devnull_fd;
    /* FIRST: drop the inherited signal handlers.  The parent kills
       losing children with SIGTERM, and the inherited timeout_handler
       answers it by WRITING a Timeout status line to fd 1 -- which, in
       the window before the /dev/null redirect below, is still the
       REAL stdout.  On tiny problems whose winner finishes while
       siblings are still being spawned, that emitted a spurious second
       status line (StarExec Job7072: four MGT pairs with "Timeout"
       followed by the winner's real status).  Default disposition is
       to die silently: losers' output is discarded anyway, and
       arm_suspend_timer installs the child's own SIGALRM handler
       further down.  (mace4's fork_size_child has always done this.) */
    signal(SIGTERM, SIG_DFL);
    signal(SIGALRM, SIG_DFL);
    signal(SIGINT,  SIG_DFL);
#ifdef SIGXCPU
    signal(SIGXCPU, SIG_DFL);
#endif
    /* Only now deliver anything that arrived during the window: the
       dispositions are default, so a pending kill terminates silently. */
    sigprocmask(SIG_SETMASK, &fork_old, NULL);
    close(saved_stdout);

    /* Redirect fd 1 to /dev/null as safety net for stray raw writes.
       Also redirect fd 2 (stderr): every child inherits the SAME real
       terminal stderr from the parent, and per-proof progress banners
       ("-------- Proof N --------", search.c) print via fprintf(stderr,
       ...) -- unlike stdout, that path was never captured/buffered per
       child, so with N>1 concurrent children each solving the same
       problem, their banners interleaved live on the real terminal,
       unlabeled and duplicated (confirmed live, 2026-08-06, racing 2
       strategies against a multi-goal problem: "Proof 1/Proof 2/Proof
       1/Proof 2/Proof 3..." from two different children print-racing
       each other). Losing children's stderr is discarded anyway, same
       as their stdout; suppressing it here instead of leaking it live
       is consistent with -cores's existing all-buffered-until-the-end
       design (the winner's stdout output isn't streamed live either). */
    devnull_fd = open("/dev/null", O_WRONLY);
    if (devnull_fd >= 0) {
      dup2(devnull_fd, STDOUT_FILENO);
      dup2(devnull_fd, STDERR_FILENO);
      close(devnull_fd);
    }

    /* Capture child stdout via open_memstream (POSIX.1-2008).
       All printf/fprintf(stdout) goes to a growable memory buffer.
       child_exit() flushes and copies the buffer to shared memory.
       On old systems without open_memstream, child output goes to
       /dev/null and the parent emits only the SZS status line. */
#ifndef NO_OPEN_MEMSTREAM
    if (output_shm) {
      FILE *memfp;
      /* Indexed by order_idx, not slot: a suspended child can be resumed
         into a DIFFERENT physical slot than the one it was originally
         spawned into (cores_poll_loop's Phase 2 resume assigns whichever
         slot just freed up, not the child's original slot -- see
         "slots[i] = rpid" there). order_idx is the child's stable identity
         across that reassignment (same pattern hints_shm already uses).
         Indexing by slot here made a winner's captured output land in a
         shared-memory cell the parent had stopped associating with that
         child, so the parent read a still-zeroed neighbor slot instead --
         a genuine proof, fully printed, silently reported as no status at
         all. Found live, 2026-08-07, TPTP v9.3.0 sweep. */
      my_output = &output_shm[order_idx];
      my_output->output_len = 0;
      Memstream_buf = NULL;
      Memstream_len = 0;
      memfp = open_memstream(&Memstream_buf, &Memstream_len);
      if (memfp) {
        fclose(stdout);
        stdout = memfp;
      }
      else {
        /* open_memstream failed (e.g. ENOMEM under heavy concurrent load).
           Without it, everything this child prints to stdout goes to
           /dev/null (redirected above) and is never captured -- if this
           child wins, child_exit()'s "my_output && Memstream_buf" copy
           check sees Memstream_buf still NULL and skips the copy
           entirely, so a winner with a real proof reports a clean exit
           with zero output, indistinguishable from a plain failure.
           Seed a fallback status directly into the shared buffer so a
           win is still reported as something, not silence. */
        static const char msg[] =
          "\n% SZS status Unknown : proof output buffer allocation failed "
          "(open_memstream)\n";
        size_t len = sizeof(msg) - 1;
        if (len > sizeof(my_output->buf))
          len = sizeof(my_output->buf);
        memcpy(my_output->buf, msg, len);
        my_output->output_len = (int) len;
        fprintf(stderr, "%% WARNING: Cores slot %d: open_memstream failed "
                "(%s) -- this child's output, if it wins, is unrecoverable "
                "beyond the fallback status.\n", slot, strerror(errno));
      }
    }
#endif

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
      if (force_single_proof) {
        /* LADR -cores race (cores_search_ladr): force exactly one proof
           of ANY goal, overriding auto_denials()'s own bump of
           max_proofs to the file's goal count for a multi-goal Horn set
           -- single_proof_race is what makes the override actually
           stick (see search.c's auto_denials, and docs/cores-ladr-
           single-goal-race-spec.md). TPTP mode never sets this. */
        assign_parm(input->options->max_proofs, 1, FALSE);
        set_flag(input->options->single_proof_race, FALSE);
      }
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
  /* Track the new child BEFORE unblocking SIGALRM/SIGTERM/SIGINT/SIGXCPU
     (blocked since before fork(), above) -- not after, back in the
     caller. If unblocked first, there's a real window where a signal
     landing right here would run parent_death_handler() (or the
     no-cleanup pre-SIGALRM-fix handler) with this child's pid not yet
     in Child_pids[], leaking it as an orphan indistinguishable from a
     completely different bug. Found live, 2026-08-10: 54ef0b4 (wiring
     parent_death_handler to SIGALRM) fixed the single-shot repro but
     a real 950-problem sustained sweep still accumulated orphans into
     a much worse OOM burst (227 concurrent processes vs. an expected
     ~48) -- this window, hit repeatedly at the volume of many
     sequential -cores invocations rather than as a rare one-off, is
     the second leak path. */
  track_child(cpid);
  sigprocmask(SIG_SETMASK, &fork_old, NULL);
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

  /* Claim the single-status slot so a concurrent external-kill signal
     does not also emit via parent_death_handler. */
  Szs_emitted = 1;

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
  case SIGINT_EXIT:
    szs = "User"; break;
  case SIGTERM_EXIT:
    szs = "Timeout"; break;   /* external wall-limit kill */
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
  unsigned last_mem_check;

  /* Suspended pool for sleep/wake scheduling (sized for phase1_limit) */
  struct suspended_child *suspended;
  int n_suspended;

  slots = safe_calloc(N, sizeof(pid_t));
  slot_strat = safe_calloc(N, sizeof(int));
  slot_oidx = safe_calloc(N, sizeof(int));
  suspended = safe_calloc(phase1_limit, sizeof(struct suspended_child));

  next = 0;
  best_code = -1;
  n_suspended = 0;
  start_time = absolute_wallclock();
  last_mem_check = start_time;

  /* Install cleanup handler so external kill (SIGTERM/SIGXCPU)
     kills all children instead of orphaning them. */
  install_parent_death_handler();

  /* Initial fill: launch up to N children.
     auto_default gets full time budget (never self-suspends), keeping
     its dedicated slot for the entire run.  Other strategies get the
     normal per_child_sec slice and cycle through the remaining slots. */
  for (i = 0; i < N && next < phase1_limit; i++) {
    int si = order[next];
    int slice = (si == AUTO_DEFAULT_IDX) ? total_deadline : per_child_sec;
    pid_t cpid = spawn_child(i, si, next, slice, saved_stdout,
                             output_shm, input, psr, hints_shm, FALSE);
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

    /* Periodic memory check on RUNNING children, throttled to once a
       second. Without this, a child is only ever checked against the
       budget at the moment it self-suspends (WIFSTOPPED below) -- for
       a long slice, or when phase1_limit<=N and no slicing happens at
       all (per_child_sec==total_time, see the caller), a fast-
       ballooning child would otherwise go completely uncaught until it
       either finishes or hits the backstop deadline above. Suspended
       children are NOT re-checked here: they're frozen (SIGSTOPped),
       so their RSS can't grow, and they were already checked once at
       the moment they were suspended. */
    if (per_child_megs_budget > 0 &&
        absolute_wallclock() != last_mem_check) {
      last_mem_check = absolute_wallclock();
      for (i = 0; i < N; i++) {
        long rss_megs;
        if (slots[i] <= 0) continue;
        rss_megs = child_rss_megs(slots[i]);
        if (rss_megs >= 0 && rss_megs > per_child_megs_budget) {
#ifdef DEBUG
          fprintf(stderr, "%% Cores: killed s%d (slot %d): %ld MB "
                  "(RSS, running) > %d MB budget\n",
                  slot_strat[i], i, rss_megs, per_child_megs_budget);
#endif
          kill_child(slots[i]);
          slots[i] = 0;
        }
      }
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
        untrack_child(slots[i]);
        slots[i] = 0;
        continue;
      }

      if (WIFSTOPPED(status)) {
        /* Child self-suspended (SIGALRM -> SIGSTOP) */
        int oidx = slot_oidx[i];
        /* Read real OS-level RSS now, while the child is genuinely
           frozen (WIFSTOPPED confirmed above) -- see child_rss_megs()
           for why this replaces hints_shm[oidx].megs_used for the
           budget decision below (that IPC figure can be stale for
           large-theory problems stuck inside a preprocessing call with
           no checkpoints of its own). Still read for the DEBUG trace
           below, to make a stale-vs-real mismatch visible if it recurs. */
        long rss_megs = (per_child_megs_budget > 0)
                        ? child_rss_megs(slots[i]) : -1;

#ifdef DEBUG
        fprintf(stderr, "%% Cores slot %d (%s) [pid %d]: suspended"
                " (stage=%d given=%d kept=%d megs=%d rss=%ld)\n",
                i, Portfolio[slot_strat[i]].name, (int) slots[i],
                hints_shm ? hints_shm[oidx].stage : -1,
                hints_shm ? hints_shm[oidx].given : -1,
                hints_shm ? hints_shm[oidx].kept  : -1,
                hints_shm ? hints_shm[oidx].megs_used : -1,
                rss_megs);
#endif

        /* Memory ejection: kill children exceeding budget. rss_megs<0
           means "unknown" (unsupported platform, or the read raced the
           child's own exit) -- treat as "don't kill", not as 0 MB. */
        if (per_child_megs_budget > 0 &&
            rss_megs >= 0 && rss_megs > per_child_megs_budget) {
#ifdef DEBUG
          fprintf(stderr, "%% Cores: killed s%d (slot %d): "
                  "%ld MB (RSS) > %d MB budget\n",
                  slot_strat[i], i,
                  rss_megs, per_child_megs_budget);
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
                                   output_shm, input, psr, hints_shm, FALSE);
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
        else {
          child_code = FATAL_EXIT;
          if (WIFSIGNALED(status))
            fprintf(stderr, "%% WARNING: Cores slot %d (%s): child pid %d "
                    "killed by signal %d (%s)%s\n",
                    i, Portfolio[slot_strat[i]].name, slots[i],
                    WTERMSIG(status), strsignal(WTERMSIG(status)),
                    WCOREDUMP(status) ? ", core dumped" : "");
        }


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

          if (output_shm) {
            /* Indexed by slot_oidx[i], not i: this child may have been
               resumed into slot i from a suspend (Phase 2 above), in which
               case it was originally spawned -- and wrote its captured
               output -- under a different order_idx (see spawn_child's
               my_output comment). slot_oidx[i] is this slot's CURRENT
               occupant's order_idx, kept in sync at every spawn/resume. */
            /* Arm the death handler with the winner's own status line so a
               kill landing before the publish below still emits the correct
               status; then publish status-first (see cores_publish_winner). */
            cores_arm_death_from_winner(&output_shm[slot_oidx[i]]);
            cores_publish_winner(&output_shm[slot_oidx[i]], saved_stdout);
          }
          else {
            /* output_shm allocation failed at start-up (mmap under heavy
               concurrent -cores load, e.g. many racing instances at once
               -- found live, 2026-08-07, TPTP sweep at -P4 x 8-way): every
               child also skipped its own output-capture setup (spawn_child
               only redirects stdout to a memstream when output_shm is
               non-NULL), so there is no captured transcript to publish for
               ANY slot, not just this one -- the whole race's outputs went
               to /dev/null from the moment they were spawned. Silently
               falling through here previously made the whole process
               exit(MAX_PROOFS_EXIT) (0) with zero output: indistinguishable
               from a hung/killed process to anything scripting around this
               tool. Print an honest, minimal status instead of nothing --
               never claim the specific proof/theorem status without the
               transcript to back it up. */
            FILE *fp = fdopen(dup(saved_stdout), "w");
            if (fp) {
              fprintf(fp, "\n%% SZS status Unknown : -cores winner found but "
                          "its output was never captured (shared-memory "
                          "allocation failed at start-up, likely from heavy "
                          "concurrent -cores load) -- rerun with less "
                          "concurrent -cores load for a definitive result.\n");
              fclose(fp);
            }
          }

#ifdef DEBUG
          fprintf(stderr, "%% Cores winner: slot %d (%s)\n",
                  i, Portfolio[slot_strat[i]].name);
#endif

          safe_free(slots);
          safe_free(slot_strat);
          safe_free(slot_oidx);
          safe_free(suspended);
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

        untrack_child(slots[i]);
        slots[i] = 0;

        /* Fill slot: Phase 1 (new strategy) or Phase 2 (resume) */
        if (next < phase1_limit) {
          int si = order[next];
          pid_t cpid = spawn_child(i, si, next, per_child_sec, saved_stdout,
                                   output_shm, input, psr, hints_shm, FALSE);
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

  safe_free(slots);
  safe_free(slot_strat);
  safe_free(slot_oidx);
  safe_free(suspended);
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
  /* No -t given (total_time <= 0): race exactly N strategies with no
     time limit, instead of silently falling back to a single, non-raced
     auto search -- see cores_search_ladr's identical fix/comment
     (2026-08-09) for the full rationale.  The Phase 1 breadth-then-depth
     formula below fundamentally needs a known total budget to divide
     between breadth and depth; with none, skip it entirely rather than
     feeding it a nonsensical total_time and race N un-sliced,
     unbounded strategies instead (per_child_sec=0 and, further down,
     a <=0 deadline both already mean "no limit" to cores_poll_loop). */
  BOOL unbounded = (total_time <= 0);
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

  if (N <= 0)
    return;  /* fall through to single strategy */

  if (unbounded) {
    phase1_limit = N;
    per_child_sec = 0;
  }
  else {
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
  }

  /* Per-child memory budget: always enforced (unless max_megs is
     explicitly set to -1, meaning "no limit"), scaled to phase1_limit --
     the real worst-case number of children ONE instance can hold at
     once (N running + up to phase1_limit-N suspended-but-not-killed in
     the Phase 1 breadth pool) -- not num_strats (a fixed 96, unrelated
     to how many are ever actually held concurrently). Previously this
     only activated when max_megs was explicitly set to a small value,
     so the default 48GB max_megs left the breadth pool completely
     uncapped: for -cores 8 -t90 (phase1_limit=45), that's up to ~37
     suspended children, each holding real memory, times however many
     independent -cores instances an outside driver runs concurrently.
     Found live, 2026-08-10/11 via an independently-developed prover:
     this, not either of the two process-tracking races already fixed
     (54ef0b4, 8ea44ba), is what
     actually drove a 6-way-concurrent sweep to 227-230 processes and a
     near-reboot on a 503GB box -- reproduced directly and safely on a
     single local instance (-cores 8 -slice 2 -t 30: process count
     climbed to N+phase1_limit and held, memory passed 1GB and was still
     climbing). Dividing by phase1_limit caps ONE instance's aggregate
     Phase-1 memory at max_megs total -- the same ceiling a single
     non-cores prover9 run already gets -- instead of unbounded; an
     outside driver running many concurrent instances should still pass
     an explicit, appropriately-divided assign(max_megs,N) of its own,
     since this can only bound each instance individually, not the sum
     across instances it has no visibility into. */
  if (max_megs_val > 0) {
    /* An untouched max_megs is still exactly ladr/memory.c's compiled-in
       48GB default -- fine as a ceiling for a single ordinary
       (non-cores) run, but not a meaningful DEFAULT for -cores itself
       (see system_ram_megs()'s own comment): swap it for 80% of this
       machine's real RAM in that case. An explicit assign(max_megs,N)
       (parm_is_user_set) always wins and is used as-is, unchanged. */
    if (!parm_is_user_set(input->options->max_megs)) {
      long ram_megs = system_ram_megs();
      if (ram_megs > 0)
        max_megs_val = (int) (ram_megs * 0.8);
    }
    per_child_megs = max_megs_val / phase1_limit;
  }
  else
    per_child_megs = 0;  /* max_megs explicitly disabled (-1) */

  order = safe_malloc(num_strats * sizeof(int));
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

  /* Allocate shared-memory output buffers (16 MB per slot, indexed by
     order_idx -- a suspended child can be resumed into a different
     physical slot than it was spawned into, so this must be sized for
     the full order_idx range (phase1_limit), not just N slots. */
  output_shm = (struct child_output *) mmap(NULL,
      phase1_limit * sizeof(struct child_output),
      PROT_READ | PROT_WRITE,
      MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (output_shm == MAP_FAILED) {
    /* Losing this buffer silently disables output capture for every child
       spawned from here on (spawn_child only redirects a child's stdout to
       a memstream when output_shm is non-NULL) -- the eventual winner-
       publish fallback further down handles the "no captured output"
       case, but the root cause (why the mmap itself failed) is worth a
       permanent, unconditional record: this is small (a few dozen MB at
       most) and every prior anonymous mmap in this same process already
       succeeded, so a failure here means something environmental (an
       existing memory-mapping-count limit, transient memory pressure from
       many concurrent -cores instances, etc.), not this allocation being
       unreasonably large. */
    fprintf(stderr, "%% WARNING: Cores: output_shm mmap failed (%s) -- "
                    "winner output will be uncapturable this run.\n",
            strerror(errno));
    output_shm = NULL;
  }


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

  cores_arm_death_status(saved_stdout, flag(input->options->tptp_output),
                         input->problem_name);

  result = cores_poll_loop(N, order, num_strats, phase1_limit, per_child_sec,
                           saved_stdout, input, NULL,
                           unbounded ? 0 : (total_time + 2),
                           hints_shm, per_child_megs, output_shm);
  safe_free(order);

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
 *   cores_poll_loop_ladr()
 *
 *   Simplified sliding-window loop for LADR-mode -cores: race exactly
 *   n_race DISTINCT strategies concurrently, each running unsliced for
 *   the whole per-child budget -- no suspend/resume, no Phase 1/Phase 2
 *   breadth-then-depth expansion beyond n_race (see docs/cores-ladr-
 *   single-goal-race-spec.md). Every child is spawned with
 *   force_single_proof=TRUE, so whichever finds ANY one proof first
 *   wins; the others are killed and discarded, same publish-winner
 *   mechanics as cores_poll_loop(). Deliberately NOT shared with
 *   cores_poll_loop() itself: this keeps the TPTP-mode scheduler's own
 *   behavior structurally untouched rather than threading a mode flag
 *   through its breadth/depth machinery.
 *
 *   A slot whose strategy finishes without a proof is NOT refilled --
 *   once its distinct strategy is done, it's simply done. Only
 *   n_race strategies are ever tried in one race, never more.
 *
 *   Returns: MAX_PROOFS_EXIT if a proof was found, otherwise the best
 *   non-proof exit code seen (or -1 if nothing exited before the
 *   backstop deadline).
 *
 *************/

static
int cores_poll_loop_ladr(int n_race, int *order, int per_child_sec,
                         int saved_stdout, Prover_input input,
                         int total_deadline,
                         struct child_hints *hints_shm,
                         int per_child_megs_budget,
                         struct child_output *output_shm)
{
  pid_t *slots;
  int *slot_strat;
  int best_code;
  int i;
  unsigned start_time;
  unsigned last_mem_check;

  slots = safe_calloc(n_race, sizeof(pid_t));
  slot_strat = safe_calloc(n_race, sizeof(int));

  best_code = -1;
  start_time = absolute_wallclock();
  last_mem_check = start_time;

  install_parent_death_handler();

  /* Launch all n_race strategies at once -- no breadth-then-depth
     expansion: each runs the full budget uninterrupted (auto_default
     gets total_deadline, matching cores_poll_loop's own treatment;
     everyone else gets per_child_sec, which for this design IS the
     whole time budget, not a short slice). */
  for (i = 0; i < n_race; i++) {
    int si = order[i];
    int slice = (si == AUTO_DEFAULT_IDX) ? total_deadline : per_child_sec;
    pid_t cpid = spawn_child(i, si, i, slice, saved_stdout,
                             output_shm, input, NULL, hints_shm, TRUE);
    if (cpid > 0) {
      slots[i] = cpid;
      slot_strat[i] = si;
#ifdef DEBUG
      fprintf(stderr, "%% Cores(ladr) slot %d [pid %d]: %s (%ds)\n",
              i, (int) cpid, Portfolio[si].name, slice);
#endif
    }
  }

  while (1) {
    int all_empty;
    int elapsed = (int)(absolute_wallclock() - start_time);
    /* Throttle the memory check below to once a second: RSS reads
       (child_rss_megs(), a /proc read or syscall) are cheap
       individually but need not run at the poll loop's own 10ms
       cadence -- once a second is still far more responsive than
       "only at suspend", which this design never does at all. */
    BOOL do_mem_check = (absolute_wallclock() != last_mem_check);
    if (do_mem_check) last_mem_check = absolute_wallclock();

    if (total_deadline > 0 && elapsed >= total_deadline) {
#ifdef DEBUG
      fprintf(stderr, "%% Cores(ladr): backstop deadline (%ds) reached\n",
              total_deadline);
#endif
      for (i = 0; i < n_race; i++) {
        if (slots[i] > 0) { kill_child(slots[i]); slots[i] = 0; }
      }
      break;
    }

    for (i = 0; i < n_race; i++) {
      int status;
      pid_t wpid;

      if (slots[i] <= 0)
        continue;

      /* Memory ejection: same protection cores_poll_loop applies at
         suspend time, checked here on every poll tick (throttled,
         see do_mem_check above) instead since this design has no
         suspend events to hang it off of. Uses real OS-level RSS
         (child_rss_megs()), not hints_shm[i].megs_used -- that
         self-reported figure can go stale for large-theory problems
         stuck inside a preprocessing call with no checkpoints of its
         own, same gap 3733dcd fixed for cores_poll_loop's own
         suspend-time check; this is the same fix applied here too. */
      if (do_mem_check && per_child_megs_budget > 0) {
        long rss_megs = child_rss_megs(slots[i]);
        if (rss_megs >= 0 && rss_megs > per_child_megs_budget) {
#ifdef DEBUG
          fprintf(stderr, "%% Cores(ladr): killed s%d (slot %d): "
                  "%ld MB (RSS) > %d MB budget\n",
                  slot_strat[i], i, rss_megs, per_child_megs_budget);
#endif
          kill_child(slots[i]);
          slots[i] = 0;
          continue;
        }
      }

      wpid = waitpid(slots[i], &status, WNOHANG | WUNTRACED);
      if (wpid == 0)
        continue;  /* still running */

      if (wpid < 0) {
        untrack_child(slots[i]);
        slots[i] = 0;
        continue;
      }

      if (WIFSTOPPED(status)) {
        /* Nothing self-suspends before the deadline in this design --
           if a child's own full-budget alarm fires right as the
           backstop is about to anyway, treat it as done, not
           resumable (there is no resume mechanism here). */
        kill_child(slots[i]);
        slots[i] = 0;
        continue;
      }

      {
        int child_code;
        if (WIFEXITED(status))
          child_code = WEXITSTATUS(status);
        else {
          child_code = FATAL_EXIT;
          if (WIFSIGNALED(status))
            fprintf(stderr, "%% WARNING: Cores(ladr) slot %d (%s): child pid %d "
                    "killed by signal %d (%s)%s\n",
                    i, Portfolio[slot_strat[i]].name, slots[i],
                    WTERMSIG(status), strsignal(WTERMSIG(status)),
                    WCOREDUMP(status) ? ", core dumped" : "");
        }

#ifdef DEBUG
        fprintf(stderr, "%% Cores(ladr) slot %d (%s): exit %d (%s)\n",
                i, Portfolio[slot_strat[i]].name, child_code,
                child_code == MAX_PROOFS_EXIT ? "proof" :
                child_code == SOS_EMPTY_EXIT ? "sos_empty" : "other");
#endif

        if (child_code == MAX_PROOFS_EXIT) {
          int j;
          for (j = 0; j < n_race; j++) {
            if (j != i && slots[j] > 0) {
              kill_child(slots[j]);
              slots[j] = 0;
            }
          }
          if (output_shm) {
            cores_arm_death_from_winner(&output_shm[i]);
            cores_publish_winner(&output_shm[i], saved_stdout);
          }
#ifdef DEBUG
          fprintf(stderr, "%% Cores(ladr) winner: slot %d (%s)\n",
                  i, Portfolio[slot_strat[i]].name);
#endif
          safe_free(slots);
          safe_free(slot_strat);
          return MAX_PROOFS_EXIT;
        }

        if (best_code < 0)
          best_code = child_code;
        else if (child_code == SOS_EMPTY_EXIT)
          best_code = SOS_EMPTY_EXIT;
        else if (child_code == MAX_SECONDS_EXIT &&
                 best_code != SOS_EMPTY_EXIT)
          best_code = MAX_SECONDS_EXIT;

        untrack_child(slots[i]);
        slots[i] = 0;
        /* No refill -- see function comment. */
      }
    }

    all_empty = 1;
    for (i = 0; i < n_race; i++) {
      if (slots[i] > 0) { all_empty = 0; break; }
    }
    if (all_empty)
      break;

    usleep(10000);  /* 10ms poll */
  }

  safe_free(slots);
  safe_free(slot_strat);
  return best_code;
}  /* cores_poll_loop_ladr */

/*************
 *
 *   cores_search_ladr()
 *
 *   LADR-mode -cores entry point: race up to N DISTINCT strategies
 *   (never more than requested, never more than actually exist -- a
 *   request exceeding the portfolio's size just races however many
 *   distinct strategies there are, per jpm's own call) to a single
 *   proof of ANY goal, each running unsliced for the whole time
 *   budget. Does not return (calls exit()).
 *
 *   See docs/cores-ladr-single-goal-race-spec.md for the full
 *   background: -cores was designed for TPTP mode's single-goal,
 *   max_proofs==1 world; LADR mode's own auto_denials() bumps
 *   max_proofs up to the file's goal count for a multi-goal Horn set,
 *   which made every -cores child sweep ALL goals with its own
 *   strategy instead of racing to the first proof of ANY of them.
 *   Deliberately a separate function from cores_search(), not a mode
 *   flag threaded through it -- TPTP mode's own scheduler is completely
 *   untouched by this, structurally, not just by inspection.
 *
 *************/

static
void cores_search_ladr(Prover_input input, int max_strats_arg)
{
  int N = parm(input->options->cores);
  int total_time = parm(input->options->max_seconds);
  /* No -t given (total_time <= 0, LADR's "unset" sentinel): race n_race
     strategies with no time limit at all, rather than silently falling
     back to a single, non-raced auto search -- that fallback used to
     happen with zero diagnostic output, which from the outside is
     indistinguishable from -cores being ignored entirely (found live,
     2026-08-09: -cores 4 with no -t showed exactly one prover9 process
     for the whole run). We deliberately do NOT invent a default time
     limit here (e.g. some large sentinel) -- if the user didn't ask for
     one, there isn't one; each racer just runs to its own natural
     conclusion (proof or SOS-exhausted) and the loop below already
     treats a <=0 deadline as "no backstop" and a 0 per-child slice as
     "no alarm" (setup_timeout_signal/alarm() semantics), so passing a
     genuine 0 through -- not the raw -1 sentinel, whose arithmetic
     (total_time+2) would arm a bogus near-immediate deadline -- gets
     unbounded racing for free from machinery that already existed. */
  BOOL unbounded = (total_time <= 0);
  int max_megs_val = parm(input->options->max_megs);
  int num_strats = NUM_PORTFOLIO_STRATS;
  int cap;
  int n_race;
  int *order;
  int saved_stdout;
  int result;
  int per_child_megs;
  struct child_hints *hints_shm;
  struct child_output *output_shm;

  if (N <= 0)
    return;  /* fall through to single strategy */

  /* -strategies N (if given) caps how many distinct strategies to
     race, same as it caps cores_search's Phase 1 breadth; otherwise
     race up to N (the -cores value), capped by however many distinct
     strategies the portfolio actually has. */
  cap = num_strats;
  if (max_strats_arg > 0 && max_strats_arg < cap)
    cap = max_strats_arg;
  n_race = (N < cap) ? N : cap;

  /* Per-child memory budget: same treatment as cores_search()/
     cores_from_scan() above -- always enforced (unless max_megs is
     explicitly -1), with a machine-aware default (80% of real RAM)
     when the user never set max_megs at all, instead of the old
     <=8192MB opt-in gate (which left this LADR-native racing path
     completely uncapped by default, same gap as the other two
     entry points had before 2f46dd1/6c10103). n_race (not
     phase1_limit) is already the correct divisor here: this mode
     races a flat, unsliced n_race<=N with no Phase-1 breadth pool. */
  if (max_megs_val > 0) {
    if (!parm_is_user_set(input->options->max_megs)) {
      long ram_megs = system_ram_megs();
      if (ram_megs > 0)
        max_megs_val = (int) (ram_megs * 0.8);
    }
    per_child_megs = max_megs_val / n_race;
  }
  else
    per_child_megs = 0;  /* max_megs explicitly disabled (-1) */

  order = safe_malloc(num_strats * sizeof(int));
  build_cores_order(NULL, 0, order, num_strats);  /* LADR: no ML ranking */

  saved_stdout = dup(STDOUT_FILENO);

  hints_shm = (struct child_hints *) mmap(NULL,
      n_race * sizeof(struct child_hints),
      PROT_READ | PROT_WRITE,
      MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (hints_shm == MAP_FAILED)
    hints_shm = NULL;
  else
    memset(hints_shm, 0, n_race * sizeof(struct child_hints));

  output_shm = (struct child_output *) mmap(NULL,
      n_race * sizeof(struct child_output),
      PROT_READ | PROT_WRITE,
      MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (output_shm == MAP_FAILED) {
    /* Losing this buffer silently disables output capture for every child
       spawned from here on (spawn_child only redirects a child's stdout to
       a memstream when output_shm is non-NULL) -- the eventual winner-
       publish fallback further down handles the "no captured output"
       case, but the root cause (why the mmap itself failed) is worth a
       permanent, unconditional record: this is small (a few dozen MB at
       most) and every prior anonymous mmap in this same process already
       succeeded, so a failure here means something environmental (an
       existing memory-mapping-count limit, transient memory pressure from
       many concurrent -cores instances, etc.), not this allocation being
       unreasonably large. */
    fprintf(stderr, "%% WARNING: Cores: output_shm mmap failed (%s) -- "
                    "winner output will be uncapturable this run.\n",
            strerror(errno));
    output_shm = NULL;
  }

  fflush(stdout);
  fflush(stderr);

  /* Disarm parent's SIGALRM so the poll loop manages its own timing. */
  {
    struct itimerval disarm;
    memset(&disarm, 0, sizeof(disarm));
    setitimer(ITIMER_REAL, &disarm, NULL);
  }

  cores_arm_death_status(saved_stdout, flag(input->options->tptp_output),
                         input->problem_name);

  result = cores_poll_loop_ladr(n_race, order, unbounded ? 0 : total_time,
                                saved_stdout, input,
                                unbounded ? 0 : (total_time + 2),
                                hints_shm, per_child_megs, output_shm);
  safe_free(order);

  if (hints_shm)
    munmap(hints_shm, n_race * sizeof(struct child_hints));
  if (output_shm)
    munmap(output_shm, n_race * sizeof(struct child_output));

  if (result == MAX_PROOFS_EXIT) {
    close(saved_stdout);
    exit(MAX_PROOFS_EXIT);
  }

  cores_emit_no_proof(saved_stdout, result,
                      input->options, input->problem_name);
  /* Does not return */
}  /* cores_search_ladr */

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
  /* No -t given: race exactly N strategies with no time limit, same
     fix/rationale as cores_search()/cores_search_ladr() (2026-08-09). */
  BOOL unbounded = (total_time <= 0);
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

  if (N <= 0)
    return;  /* fall through to single strategy */

  if (unbounded) {
    phase1_limit = N;
    per_child_sec = 0;
  }
  else {
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
  }

  /* Per-child memory budget: same fix and rationale as cores_search()'s
     identical block above -- always enforced (unless max_megs is
     explicitly -1), scaled to phase1_limit rather than the unrelated
     num_strats constant, closing the same uncapped-breadth-pool gap for
     this (>5000-axiom) SInE entry point too. */
  if (max_megs_val > 0) {
    /* Same machine-aware default as cores_search() above -- an
       untouched max_megs is still just the 48GB compiled-in constant,
       not a real signal the user wants that specific figure for
       -cores. Swap it for 80% of real RAM when untouched; an explicit
       assign(max_megs,N) always wins. */
    if (!parm_is_user_set(psr->options->max_megs)) {
      long ram_megs = system_ram_megs();
      if (ram_megs > 0)
        max_megs_val = (int) (ram_megs * 0.8);
    }
    per_child_megs = max_megs_val / phase1_limit;
  }
  else
    per_child_megs = 0;  /* max_megs explicitly disabled (-1) */

  order = safe_malloc(num_strats * sizeof(int));
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

  /* Allocate shared-memory output buffers (16 MB per slot, indexed by
     order_idx -- a suspended child can be resumed into a different
     physical slot than it was spawned into, so this must be sized for
     the full order_idx range (phase1_limit), not just N slots. */
  output_shm = (struct child_output *) mmap(NULL,
      phase1_limit * sizeof(struct child_output),
      PROT_READ | PROT_WRITE,
      MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  if (output_shm == MAP_FAILED) {
    /* Losing this buffer silently disables output capture for every child
       spawned from here on (spawn_child only redirects a child's stdout to
       a memstream when output_shm is non-NULL) -- the eventual winner-
       publish fallback further down handles the "no captured output"
       case, but the root cause (why the mmap itself failed) is worth a
       permanent, unconditional record: this is small (a few dozen MB at
       most) and every prior anonymous mmap in this same process already
       succeeded, so a failure here means something environmental (an
       existing memory-mapping-count limit, transient memory pressure from
       many concurrent -cores instances, etc.), not this allocation being
       unreasonably large. */
    fprintf(stderr, "%% WARNING: Cores: output_shm mmap failed (%s) -- "
                    "winner output will be uncapturable this run.\n",
            strerror(errno));
    output_shm = NULL;
  }


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

  cores_arm_death_status(saved_stdout, flag(psr->options->tptp_output), pname);

  result = cores_poll_loop(N, order, num_strats, phase1_limit, per_child_sec,
                           saved_stdout, NULL, psr,
                           unbounded ? 0 : (total_time + 2),
                           hints_shm, per_child_megs, output_shm);
  safe_free(order);

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

#endif /* !NO_OPEN_MEMSTREAM */
#endif /* !__EMSCRIPTEN__ */

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
  BOOL cnf_only = FALSE;
#ifndef __EMSCRIPTEN__
  int force_strategy = -1;  /* -strategy N: force portfolio index */
  int max_strategies = -1;  /* -strategies N: cap Phase 1 breadth */
  int slice_sec = -1;       /* -slice N: per-child time slice override */
#endif

  /* Raise the stack limit before any parsing: the TPTP recursive-descent
     parser has no iterative fallback, and a legitimately very deeply
     nested input can otherwise overflow the OS default stack. Inherited
     by -cores children via fork(), so this one call covers them too. */
  raise_stack_limit();

  /* Save original command line before any argv mutation. */
  saved_command = build_command_string(argc, argv);

#ifndef __EMSCRIPTEN__
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
#endif

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

  /* Check for -modern_parse flag: opt-in precedence-climbing LADR-native
     parser instead of the classic backtracking one -- see the "modern
     LADR parser" comment in ladr/parse.c for what this trades away.
     Must neutralize argv[i] like -strategy/-strategies/-slice above:
     std_prover_init_and_input() later runs getopt() with an optstring
     containing "r:" (for -r, resume-from-checkpoint), and getopt reads
     an unrecognized long flag as a cluster of short options -- it would
     otherwise walk into the 'r' in "-modern_parse" and swallow the rest
     of the token ("n_parse") as -r's argument. */
  {
    int i;
    for (i = 1; i < argc; i++) {
      if (strcmp(argv[i], "-modern_parse") == 0 ||
          strcmp(argv[i], "-modern-parse") == 0) {
        use_modern_ladr_parser(TRUE);
        argv[i] = "-_";  /* neutralize so getopt skips it */
        break;
      }
    }
  }

  /* Check for -cnf flag (clausify-only mode: output cnf() lines, no search) */
  {
    int i;
    for (i = 1; i < argc; i++) {
      if (strcmp(argv[i], "-cnf") == 0) {
        cnf_only = TRUE;
        tptp_mode = TRUE;   /* -cnf implies TPTP I/O */
        nosine = TRUE;       /* output all clauses, no SInE filtering */
        break;
      }
    }
  }

  if (!cnf_only)
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

  if (tptp_mode)
    set_tptp_mode_for_sig();  /* SZS status in signal handler */

  /***************** Initialize and read the input ***************************/

#ifdef __EMSCRIPTEN__
  /* WASM mode: no fork/cores/strategy scheduling.
     Use std_prover_init_and_input for both TPTP and LADR. */
  input = std_prover_init_and_input(argc, argv, TRUE, TRUE, KILL_UNKNOWN);

  if (nosine) {
    assign_parm(input->options->sine, 0, FALSE);
    clear_flag(input->options->multi_order_trial, FALSE);
  }
  if (nomem)
    disable_max_megs();

#else /* native */

  if (tptp_mode && cnf_only) {
    /* CNF-only mode: simple init + clausify, no strategy scheduling.
       echo=FALSE suppresses intermediate output to stdout so only
       the cnf() lines we emit at the end appear. */
    input = std_prover_init_and_input(argc, argv, TRUE, FALSE, KILL_UNKNOWN);
    assign_parm(input->options->sine, 0, FALSE);
    if (nomem) disable_max_megs();
  }
  else if (tptp_mode) {
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
      ml_ranking = ml_rank(psr->scan, &ml_ranking_len);
      if (ml_ranking != NULL && ml_ranking_len > 0)
        ml_pick = (int) ml_ranking[0];
      else
        ml_pick = ml_classify(psr->scan);
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

#ifndef NO_OPEN_MEMSTREAM
      /* Sliding-window cores (from scan) for large inputs.  No cmd_max_sec
         gate: an unset/non-positive value means "no -t given", and
         cores_from_scan() itself now races unbounded in that case
         (2026-08-09) rather than silently skipping -cores entirely --
         only assign it into the options when it's a genuine positive
         value the user actually gave. */
      if (force_strategy < 0 &&
          parm(psr->options->cores) > 0 &&
          psr->scan != NULL &&
          psr->scan->n_axioms > 5000) {
        if (cmd_max_sec > 0)
          assign_parm(psr->options->max_seconds, cmd_max_sec, FALSE);
        cores_from_scan(psr, ml_ranking, ml_ranking_len, max_strategies, slice_sec);
        /* Does not return on success. Falls through on fork failure. */
      }
#endif
    }

    /* Single-strategy or small input: complete phase 2 normally. */
    input = std_prover_from_scan(psr, -1, -1, -1);

#ifndef NO_OPEN_MEMSTREAM
    /* Sliding-window cores (post-clausify) for small inputs.  No
       max_seconds gate here either -- see the from-scan branch above
       and cores_search()'s own 2026-08-09 fix for the rationale. */
    if (force_strategy < 0 &&
        parm(input->options->cores) > 0) {
      cores_search(input, ml_ranking, ml_ranking_len, max_strategies, slice_sec);
      /* Does not return on success. */
    }
#endif

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

#ifndef NO_OPEN_MEMSTREAM
    /* No max_seconds gate -- see cores_search_ladr()'s own 2026-08-09
       fix for the rationale (race unbounded rather than silently
       skipping -cores when no -t was given). */
    if (parm(input->options->cores) > 0) {
      cores_search_ladr(input, max_strategies);
    }
#endif
  }

#endif /* __EMSCRIPTEN__ */

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

  /***************** CNF-only: set flag and fall through to search() *********/

  /***************** CNF-only output (if -cnf flag) *************************/

  if (cnf_only) {
    Plist p;
    /* Ensure all clauses have IDs */
    for (p = input->usable; p; p = p->next) {
      Topform c = p->v;
      if (c->id == 0) assign_clause_id(c);
    }
    for (p = input->sos; p; p = p->next) {
      Topform c = p->v;
      if (c->id == 0) assign_clause_id(c);
    }
    /* Post-clausification simplification: apply the same three
       transforms that search()/cl_process_simplify() applies to
       initial clauses before proof search.  Without these, the
       raw CNF output differs from what appears as proof leaves -
       equalities may be unoriented, duplicate literals unsimplified,
       and trivial literals (x=x) unremoved.  These are standalone
       LADR library functions with no Glob/Opt dependencies. */
    for (p = input->usable; p; p = p->next) {
      orient_equalities(p->v, TRUE);
      simplify_literals2(p->v);
      merge_literals(p->v);
    }
    for (p = input->sos; p; p = p->next) {
      orient_equalities(p->v, TRUE);
      simplify_literals2(p->v);
      merge_literals(p->v);
    }
    /* TPTP output formatting */
    set_variable_style(PROLOG_STYLE);
    clear_parse_type_for_all_symbols();
    declare_tptp_output_types();
    /* Output all clauses in TPTP cnf() format */
    for (p = input->usable; p; p = p->next)
      fwrite_clause(stdout, p->v, CL_FORM_TSTP);
    for (p = input->sos; p; p = p->next)
      fwrite_clause(stdout, p->v, CL_FORM_TSTP);
    fflush(stdout);
    exit(0);
  }

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
