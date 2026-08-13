/*  Copyright (C) 2026 Jeffrey P. Machado, Larry Lesyna

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

/*
 *  sizesched.c -- parallel-over-domain-sizes scheduler for Mace4 (-cores N).
 *
 *  Mace4 normally searches domain sizes sequentially, smallest first.
 *  With -cores N (>1) this scheduler races up to N domain sizes
 *  concurrently, one forked child per size, each running the existing
 *  single-size search (mace4_one_size_exit_code) UNCHANGED.  The search
 *  core is untouched; only this orchestration is new.
 *
 *  Semantics (the important part):
 *    - The smallest model is the desired answer.  A child that finds a
 *      model does NOT cause immediate output: the parent retains the
 *      smallest model found so far and keeps smaller sizes running while
 *      wall-clock remains, hoping for a smaller one.
 *    - The retained best model is published when (a) the wall clock runs
 *      out (SIGALRM/SIGXCPU/SIGTERM), or (b) it is proven minimal (no
 *      smaller size remains to run), whichever happens first.
 *    - Status:
 *        model found      -> Satisfiable / CounterSatisfiable
 *        no model, clock  -> Timeout       (we timed out)
 *        no model, we
 *          chose to stop  -> GaveUp        (range/overflow exhausted)
 *
 *  Fork-only (no exec): children are forked AFTER initialize_for_search()
 *  has run in the parent, so they inherit the parsed/clausified problem
 *  in memory -- no re-parse.  Each child redirects stdout to a pipe; the
 *  model it prints is captured by the parent and relayed for the winner.
 *
 *  Not used for: resume, arithmetic, iterate_primes/nonprimes (those
 *  assume ordered single-process state) -- mace4() falls through to the
 *  sequential loop in those cases.
 */

#include "msearch.h"

#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/select.h>
#include <signal.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>

/* Deadline flag, set by the parent's signal handler. */
static volatile sig_atomic_t Deadline_hit = 0;

static void sizesched_sig_handler(int sig)
{
  (void) sig;
  Deadline_hit = 1;
}

/* ---- Async-safe external-kill reporting --------------------------------
   The competition infrastructure kills the whole process group with
   SIGTERM (or SIGXCPU) and follows with SIGKILL after a short grace.
   With 8 busy children the job's CPU budget is spent at ~1/8 the wall
   rate, so this arrives long before the internal wall timer.  Deferring
   the report to the main loop (the Deadline_hit path) loses the race:
   by the time the loop runs, the SIGKILL may have landed -- that was
   669 silent no-status outputs in one StarExec run.  Instead everything
   the handler needs is pre-rendered in normal context, and the handler
   only kill()s, write()s, and _exit()s (all async-signal-safe).
   If a best model has been retained it is published (model text +
   CounterSatisfiable/Satisfiable); otherwise a Timeout line.  A non-TPTP
   run pre-renders nothing and just exits. */

#define MAX_KIDS_TRACK 64
static volatile pid_t Sched_kid_pids[MAX_KIDS_TRACK];

static char *Death_buf = NULL;              /* pre-rendered output+status */
static volatile sig_atomic_t Death_len = 0;
static char  Death_line[300];               /* pre-rendered status line only */
static volatile sig_atomic_t Death_line_len = 0;
static volatile sig_atomic_t Death_exit_code = 0;
static volatile sig_atomic_t Publish_started = 0;  /* graceful path owns output */

static void sched_track_kid(pid_t pid)
{
  int i;
  for (i = 0; i < MAX_KIDS_TRACK; i++)
    if (Sched_kid_pids[i] == 0) { Sched_kid_pids[i] = pid; return; }
}

static void sched_untrack_kid(pid_t pid)
{
  int i;
  for (i = 0; i < MAX_KIDS_TRACK; i++)
    if (Sched_kid_pids[i] == pid) { Sched_kid_pids[i] = 0; return; }
}

/* Pre-render what the death handler should write.  model_text == NULL
   means no model retained yet (render a Timeout line).  Swap order keeps
   the handler safe at every interleaving: it reads Death_len first, and
   the pointer is already valid whenever the length is nonzero. */
static void arm_death_output(String_buf model_text)
{
  char *old = Death_buf;
  char *nb;
  int n = 0;
  char line[300];
  int linelen;
  const char *szs;
  sigset_t block_set, old_set;

  if (!Mace4_tptp_mode) {
    Death_len = 0;
    return;
  }
  /* Block the kill signals for the duration: a SIGTERM/SIGXCPU landing
     mid-swap would find Death_len == 0 and the handler would write
     nothing -- a blank, the exact defect this machinery prevents. */
  sigemptyset(&block_set);
  sigaddset(&block_set, SIGTERM);
#ifdef SIGXCPU
  sigaddset(&block_set, SIGXCPU);
#endif
  sigprocmask(SIG_BLOCK, &block_set, &old_set);
  szs = model_text ? (Mace4_has_goals ? "CounterSatisfiable" : "Satisfiable")
                   : "Timeout";
  if (Mace4_problem_name && Mace4_problem_name[0])
    linelen = snprintf(line, sizeof(line), "\n%% SZS status %s for %s\n",
                       szs, Mace4_problem_name);
  else
    linelen = snprintf(line, sizeof(line), "\n%% SZS status %s\n", szs);
  if (linelen < 0) linelen = 0;
  else if (linelen > (int) sizeof(line)) linelen = (int) sizeof(line);

  if (model_text != NULL) {
    /* Status-first for the SZS FiniteModel path: the status line precedes
       the model, so a kill that truncates the (possibly multi-megabyte)
       model relay still shows the solve.  -ladr_out has no SZS block, so it
       keeps the status last, matching its non-killed output. */
    char *mt = sb_to_malloc_string(model_text);
    int mlen = (int) strlen(mt);
    nb = safe_malloc(mlen + linelen + 1);
    if (Mace4_ladr_output) {
      memcpy(nb, mt, mlen);
      memcpy(nb + mlen, line, linelen);
    }
    else {
      memcpy(nb, line, linelen);
      memcpy(nb + linelen, mt, mlen);
    }
    n = mlen + linelen;
    safe_free(mt);
  }
  else {
    nb = safe_malloc(linelen + 1);
    memcpy(nb, line, linelen);
    n = linelen;
  }

  Death_len = 0;          /* handler now skips writing */
  Death_buf = nb;         /* pointer valid before length is set */
  Death_len = n;
  memcpy(Death_line, line, linelen);
  Death_line_len = linelen;
  Death_exit_code = model_text ? MAX_MODELS_EXIT : MAX_SEC_NO_EXIT;
  if (old != NULL)
    safe_free(old);
  sigprocmask(SIG_SETMASK, &old_set, NULL);
}

/* Retry-safe raw write for the handler. */
static void death_write(const char *buf, int len)
{
  int off = 0;
  while (off < len) {
    ssize_t w = write(STDOUT_FILENO, buf + off, (size_t) (len - off));
    if (w <= 0) break;
    off += (int) w;
  }
}

static void sizesched_death_handler(int sig)
{
  int i;
  (void) sig;
  for (i = 0; i < MAX_KIDS_TRACK; i++) {
    if (Sched_kid_pids[i] > 0) {
      kill(Sched_kid_pids[i], SIGCONT);
      kill(Sched_kid_pids[i], SIGKILL);
    }
  }
  /* Three states, exactly one status line in every interleaving:
       (a) publish not started: write the pre-rendered output, status
           line FIRST then the model (or just the Timeout line);
       (b) publish under way but the graceful status has not been
           printed yet (killed in the tiny window after Publish_started
           but before the status write): emit ONLY the status line;
       (c) status already printed (by the publish path or mace4_exit):
           write nothing -- the model relay may be truncated, harmlessly. */
  if (!Mace4_szs_printed) {
    if (!Publish_started)
      death_write(Death_buf, (int) Death_len);
    else
      death_write(Death_line, (int) Death_line_len);
  }
  _exit((int) Death_exit_code);
}

/* One running child. */
struct kid {
  pid_t pid;
  int   size;
  int   fd;          /* read end of the child's stdout pipe */
  String_buf buf;    /* accumulated child stdout (the model text, if any) */
  int   done;        /* reaped + drained */
  int   exit_code;
};

#define MAX_KIDS 64

/* Read whatever is available on a kid's pipe into its buffer. */
static void drain_kid(struct kid *k)
{
  char tmp[4096];
  ssize_t n;
  if (k->fd < 0) return;
  while ((n = read(k->fd, tmp, sizeof(tmp))) > 0) {
    int i;
    for (i = 0; i < n; i++)
      sb_append_char(k->buf, tmp[i]);
  }
  /* n == 0: EOF (child closed/exited).  n < 0 with EAGAIN: no more now. */
}

/* Fork a child to search exactly one domain size.  Returns pid, sets
   *out_fd to the read end of its stdout pipe.  Child never returns. */
static pid_t fork_size_child(Plist clauses, int size, int *out_fd)
{
  int pfd[2];
  pid_t pid;
  sigset_t fork_block, fork_old;

  if (pipe(pfd) != 0)
    return -1;

  /* Block the status-writing signals across the fork: a group-kill
     SIGTERM delivered before the child is first scheduled would fire
     the INHERITED sizesched_death_handler with fd 1 still the real
     stdout, adding a second status line next to the parent's (the
     prover9 Job7086 double-status race; same window here). */
  sigemptyset(&fork_block);
  sigaddset(&fork_block, SIGTERM);
  sigaddset(&fork_block, SIGALRM);
  sigaddset(&fork_block, SIGINT);
#ifdef SIGXCPU
  sigaddset(&fork_block, SIGXCPU);
#endif
  sigprocmask(SIG_BLOCK, &fork_block, &fork_old);

  pid = fork();
  if (pid < 0) {
    sigprocmask(SIG_SETMASK, &fork_old, NULL);
    close(pfd[0]); close(pfd[1]);
    return -1;
  }

  if (pid == 0) {
    /* ---- child ---- */
    int code;
    /* Restore default signal handling; the parent owns the deadline. */
    signal(SIGALRM, SIG_DFL);
    signal(SIGTERM, SIG_DFL);
    signal(SIGINT,  SIG_DFL);
#ifdef SIGXCPU
    signal(SIGXCPU, SIG_DFL);
#endif
    /* Deliver anything pending only now that dispositions are default. */
    sigprocmask(SIG_SETMASK, &fork_old, NULL);
    /* Redirect stdout to the pipe so the model we print is captured. */
    close(pfd[0]);
    dup2(pfd[1], STDOUT_FILENO);
    close(pfd[1]);

    /* This child prints only the model to the pipe; the parent emits the
       SZS status line, status-first, when it publishes the winner. */
    Mace4_cores_child = 1;

    code = mace4_one_size_exit_code(clauses, size);
    fflush(stdout);
    _exit(code);
  }

  /* ---- parent ---- */
  sigprocmask(SIG_SETMASK, &fork_old, NULL);
  close(pfd[1]);
  /* non-blocking reads so drain_kid never blocks */
  {
    int fl = fcntl(pfd[0], F_GETFL, 0);
    if (fl != -1) fcntl(pfd[0], F_SETFL, fl | O_NONBLOCK);
  }
  *out_fd = pfd[0];
  return pid;
}

static void kill_kid(struct kid *k)
{
  if (k->pid > 0 && !k->done) {
    kill(k->pid, SIGKILL);
    waitpid(k->pid, NULL, 0);
    sched_untrack_kid(k->pid);
  }
  if (k->fd >= 0) { close(k->fd); k->fd = -1; }
  k->done = 1;
}

/* PUBLIC */
Mace_results mace4_parallel(Plist clauses, Mace_options opt, int ncores)
{
  Mace_results results = safe_malloc(sizeof(struct mace_results));
  struct kid kids[MAX_KIDS];
  int nkids = 0, i;
  int start = parm(opt->start_size);
  int end   = parm(opt->end_size);          /* -1 == unbounded */
  int incr  = parm(opt->increment);
  int next  = start;

  int best_size = INT_MAX;
  String_buf best_text = NULL;               /* winning model's stdout */
  int overflow_floor = INT_MAX;              /* sizes >= this are unlaunchable */
  int decided_to_stop = 0;                   /* hit range/overflow with nothing smaller left */
  double t0 = user_seconds();

  if (ncores > MAX_KIDS) ncores = MAX_KIDS;
  if (ncores < 1) ncores = 1;

  /* Parent owns the deadline.  SIGALRM (our internal wall timer) and
     SIGINT (interactive) set Deadline_hit and let the main loop publish
     gracefully.  SIGTERM/SIGXCPU are the competition infrastructure's
     kill -- typically followed quickly by SIGKILL -- so they must be
     answered inside the handler (see sizesched_death_handler). */
  signal(SIGALRM, sizesched_sig_handler);
  signal(SIGINT,  sizesched_sig_handler);
  signal(SIGTERM, sizesched_death_handler);
#ifdef SIGXCPU
  signal(SIGXCPU, sizesched_death_handler);
#endif
  memset((void *) Sched_kid_pids, 0, sizeof(Sched_kid_pids));
  Publish_started = 0;
  arm_death_output(NULL);   /* Timeout line until a model is retained */

  while (!Deadline_hit) {
    /* Launch the smallest still-useful sizes into idle slots. */
    while (nkids < ncores &&
           next >= start &&
           next < best_size &&
           next < overflow_floor &&
           (end < 0 || next <= end)) {
      int fd = -1;
      pid_t pid = fork_size_child(clauses, next, &fd);
      if (pid < 0) break;                    /* fork failed; try later */
      sched_track_kid(pid);
      kids[nkids].pid = pid;
      kids[nkids].size = next;
      kids[nkids].fd = fd;
      kids[nkids].buf = get_string_buf();
      kids[nkids].done = 0;
      kids[nkids].exit_code = -1;
      nkids++;
      next += incr;
    }

    if (nkids == 0) {
      /* Nothing running and nothing left to launch that could improve
         best.  If we never found a model and we stopped because the
         size range/overflow was exhausted (not the clock), that's a
         deliberate stop -> GaveUp. */
      if (best_text == NULL)
        decided_to_stop = 1;
      break;
    }

    /* Wait for activity on any child pipe, with a short timeout so we
       re-check Deadline_hit promptly even if no pipe data arrives. */
    {
      fd_set rset;
      int maxfd = -1;
      struct timeval tv;
      FD_ZERO(&rset);
      for (i = 0; i < nkids; i++) {
        if (kids[i].fd >= 0) {
          FD_SET(kids[i].fd, &rset);
          if (kids[i].fd > maxfd) maxfd = kids[i].fd;
        }
      }
      tv.tv_sec = 0; tv.tv_usec = 200000;    /* 0.2s */
      if (maxfd >= 0)
        select(maxfd + 1, &rset, NULL, NULL, &tv);
      else
        break;
    }

    if (Deadline_hit) break;

    /* Drain pipes and reap any children that have exited. */
    for (i = 0; i < nkids; i++) {
      int status;
      pid_t w;
      if (kids[i].done) continue;
      drain_kid(&kids[i]);
      w = waitpid(kids[i].pid, &status, WNOHANG);
      if (w == kids[i].pid) {
        /* Child exited: final drain to capture trailing output. */
        int code;
        int sz;
        drain_kid(&kids[i]);
        sched_untrack_kid(kids[i].pid);
        kids[i].exit_code = WIFEXITED(status) ? WEXITSTATUS(status) : -1;
        close(kids[i].fd); kids[i].fd = -1;
        kids[i].done = 1;

        code = kids[i].exit_code;
        sz   = kids[i].size;

        if (code == MAX_MODELS_EXIT || code == ALL_MODELS_EXIT ||
            code == MAX_SEC_YES_EXIT || code == MAX_MEGS_YES_EXIT) {
          /* This size found a model. */
          if (sz < best_size) {
            best_size = sz;
            if (best_text) zap_string_buf(best_text);
            best_text = kids[i].buf;
            kids[i].buf = NULL;              /* ownership moved to best_text */
            /* Keep the death handler's pre-rendered output current, so an
               external kill from here on publishes this model. */
            arm_death_output(best_text);
          }
        }
        else if (code == MACE_CELLS_OVERFLOW_EXIT) {
          /* Larger sizes are only worse: don't launch sizes >= sz. */
          if (sz < overflow_floor) overflow_floor = sz;
        }
        /* EXHAUSTED_EXIT / MACE_DOMAIN_OOR_EXIT / MAX_SEC_NO_EXIT:
           no model at this size; smaller sizes remain candidates. */
      }
    }

    /* Compaction + supersede: kill any child that can no longer help
       (size >= best_size or size >= overflow_floor), and drop finished
       slots from the array. */
    {
      int j = 0;
      for (i = 0; i < nkids; i++) {
        if (!kids[i].done &&
            (kids[i].size >= best_size || kids[i].size >= overflow_floor))
          kill_kid(&kids[i]);
        if (kids[i].done) {
          if (kids[i].buf) { zap_string_buf(kids[i].buf); kids[i].buf = NULL; }
          continue;                          /* drop from array */
        }
        kids[j++] = kids[i];
      }
      nkids = j;
    }

    /* If we have a best model and nothing smaller can still run, it is
       proven minimal -- publish now without waiting out the clock. */
    if (best_text != NULL && nkids == 0 &&
        (next >= best_size || next < start || (end >= 0 && next > end)))
      break;
  }

  /* Deadline or decision: stop everything still running. */
  for (i = 0; i < nkids; i++)
    kill_kid(&kids[i]);
  for (i = 0; i < nkids; i++)
    if (kids[i].buf) { zap_string_buf(kids[i].buf); kids[i].buf = NULL; }

  /* ---- publish ---- */
  results->models = NULL;
  results->user_seconds = user_seconds() - t0;

  if (best_text != NULL) {
    Publish_started = 1;   /* death handler switches to status-line-only */
    /* Emit the SZS status line FIRST, then relay the model.  The winning
       child printed only the model to its pipe (Mace4_cores_child suppressed
       its status), so the parent owns the status here.  Claim the one-status
       slot (Mace4_szs_printed) under a signal block so a concurrent external
       kill neither doubles the status nor blanks it; afterwards mace4_exit
       and the death handler add nothing.  Status-first means a truncated
       model relay still credits the solve. */
    /* Only the SZS FiniteModel output path is status-first; -ladr_out emits
       a LADR-format model with no SZS block, so it keeps the status at the
       end via mace4_exit (Mace4_szs_printed stays clear here). */
    if (!Mace4_ladr_output) {
      const char *szs = Mace4_has_goals ? "CounterSatisfiable" : "Satisfiable";
      sigset_t block_set, old_set;
      sigemptyset(&block_set);
      sigaddset(&block_set, SIGTERM);
      sigaddset(&block_set, SIGINT);
      sigaddset(&block_set, SIGALRM);
#ifdef SIGXCPU
      sigaddset(&block_set, SIGXCPU);
#endif
      sigprocmask(SIG_BLOCK, &block_set, &old_set);
      if (!Mace4_szs_printed) {
        Mace4_szs_printed = 1;
        if (Mace4_problem_name)
          printf("\n%% SZS status %s for %s\n", szs, Mace4_problem_name);
        else
          printf("\n%% SZS status %s\n", szs);
        fflush(stdout);
      }
      sigprocmask(SIG_SETMASK, &old_set, NULL);
    }
    /* Relay the winning child's captured model output verbatim.
       Use fprint_sb (walks the chunk list once, O(n)); a per-index
       sb_char loop would be O(n^2) and can take tens of seconds on
       multi-megabyte models (e.g. NLP054+1's 2.5 MB model). */
    fprint_sb(stdout, best_text);
    fflush(stdout);
    zap_string_buf(best_text);
    results->success = TRUE;
    /* MAX_MODELS_EXIT (the default max_models=1 "found a model" code) to match
       the sequential path's exit code (msearch.c uses MAX_MODELS_EXIT here, =0;
       ALL_MODELS_EXIT is 3 and would make -cores report a different exit code
       than sequential for the same result -- which can make StarExec/CASC
       tooling misread a valid Satisfiable/CounterSatisfiable as an error).
       Both codes map to the same model-found SZS status via mace4_szs_status. */
    results->return_code = MAX_MODELS_EXIT;
  }
  else if (Deadline_hit && !decided_to_stop) {
    results->success = FALSE;
    results->return_code = MAX_SEC_NO_EXIT;   /* -> Timeout */
  }
  else {
    results->success = FALSE;
    results->return_code = EXHAUSTED_EXIT;    /* -> GaveUp */
  }

  return results;
}  /* mace4_parallel */
