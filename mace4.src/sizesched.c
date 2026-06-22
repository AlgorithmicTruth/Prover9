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

  if (pipe(pfd) != 0)
    return -1;

  pid = fork();
  if (pid < 0) {
    close(pfd[0]); close(pfd[1]);
    return -1;
  }

  if (pid == 0) {
    /* ---- child ---- */
    /* Restore default signal handling; the parent owns the deadline. */
    signal(SIGALRM, SIG_DFL);
    signal(SIGTERM, SIG_DFL);
    signal(SIGINT,  SIG_DFL);
#ifdef SIGXCPU
    signal(SIGXCPU, SIG_DFL);
#endif
    /* Redirect stdout to the pipe so the model we print is captured. */
    close(pfd[0]);
    dup2(pfd[1], STDOUT_FILENO);
    close(pfd[1]);

    int code = mace4_one_size_exit_code(clauses, size);
    fflush(stdout);
    _exit(code);
  }

  /* ---- parent ---- */
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

  /* Parent owns the deadline.  mace4.c armed SIGALRM/SIGXCPU from -t /
     max_seconds; install our handler so they set Deadline_hit instead of
     calling mace4_exit (which would print from the parent prematurely). */
  signal(SIGALRM, sizesched_sig_handler);
  signal(SIGTERM, sizesched_sig_handler);
  signal(SIGINT,  sizesched_sig_handler);
#ifdef SIGXCPU
  signal(SIGXCPU, sizesched_sig_handler);
#endif

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
        drain_kid(&kids[i]);
        kids[i].exit_code = WIFEXITED(status) ? WEXITSTATUS(status) : -1;
        close(kids[i].fd); kids[i].fd = -1;
        kids[i].done = 1;

        int code = kids[i].exit_code;
        int sz   = kids[i].size;

        if (code == MAX_MODELS_EXIT || code == ALL_MODELS_EXIT ||
            code == MAX_SEC_YES_EXIT || code == MAX_MEGS_YES_EXIT) {
          /* This size found a model. */
          if (sz < best_size) {
            best_size = sz;
            if (best_text) zap_string_buf(best_text);
            best_text = kids[i].buf;
            kids[i].buf = NULL;              /* ownership moved to best_text */
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
    /* Relay the winning child's captured model output verbatim.
       Use fprint_sb (walks the chunk list once, O(n)); a per-index
       sb_char loop would be O(n^2) and can take tens of seconds on
       multi-megabyte models (e.g. NLP054+1's 2.5 MB model). */
    fprint_sb(stdout, best_text);
    fflush(stdout);
    zap_string_buf(best_text);
    results->success = TRUE;
    /* ALL_MODELS_EXIT maps to Satisfiable/CounterSatisfiable in
       mace4_exit via mace4_szs_status (it checks Mace4_has_goals). */
    results->return_code = ALL_MODELS_EXIT;
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
