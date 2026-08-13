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

#include "nonport.h"
#include <string.h>
#include <stdlib.h>   /* getenv */

/* Private definitions and types */

#ifdef PRIMITIVE_ENVIRONMENT
/* This means that we don't have some UNIXy things */
#else
#  include <unistd.h>
#  include <sys/resource.h>
#  if !defined(LADR_STATIC)
#    include <pwd.h>   /* getpwuid (dynamic builds only; see username()) */
#  endif
#endif

/*************
 *
 *   username()
 *
 *************/

/* DOCUMENTATION
Return the name of the user who started the current job.
*/

/* PUBLIC */
char *username(void)
{
#ifdef PRIMITIVE_ENVIRONMENT
  return("an unknown user");
#elif defined(LADR_STATIC)
  /* Static builds only: avoid getpwuid(getuid()).  getpwuid pulls in glibc
     NSS (a runtime dlopen of libnss_*), which segfaults in a fully static
     binary when the target's glibc differs from the build host's.  The
     username is only used in the banner, so read it from the environment,
     which is static-safe.  Dynamic builds keep the original getpwuid path. */
  char *u = getenv("USER");
  if (u == NULL || u[0] == '\0')
    u = getenv("LOGNAME");
  return(u != NULL && u[0] != '\0' ? u : "an unknown user");
#else
  struct passwd *p;
  p = getpwuid(getuid());
  return(p ? p->pw_name : "???");
#endif
}  /* username */

/*************
 *
 *   hostname()
 *
 *************/

/* DOCUMENTATION
Return the hostname of the computer on which the current job is running.
*/

/* PUBLIC */
char *hostname(void)
{
#ifdef PRIMITIVE_ENVIRONMENT
  return("an unknown computer");
#else
  static char host[64];
  if (gethostname(host, 64) != 0)
    strcpy(host, "???");
  return(host);
#endif
}  /* hostname */

/*************
 *
 *   my_process_id()
 *
 *************/

/* DOCUMENTATION
Return the process ID of the current process.
*/

/* PUBLIC */
int my_process_id(void)
{
#ifdef PRIMITIVE_ENVIRONMENT
  return 0;
#else
  return getpid();
#endif
}  /* my_process_id */

/*************
 *
 *   get_bits()
 *
 *************/

/* DOCUMENTATION
If (64-bit long and pointer) return 64, else return 32.
*/

/* PUBLIC */
int get_bits(void)
{
  return sizeof(long) == 8 && sizeof(void *) == 8 ? 64 : 32;
}  /* get_bits */

/*************
 *
 *   raise_stack_limit()
 *
 *************/

/* DOCUMENTATION
Raise this process's stack size limit toward a generous target (1 GB),
capped by whatever the OS's hard limit allows. Several places in the
codebase (the TPTP recursive-descent parser in particular) recurse
once per syntactic nesting level with no iterative fallback -- a
legitimate, very deeply nested input (found live, 2026-08-07, an
auto-generated ~20,000-line software-verification problem with over
13,000 levels of parenthesization) can exhaust the OS default stack
(commonly 8 MB) and crash with SIGSEGV or a stack-smashing abort.
Raising the limit here, once, before any parsing happens, is a
standard, low-risk mitigation -- rlimits are inherited across fork(),
so -cores children get the raised limit too without needing their own
call. Silently accepts a partial increase (or no-op on a platform/
limit that refuses it) rather than treating this as fatal: the
original default already works for the overwhelming majority of
inputs, this only helps the rare very-deep outlier.
*/

/* PUBLIC */
void raise_stack_limit(void)
{
#ifndef PRIMITIVE_ENVIRONMENT
  const rlim_t target = (rlim_t) 1024 * 1024 * 1024;  /* 1 GB */
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) == 0) {
    rlim_t want = target;
    if (rl.rlim_max != RLIM_INFINITY && want > rl.rlim_max)
      want = rl.rlim_max;
    if (rl.rlim_cur == RLIM_INFINITY || want > rl.rlim_cur) {
      rl.rlim_cur = want;
      setrlimit(RLIMIT_STACK, &rl);  /* best-effort; ignore failure */
    }
  }
#endif
}  /* raise_stack_limit */
