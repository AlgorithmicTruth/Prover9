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

#include "fatal.h"

/* Private definitions and types */

static int Fatal_exit_code = 1;
static BOOL Fatal_tptp_mode = FALSE;
static char *Fatal_problem_name = NULL;
static char *Fatal_szs_status = NULL;  /* NULL = default "Error" */
static char *Fatal_message = NULL;     /* see fatal_file_not_found() */

/*************
 *
 *   bell()
 *
 *************/

/* DOCUMENTATION
Send the bell character '\007' to a file.
*/

/* PUBLIC */
void bell(FILE *fp)
{
#ifndef __EMSCRIPTEN__
  fprintf(fp, "%c", '\007');
#endif
}  /* bell */

/*************
 *
 *   get_fatal_exit_code()
 *
 *************/

/* DOCUMENTATION
This function returns the exit code that will be used in
case fatal_error() is called.
*/

/* PUBLIC */
int get_fatal_exit_code()
{
  return Fatal_exit_code;
}  /* get_fatal_exit_code */

/*************
 *
 *   set_fatal_exit_code()
 *
 *************/

/* DOCUMENTATION
This routine changes the exit code that will be used in case
fatal_error() is called.  The default value is 1.
*/

/* PUBLIC */
void set_fatal_exit_code(int exit_code)
{
  Fatal_exit_code = exit_code;
}  /* set_fatal_exit_code */

/*************
 *
 *   set_fatal_tptp_mode()
 *
 *************/

/* DOCUMENTATION
Enable TPTP/SZS output in fatal_error().  When enabled, fatal_error()
prints "% SZS status Error [for <name>]" to stdout before the error
message.  The problem_name may be NULL.
*/

/* PUBLIC */
void set_fatal_tptp_mode(BOOL mode, char *problem_name)
{
  Fatal_tptp_mode = mode;
  Fatal_problem_name = problem_name;
}  /* set_fatal_tptp_mode */

/*************
 *
 *   set_fatal_szs_status()
 *
 *************/

/* DOCUMENTATION
Override the SZS status string used by fatal_error() in TPTP mode.
Default is "Error".  Set to "Timeout" for CNF preprocessing timeouts.
*/

/* PUBLIC */
void set_fatal_szs_status(const char *status)
{
  Fatal_szs_status = (char *)status;
}  /* set_fatal_szs_status */

/*************
 *
 *   fatal_error()
 *
 *************/

/* DOCUMENTATION
This routine should be called if something terrible happens.
The message is printed to stdout and to stderr, and the
process exits with the fatal_exit_code (default 1).
*/

/* PUBLIC */
void fatal_error(char *message)
{
  if (Fatal_tptp_mode) {
    const char *status = Fatal_szs_status ? Fatal_szs_status : "Error";
    if (Fatal_problem_name)
      fprintf(stdout, "\n%% SZS status %s for %s\n", status, Fatal_problem_name);
    else
      fprintf(stdout, "\n%% SZS status %s\n", status);
  }
  fprintf(stdout, "\nFatal error:  %s\n\n", message);
  fprintf(stderr, "\nFatal error:  %s\n\n", message);
  exit(Fatal_exit_code);
}  /* fatal_error */

/*************
 *
 *   fatal_file_not_found()
 *
 *************/

/* DOCUMENTATION
Report that a file could not be opened, and exit as fatal_error() does.
If <context> is not NULL, it names the routine that was trying to open
the file.

The filename comes from the command line or from the input, so its
length is not bounded.  The message is measured with snprintf() and
allocated to fit, so the whole name is reported however long it is.
The allocation is plain malloc(), not the LADR allocator, which can call
fatal_error() itself.  The message is held in a file-scope pointer,
because fatal_error() does not return and the message cannot be freed.
*/

/* PUBLIC */
void fatal_file_not_found(char *context, char *filename)
{
  char *ctx = (context == NULL ? "" : context);
  char *sep = (context == NULL ? "" : ", ");
  int n = snprintf(NULL, 0, "%s%sfile %s not found", ctx, sep, filename);

  if (n >= 0) {
    Fatal_message = malloc((size_t) n + 1);
    if (Fatal_message != NULL) {
      snprintf(Fatal_message, (size_t) n + 1,
	       "%s%sfile %s not found", ctx, sep, filename);
      fatal_error(Fatal_message);
    }
  }

  {
    /* Out of memory: report as much of the name as fits. */
    char s[1000];
    snprintf(s, sizeof(s), "%s%sfile %s not found", ctx, sep, filename);
    fatal_error(s);
  }
}  /* fatal_file_not_found */
