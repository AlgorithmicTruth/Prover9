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
