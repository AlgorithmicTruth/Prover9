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

#include "banner.h"

#include <ctype.h>  /* for toupper, tolower */

/* Private definitions and types */

/*
 * memory management
 */

/*************
 *
 *   print_separator()
 *
 *************/

/* DOCUMENTATION
Print the standard separator line.
*/

/* PUBLIC */
void print_separator(FILE *fp, char *str, BOOL initial_newline)
{
  int len = 70;  /* total length of line */
  int n, i;
  char *first_half = "==============================";
  if (initial_newline)
    fprintf(fp, "\n");
  fprintf(fp, "%s %s ", first_half, str);
  n = len - (strlen(first_half) + strlen(str) + 2);
  for (i = 0; i < n; i++)
    fprintf(fp, "=");
  fprintf(fp, "\n");
  fflush(fp);
}  /* print_separator */

/*************
 *
 *    char *build_command_string(argc, argv)
 *
 *************/

/* DOCUMENTATION
Build a malloc'd string from argc/argv.  Call this before any code
that mutates argv so the original command line is preserved.
The caller may free the result, but typically it lives for the
entire process.
*/

/* PUBLIC */
char *build_command_string(int argc, char **argv)
{
  int i, len;
  char *s, *p;

  len = 0;
  for (i = 0; i < argc; i++)
    len += strlen(argv[i]) + 1;  /* +1 for space or NUL */

  s = safe_malloc(len);

  p = s;
  for (i = 0; i < argc; i++) {
    int n = strlen(argv[i]);
    memcpy(p, argv[i], n);
    p += n;
    if (i < argc - 1)
      *p++ = ' ';
  }
  *p = '\0';
  return s;
}  /* build_command_string */

/*************
 *
 *    void print_banner(command_line, name, version, date, as_comments)
 *
 *************/

/* DOCUMENTATION
Print the standard banner.  The command_line argument should be
a string built by build_command_string() before any argv mutation.
*/

/* PUBLIC */
void print_banner(const char *command_line,
		  char *name, char *version, char *date,
		  BOOL as_comments)
{
  char *com = (as_comments ? "% " : "");

  if (!as_comments)
    print_separator(stdout, name, FALSE);

  printf("%s%s (%d) version %s, %s.\n",
	 com, name, get_bits(), version, date);
  printf("%sProcess %d was started by %s on %s,\n%s%s",
	 com, my_process_id(), username(), hostname(), com, get_date());

  printf("%sThe command was \"%s\".\n", com, command_line);

  if (!as_comments)
    print_separator(stdout, "end of head", FALSE);
  fflush(stdout);
}  /* print_banner */

