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

#include "string.h"
#include "memory.h"

/* Private definitions and types */

static char *Float_format = "%.3f";

/*************
 *
 *     int str_ident(s, t) --  Identity of strings
 *
 *************/

/* DOCUMENTATION
This function routine checks identity of two strings.
*/

/* PUBLIC */
BOOL str_ident(char *s, char *t)
{
  return strcmp(s, t) == 0;
}  /* str_ident */

/*************
 *
 *   new_str_copy()
 *
 *************/

/* DOCUMENTATION
Return a malloced copy of the given string.  To avoid memory leaks,
call free() on the copy if you finish referring to it.
*/

/* PUBLIC */
char *new_str_copy(char *str)
{
  char *p = safe_malloc(strlen(str)+1);
  strcpy(p, str);
  return p;
}  /* new_str_copy */

/*************
 *
 *   string_member()
 *
 *************/

/* DOCUMENTATION
Is "string" a member of an array of "strings"?
*/

/* PUBLIC */
BOOL string_member(char *string, char **strings, int n)
{
  int i;
  for (i = 0; i < n; i++)
    if (string && strings[i] && str_ident(string, strings[i]))
      return TRUE;
  return FALSE;
}  /* string_member */

/*************
 *
 *   which_string_member()
 *
 *************/

/* DOCUMENTATION
If "string" is a member of an array of "strings", return the index;
else return -1.
*/

/* PUBLIC */
int which_string_member(char *string, char **strings, int n)
{
  int i;
  for (i = 1; i < n; i++)
    if (str_ident(strings[i], string))
      return i;
  return -1;
}  /* which_string_member */

/*************
 *
 *   initial_substring()
 *
 *************/

/* DOCUMENTATION
Is x an initial substring of y?
*/

/* PUBLIC */
BOOL initial_substring(char *x, char *y)
{
  while (*x && *y && *x == *y) {
    x++; y++;
  }
  return *x == '\0';
}  /* initial_substring */

/*************
 *
 *   substring()
 *
 *************/

/* DOCUMENTATION
Is x a substring of y?
*/

/* PUBLIC */
BOOL substring(char *x, char *y)
{
  BOOL found = initial_substring(x,y);
  while (*y && !found) {
    y++;
    found = initial_substring(x,y);
  }
  return found;
}  /* substring */

/*************
 *
 *   reverse_chars()
 *
 *************/

/* DOCUMENTATION
This routine reverses an array of characters.
You must give the starting and ending positions.
*/

/* PUBLIC */
void reverse_chars(char *s, int start, int end)
{
  if (start < end) {
    char c = s[start]; s[start] = s[end]; s[end] = c;
    reverse_chars(s, start+1, end-1);
  }
}  /* reverse_chars */

/*************
 *
 *   natural_string()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int natural_string(char *str)
{
  int i;
  if (!str_to_int(str, &i))
    return -1;
  else if (i < 0)
    return -1;
  else
    return i;
}  /* natural_string */

/*************
 *
 *   char_occurrences()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int char_occurrences(char *s, char c)
{
  int n = 0;
  int i;
  for (i = 0; i < strlen(s); i++) {
    if (s[i] == c)
      n++;
  }
  return n;
}  /* char_occurrences */

/*************
 *
 *   escape_char()
 *
 *************/

/* DOCUMENTATION
Retun a newly malloced string in which all occurrences of char c is
is escaped (preceded with a backslash).
*/

/* PUBLIC */
char *escape_char(char *s, char c)
{
  int n = char_occurrences(s, c);
  char *new = safe_malloc(strlen(s) + n + 1);
  int j = 0;
  int i;
  for (i = 0; i < strlen(s); i++) {
    if (s[i] == c)
      new[j++] = '\\';
    new[j++] = s[i];
  }
  new[j] = '\0';
  return new;
}  /* escape_char */

/*************
 *
 *   str_to_int()
 *
 *************/

/* DOCUMENTATION
This routine tries to convert a string into an integer (using strtol()).
If successful, TRUE is returned and *ip is set to the integer.
If failure, FALSE is returned.
*/

/* PUBLIC */
BOOL str_to_int(char *str, int *ip)
{
  char *end;
  *ip = strtol(str, &end, 10);
  if (*end != '\0')
    return FALSE;
  else
    return TRUE;
}  /* str_to_int */

/*************
 *
 *   int_to_str()
 *
 *************/

/* DOCUMENTATION
This routine converts an integer to a string (in decimal form).
The character array s must be large enough to hold the string.
The string is returned.
*/

/* PUBLIC */
char *int_to_str(int n, char *s, int size)
{
  int used = snprintf(s, size, "%d", n);
    
  if (used >= size)
    fatal_error("float_to_str, string too small");

  return s;
}  /* int_to_str */

/*************
 *
 *    str_to_double(string, double_ptr) -- convert a string to a double
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL str_to_double(char *s,
		   double *dp)
{
  char *end;
  double f;

  if (*s != '\"')
    return(FALSE);
  else if (*(s+1) == '\"')
    return(FALSE);
  else {
    f = strtod(s+1, &end);
    *dp = f;
    return (*end == '\"');
  }
}  /* str_to_double */

/*************
 *
 *    double_to_str(double, size, str, n) -- translate a double to a string
 *
 *    Like snprintf, except that format is built in and string is
 *    surrouded by double quotes.
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
char *double_to_str(double d,
		    char *s,
		    int size)
{

  int used = snprintf(s, size, Float_format, d);

  if (used >= size) {
    fatal_error("double_to_str, string too small");
    return NULL;
  }
  else {
    int i;
    int n = strlen(s);
    for (i=n; i>0; i--)
      s[i] = s[i-1];
    s[0] = '\"';
    s[n+1] = '\"';
    s[n+2] = '\0';
    return s;
  }
}  /* double_to_str */

/*************
 *
 *   string_of_repeated()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
BOOL string_of_repeated(char c, char *s)
{
  int i;
  for (i = 0; i < strlen(s); i++)
    if (s[i] != c)
      return FALSE;
  return TRUE;
}  /* string_of_repeated */

/*************
 *
 *   set_comma_formatting()
 *
 *************/

/* DOCUMENTATION
Enable or disable comma formatting in comma_num().
When disabled, numbers are formatted without commas.
*/

static BOOL Comma_formatting_enabled = FALSE;

/* PUBLIC */
void set_comma_formatting(BOOL enabled)
{
  Comma_formatting_enabled = enabled;
}  /* set_comma_formatting */

/*************
 *
 *   comma_num()
 *
 *************/

/* DOCUMENTATION
Format an unsigned long long with comma separators for readability.
Uses rotating static buffers so multiple calls can be used in one printf.
Example: 1234567890 becomes "1,234,567,890"
If comma formatting is disabled, returns plain number string.
*/

#define COMMA_NUM_BUFFERS 8
#define COMMA_NUM_SIZE 32  /* enough for 64-bit with commas */

/* PUBLIC */
char *comma_num(unsigned long long n)
{
  static char buffers[COMMA_NUM_BUFFERS][COMMA_NUM_SIZE];
  static int buf_index = 0;
  char *buf = buffers[buf_index];
  char temp[COMMA_NUM_SIZE];
  int i, j, len;

  buf_index = (buf_index + 1) % COMMA_NUM_BUFFERS;

  /* Convert number to string without commas */
  snprintf(temp, COMMA_NUM_SIZE, "%llu", n);

  if (!Comma_formatting_enabled) {
    strcpy(buf, temp);
    return buf;
  }

  len = strlen(temp);

  /* Copy with commas */
  j = 0;
  for (i = 0; i < len; i++) {
    if (i > 0 && (len - i) % 3 == 0)
      buf[j++] = ',';
    buf[j++] = temp[i];
  }
  buf[j] = '\0';

  return buf;
}  /* comma_num */

