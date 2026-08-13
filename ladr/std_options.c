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

#include "std_options.h"

/* Private definitions and types */

/* Flags */

static int Prolog_style_variables = -1;       /* delayed effect */
static int Ignore_option_dependencies = -1;   /* immediate effect */
static int Clocks = -1;                       /* delayed effect */
static int Otter_style_demod = -1;            /* delayed effect */
static int Ac_demod = -1;
static int Ac_kbo_tie;                     /* AC-oriented demodulators (experimental) */
static int Ac_demod_weight = -1;           /* parm: max weight of an adopted AC demodulator (-1 = unbounded) */

/*************
 *
 *   init_standard_options()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void init_standard_options(void)
{
  /* Flags */
  Prolog_style_variables     = init_flag("prolog_style_variables",     FALSE);
  Ignore_option_dependencies = init_flag("ignore_option_dependencies", FALSE);
  Clocks                     = init_flag("clocks",                     FALSE);
  Otter_style_demod          = init_flag("otter_style_demod",          FALSE);
  Ac_demod                   = init_flag("ac_demod",                   FALSE);
  Ac_kbo_tie                 = init_flag("ac_kbo_tie",                 FALSE);
  Ac_demod_weight            = init_parm("ac_demod_weight", -1, -1, INT_MAX);

}  /* init_standard_options */

/*************
 *
 *   process_standard_options()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
void process_standard_options(void)
{
  if (flag(Clocks))
    enable_clocks();
  else
    disable_clocks();

  if (flag(Prolog_style_variables))
    set_variable_style(PROLOG_STYLE);
  else
    set_variable_style(STANDARD_STYLE);

  /* Flag gnore_option_dependencies is handled internally by
     the options package.  It takes effect immediately.
   */

}  /* process_standard_options */

/*************
 *
 *   clocks_id()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int clocks_id(void)
{
  return Clocks;
}  /* clocks_id */

/*************
 *
 *   prolog_style_variables_id()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int prolog_style_variables_id(void)
{
  return Prolog_style_variables;
}  /* prolog_style_variables_id */

/*************
 *
 *   otter_style_demod_id()
 *
 *************/

/* PUBLIC */
int otter_style_demod_id(void)
{
  return Otter_style_demod;
}  /* otter_style_demod_id */

/*************
 *
 *   ac_demod_id()
 *
 *************/

/* PUBLIC */
int ac_demod_id(void)
{
  return Ac_demod;
}  /* ac_demod_id */

/*************
 *
 *   ac_demod_weight_id()
 *
 *************/

/* DOCUMENTATION
Parm id for ac_demod_weight: an AC equation is adopted as a demodulator
only if its atom weight is <= this value.  -1 (default) = unbounded
(every oriented AC equation is a demodulator).  Lower values make AC
demodulation less aggressive (fewer, smaller demodulators, less
back-demodulation churn).
*/

/* PUBLIC */
int ac_demod_weight_id(void)
{
  return Ac_demod_weight;
}  /* ac_demod_weight_id */

/*************
 *
 *   ac_kbo_tie_id()
 *
 *************/

/* DOCUMENTATION
*/

/* PUBLIC */
int ac_kbo_tie_id(void)
{
  return Ac_kbo_tie;
}  /* ac_kbo_tie_id */
