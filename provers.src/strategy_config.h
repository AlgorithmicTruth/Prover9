/*  Copyright (C) 2026 Jeffrey Machado, Larry Lesyna

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

#ifndef LADR_STRATEGY_CONFIG_H
#define LADR_STRATEGY_CONFIG_H

/*
 * Strategy configurations for Prover9.
 * Each strategy is a set of Prover9 option overrides.
 * -1 means "use default" for that parameter.
 *
 * Adapted from LADR-selector strategy.h.
 */

struct strategy_config {
  int   id;
  char  name[32];
  int   order;              /* 0=LPO, 1=RPO, 2=KBO, -1=default */
  int   age_part;           /* 0-3, -1=default */
  int   weight_part;        /* 0-3, -1=default */
  int   max_weight;         /* 10-200, -1=default */
  int   sine_tolerance;     /* 100-500, -1=adaptive */
  int   sine_depth;         /* 1-10/0=fixpoint, -1=adaptive */
  int   sine_max_axioms;    /* 100-10000/0=unlimited, -1=adaptive */
  int   sine_weight;        /* 0-500, -1=default */
  int   binary_resolution;  /* 0/1/-1 */
  int   hyper_resolution;   /* 0/1/-1 */
  int   ur_resolution;      /* 0/1/-1 */
  int   paramodulation;     /* 0/1/-1 */
  int   multi_order_trial;  /* 0/1/-1 */
  int   process_initial_sos;/* 0/1/-1 */
  int   back_subsume;       /* 0/1/-1 */
  int   lightest_first;     /* 0/1/-1 */
  int   breadth_first;      /* 0/1/-1 */
  int   safe_unit_conflict; /* 0/1/-1 */
  int   factor;             /* 0/1/-1 */
  int   unit_deletion;      /* 0/1/-1 */
  int   para_units_only;    /* 0/1/-1 */
  int   back_demod;         /* 0/1/-1 */
  int   ordered_res;        /* 0/1/-1 */
  int   ordered_para;       /* 0/1/-1 */
  int   literal_selection;  /* 0=max_negative, 1=all_negative, -1=default */
  int   nest_penalty;       /* floatparm value, -1=default */
  int   depth_penalty;      /* floatparm value, -1=default */
};

/* Portfolio data is in strategy_data.h (generated) */
#include "strategy_data.h"

#endif /* LADR_STRATEGY_CONFIG_H */
