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

#ifndef LADR_FEATURES_H
#define LADR_FEATURES_H

#include "../ladr/tptp_parse.h"

/*
 * 32-integer feature vector extracted from LADR scan data.
 * All values are integers; averages are scaled x100.
 * Adapted from LADR-selector features.h.
 */

#define NUM_FEATURES 32

/* Feature indices */
#define F_N_FORMULAS         0
#define F_N_AXIOMS           1
#define F_N_GOALS            2
#define F_N_SYMBOLS          3
#define F_HAS_GOAL           4
#define F_HAS_NEG_CONJ       5
#define F_IS_CNF_ONLY        6
#define F_IS_FOF_ONLY        7
#define F_HAS_HYPOTHESIS     8
#define F_MAX_SYMS_PER_FORM  9
#define F_AVG_SYMS_PER_FORM 10
#define F_MAX_BODY_LEN      11
#define F_AVG_BODY_LEN      12
#define F_DOMAIN_HASH       13
#define F_HAS_EQUALITY      14
#define F_MAX_DEPTH_EST     15
#define F_AVG_DEPTH_EST     16
#define F_MAX_LITERALS_EST  17
#define F_AVG_LITERALS_EST  18
#define F_ALL_UNIT_EST      19
#define F_ALL_HORN_EST      20
#define F_NEG_NONUNIT_COUNT 21
#define F_AXIOM_SYM_RATIO   22
#define F_GOAL_SYM_COUNT    23
#define F_SINGLETON_SYMS    24
#define F_MULTI_FORM_SYMS   25
#define F_LOG2_N_AXIOMS     26
#define F_LOG2_N_SYMBOLS    27
#define F_LOG2_MAX_BODY     28
/* 29-31 reserved */

/* Feature names for printing */
extern const char *feature_names[NUM_FEATURES];

/* Extract features from LADR scan result into fv[NUM_FEATURES] */
void extract_features(Scan_result sd, int *fv);

/* Set F_DOMAIN_HASH from TPTP filename (first 3 alpha chars hashed) */
void set_domain_hash(int *fv, const char *filename);

#endif /* LADR_FEATURES_H */
