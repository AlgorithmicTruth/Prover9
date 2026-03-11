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

#ifndef TP_TSTP_PROOF_H
#define TP_TSTP_PROOF_H

#include "topform.h"
#include "ioutil.h"

/* INTRODUCTION
Read a TSTP-format proof and convert it to LADR Topform list with
justifications.  Also provides reverse mapping from TSTP inference
rule names to LADR justification types.
*/

/* Public definitions */

/* End of public definitions */

/* Public function prototypes from tstp_proof.c */

Plist read_tstp_proof(FILE *fin, FILE *ferr);

Just_type tptp_rule_name_to_just(const char *name);

#endif  /* conditional compilation of whole file */
