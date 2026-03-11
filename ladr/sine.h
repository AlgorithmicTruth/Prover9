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

#ifndef TP_SINE_H
#define TP_SINE_H

#include "formula.h"
#include "glist.h"

/* SInE (Sine Qua Non) premise selection.
   Reference: Hoder & Voronkov, "Sine Qua Non for Large Theory Reasoning",
   CADE-23, 2011.
*/

void sine_filter(Plist axioms, Plist goals,
                 int tolerance_pct, int tolerance2_pct,
                 int max_depth,
                 Plist *p_sos, Plist *p_usable, Plist *p_unselected);

int sine_depth_attr(void);

/* Scan-pass SInE: operates on raw scan_entry arrays instead of Formulas.
   sel_depth[i] and loose_depth[i] are caller-allocated (n_entries ints).
   max_axioms: cap on total selected axioms (0 = unlimited). */
struct scan_entry;  /* forward-declare */
void sine_filter_scan(struct scan_entry *entries, int n_entries,
                      int n_symbols,
                      int tolerance_pct, int tolerance2_pct,
                      int max_depth, int max_axioms,
                      int *sel_depth, int *loose_depth);

#endif  /* conditional compilation of whole file */
