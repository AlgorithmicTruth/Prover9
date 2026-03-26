#!/usr/bin/env python3
# agmv_combine.py -- Combine a TPTP problem file with Mace4 model output
# into a single file suitable for AGMV verification via SystemOnTSTP.
#
# Usage: agmv_combine.py problem.p mace4_output
# Output: problem.agmv
#
# Copyright (C) 2026 Jeffrey P. Machado, Larry Lesyna

import sys
import os
import re

def usage():
    print("Usage: agmv_combine.py problem.p mace4_output", file=sys.stderr)
    print("Output: problem.agmv", file=sys.stderr)
    sys.exit(1)

def read_problem(path):
    """Read TPTP problem file, split into header comments and clauses."""
    header = []
    clauses = []
    in_clauses = False

    with open(path) as f:
        for line in f:
            stripped = line.rstrip('\n')
            if not in_clauses:
                # Header is everything before the first cnf/fof/tff formula
                if re.match(r'^(cnf|fof|tff|tcf)\s*\(', stripped):
                    in_clauses = True
                    clauses.append(stripped)
                else:
                    header.append(stripped)
            else:
                clauses.append(stripped)

    return header, clauses

def extract_model(path):
    """Extract model from Mace4 TPTP output (between SZS FiniteModel tags)."""
    model = []
    in_model = False

    with open(path) as f:
        for line in f:
            stripped = line.rstrip('\n')
            if re.match(r'^% SZS output start FiniteModel', stripped):
                in_model = True
                continue
            if re.match(r'^% SZS output end FiniteModel', stripped):
                break
            if in_model:
                model.append(stripped)

    if not model:
        print("Error: no FiniteModel found in " + path, file=sys.stderr)
        sys.exit(1)

    # Strip trailing blank lines
    while model and model[-1] == '':
        model.pop()

    return model

def main():
    if len(sys.argv) != 3:
        usage()

    problem_path = sys.argv[1]
    mace4_path = sys.argv[2]

    # Output file: same basename as problem, .agmv extension
    base = os.path.splitext(os.path.basename(problem_path))[0]
    out_path = base + '.agmv'

    header, clauses = read_problem(problem_path)
    model = extract_model(mace4_path)

    with open(out_path, 'w') as f:
        # Header (outside SZS tags)
        for line in header:
            f.write(line + '\n')

        # Problem clauses
        f.write('% SZS output start ListOfFormulae\n')
        for line in clauses:
            f.write(line + '\n')
        f.write('% SZS output end ListOfFormulae\n')

        # Model
        f.write('% SZS output start Interpretation\n')
        for line in model:
            f.write(line + '\n')
        f.write('\n% SZS output end Interpretation\n')

    print(out_path)

if __name__ == '__main__':
    main()
