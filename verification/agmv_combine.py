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
    print("  Set TPTP env var for include() resolution (or auto-detect).", file=sys.stderr)
    print("Output: problem.agmv", file=sys.stderr)
    sys.exit(1)

def find_tptp_root(problem_path):
    """Infer TPTP root from problem path (two levels up from Problems/DOM/)."""
    d = os.path.dirname(os.path.abspath(problem_path))
    # Walk up looking for a directory containing 'Axioms'
    for _ in range(5):
        if os.path.isdir(os.path.join(d, 'Axioms')):
            return d
        d = os.path.dirname(d)
    return None

def resolve_includes(lines, tptp_root, seen=None):
    """Recursively resolve include() directives, returning expanded lines."""
    if seen is None:
        seen = set()
    result = []
    for line in lines:
        m = re.match(r"^include\(\s*'([^']+)'\s*(?:,\s*\[([^\]]*)\])?\s*\)\.", line)
        if m:
            inc_path = m.group(1)
            selection = m.group(2)  # comma-separated names, or None
            names = None
            if selection:
                names = set(n.strip() for n in selection.split(','))

            if tptp_root:
                full_path = os.path.join(tptp_root, inc_path)
            else:
                full_path = inc_path

            if not os.path.exists(full_path):
                print("Warning: cannot resolve include '%s'" % inc_path,
                      file=sys.stderr)
                result.append(line)
                continue

            if full_path in seen:
                continue
            seen.add(full_path)

            with open(full_path) as f:
                inc_lines = [l.rstrip('\n') for l in f]

            # Recursively resolve nested includes
            inc_lines = resolve_includes(inc_lines, tptp_root, seen)

            if names:
                # Filter to selected formula names
                result.extend(select_formulas(inc_lines, names))
            else:
                # Include everything (skip comments/headers from axiom file)
                for il in inc_lines:
                    if re.match(r'^(cnf|fof|tff|tcf)\s*\(', il) or \
                       (result and not re.match(r'^(%|$)', result[-1])):
                        result.append(il)
                    elif not re.match(r'^(%|$)', il):
                        result.append(il)
                    else:
                        result.append(il)
        else:
            result.append(line)
    return result

def select_formulas(lines, names):
    """Select only formulas whose names are in the given set."""
    result = []
    in_formula = False
    current = []
    for line in lines:
        if not in_formula:
            m = re.match(r'^(cnf|fof|tff|tcf)\s*\(\s*([^,]+)', line)
            if m:
                fname = m.group(2).strip()
                in_formula = True
                current = [line]
                keep = fname in names
            # skip non-formula lines
        else:
            current.append(line)
            if re.search(r'\)\.\s*$', line):
                if keep:
                    result.extend(current)
                in_formula = False
                current = []
    return result

def read_problem(path, tptp_root):
    """Read TPTP problem file, resolve includes, split into header and clauses."""
    header = []
    clauses = []
    in_clauses = False

    with open(path) as f:
        raw_lines = [l.rstrip('\n') for l in f]

    # Resolve includes before splitting
    lines = resolve_includes(raw_lines, tptp_root)

    for line in lines:
        if not in_clauses:
            # Header is everything before the first cnf/fof/tff formula
            if re.match(r'^(cnf|fof|tff|tcf)\s*\(', line):
                in_clauses = True
                clauses.append(line)
            else:
                header.append(line)
        else:
            clauses.append(line)

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

    # Find TPTP root for include() resolution
    tptp_root = os.environ.get('TPTP') or find_tptp_root(problem_path)
    if tptp_root:
        print("TPTP root: %s" % tptp_root, file=sys.stderr)

    # Output file: same basename as problem, .agmv extension
    base = os.path.splitext(os.path.basename(problem_path))[0]
    out_path = base + '.agmv'

    header, clauses = read_problem(problem_path, tptp_root)
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
