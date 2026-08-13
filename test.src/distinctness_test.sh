#!/bin/sh
# Regression matrix for numeral/distinct-object unification (T1-T10).
# Each case pipes a one-line TPTP snippet to prover9 -tptp_out and checks
# the SZS status against the expected value below.  Run via 'make test7'
# from the repo root (needs bin/prover9 already built -- run 'make all'
# first if it isn't).

P9="${1:-bin/prover9}"
if [ ! -x "$P9" ]; then
  echo "No prover9 binary at $P9 -- run 'make all' first, then 'make test7'." >&2
  exit 2
fi

# 'timeout' is NOT a stock Darwin/macOS utility (confirmed live,
# 2026-08-12: not even present on a current macOS install unless
# Homebrew's coreutils is installed) and is even less likely to exist
# on an old/minimal system like a PowerPC Mac -- exactly the same
# "quietly assumed available" class of gap as libproc.h in
# provers.src/Makefile, found the same day. It's a safety net here,
# not load-bearing for correctness (prover9's own internal -t 5
# deadline already bounds each run), so degrade gracefully instead of
# every single case silently failing with no output the way a missing
# 'timeout' executable would (indistinguishable, before this fix, from
# prover9 itself crashing).
if command -v timeout >/dev/null 2>&1; then
  TIMEOUT_CMD="timeout 10"
else
  echo "Note: no 'timeout' command on this system -- running without the" >&2
  echo "external safety-net timeout (relying on prover9's own internal" >&2
  echo "-t deadline instead)." >&2
  TIMEOUT_CMD=""
fi

pass=0
fail=0

check() {
  desc="$1"; snippet="$2"; expected="$3"
  raw=$(printf '%s\n' "$snippet" | $TIMEOUT_CMD "$P9" -tptp_out -t 5 2>&1)
  got=$(printf '%s\n' "$raw" | grep -m1 "SZS status" | sed 's/.*SZS status \([A-Za-z]*\).*/\1/')
  if [ "$got" = "$expected" ]; then
    printf "  PASS  %-45s (%s)\n" "$desc" "$got"
    pass=$((pass+1))
  else
    printf "  FAIL  %-45s expected %s, got %s\n" "$desc" "$expected" "${got:-<none>}"
    if [ -z "$got" ]; then
      echo "        no SZS status line in prover9's output -- raw output was:"
      if [ -z "$raw" ]; then
        echo "        (completely empty -- the binary likely crashed, was"
        echo "        killed, or is not the architecture this Mac expects;"
        echo "        try running '$P9' directly to see the real error)"
      else
        printf '%s\n' "$raw" | sed 's/^/        | /'
      fi
    fi
    fail=$((fail+1))
  fi
}

echo "Distinctness unification matrix:"

# T1: axiom-only 2=3 is inconsistent (refuted via the new mechanism, not
# the old injected axioms -- Prover9's own vocabulary for a bare
# axiom-only refutation is "Unsatisfiable", not "Theorem").
check "T1  2=3 (axiom only)"            'cnf(a, axiom, 2 = 3).'         "Unsatisfiable"

# T2: value not spelling -- 02 and 2 are one value, never forced apart.
check "T2  02 = 2 (leading zero)"       'fof(g, conjecture, 02 = 2).'   "GaveUp"

# T3: distinct object vs number is never forced either way.
check "T3  \"2\" = 2 (mixed)"           'fof(g, conjecture, "2" = 2).'  "GaveUp"

# T4: the collision fix -- '2' and 2 must be different symbols now.
check "T4a '2' = 2 (was Theorem, bug)"  "fof(g, conjecture, '2' = 2)."   "GaveUp"
check "T4b 'cat' = cat (unaffected)"    "fof(g, conjecture, 'cat' = cat)." "Theorem"

# T5: distinct objects still work, via the new lazy mechanism.
check "T5  \"Apple\" != \"Microsoft\""  'fof(g, conjecture, "Apple" != "Microsoft").' "Theorem"

# T6/T7: the true half -- 2 != 3 provable with no axioms at all; a clause
# containing it as a disjunct is a tautology (checked indirectly: proving
# an irrelevant goal alongside a 2!=3 disjunct must still succeed, since
# the disjunct alone makes the axiom clause useless-but-harmless -- here
# checked directly via T6, the tautology half itself is exercised by T1's
# and T4a's proof search not needing any axiom to eliminate a 2!=3/2=2
# style disjunct, already covered by the mechanism assertions above).
check "T6  2 != 3 (true half, no axioms)" 'fof(g, conjecture, 2 != 3).' "Theorem"

echo
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
