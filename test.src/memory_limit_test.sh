#!/bin/sh
# Regression tests for max_megs.  Each case gives mace4 or prover9 a
# small max_megs and an input that needs far more memory, in a place
# the limit used to miss, and checks that the program stops with its
# max_megs exit status.  Run via 'make test13' from the repo root
# (needs bin/ already built -- run 'make all' first if it isn't).

BIN="${1:-bin}"
if [ ! -x "$BIN/mace4" ] || [ ! -x "$BIN/prover9" ]; then
  echo "No mace4/prover9 binaries in $BIN -- run 'make all' first, then 'make test13'." >&2
  exit 2
fi

# 'timeout' is not a stock macOS utility; it is only a safety net here
# (see distinctness_test.sh), so run without it if it is missing.
if command -v timeout >/dev/null 2>&1; then
  TIMEOUT_CMD="timeout 60"
else
  TIMEOUT_CMD=""
fi

# A build without these fixes can try to take many gigabytes, so cap
# the address space of every run at 1 GB where the system allows it.
# Each input also sets max_seconds or max_given, which bound a run
# where the cap is not available.
VMEM=1000000
if ! (ulimit -v $VMEM) 2>/dev/null; then
  echo "Note: 'ulimit -v' is not available here -- running without the" >&2
  echo "address-space cap (relying on each input's own limits instead)." >&2
  VMEM=""
fi

ulimit -c 0 2>/dev/null

TMP="${TMPDIR:-/tmp}/memory_limit_test.$$"
mkdir "$TMP" || exit 2
trap 'rm -rf "$TMP"' 0
trap 'exit 2' 1 2 15
OUT="$TMP/out"

pass=0
fail=0

# check DESC RC TEXT CMD...: pass if CMD exits with RC and its output
# (stdout and stderr) contains TEXT.
check() {
  desc="$1"; want_rc="$2"; want="$3"; shift 3
  ( if [ -n "$VMEM" ]; then ulimit -v $VMEM; fi
    exec $TIMEOUT_CMD "$@" ) < /dev/null > "$OUT" 2>&1
  rc=$?
  if [ "$rc" -eq "$want_rc" ] && grep -F -- "$want" "$OUT" >/dev/null; then
    printf "  PASS  %s\n" "$desc"
    pass=$((pass+1))
  else
    printf "  FAIL  %s (exit %s, expected %s)\n" "$desc" "$rc" "$want_rc"
    tail -n 3 "$OUT" | cut -c1-100 | sed 's/^/        | /'
    fail=$((fail+1))
  fi
}

# vars N: x1,x2,...,xN
vars() {
  awk -v n="$1" 'BEGIN { for (i = 1; i <= n; i++) printf "%sx%d", (i > 1 ? "," : ""), i }'
}

echo "max_megs regression cases:"

# Mace4 allocates the cell table, Domain_size^arity cells per symbol,
# with safe_malloc(), so it must be checked against max_megs before it
# is allocated.  q/22 at domain size 2 is about 330 MB.
cat > "$TMP/cells.in" <<END
assign(max_megs, 100).
assign(max_seconds, 5).
clear(negprop).
formulas(sos).
q($(vars 22)).
end_of_list.
END
check "mace4: cell table larger than max_megs" 7 "over max_megs" \
  "$BIN/mace4" -f "$TMP/cells.in"

# The negprop index is a tree of (Domain_size+1)^arity pointers per
# value of each symbol, also from safe_calloc().  For r/15 at domain
# size 2 it is about 330 MB, against a cell table of under 3 MB.
cat > "$TMP/negprop.in" <<END
assign(max_megs, 50).
assign(max_seconds, 5).
formulas(sos).
r($(vars 15)).
end_of_list.
END
check "mace4: negprop index larger than max_megs" 7 "negprop index" \
  "$BIN/mace4" -f "$TMP/negprop.in"

# Control: without the index the same problem fits, and has a model.
(echo "clear(negprop)."; cat "$TMP/negprop.in") > "$TMP/no_negprop.in"
check "mace4: same input, clear(negprop) (control)" 0 "Exiting with 1 model" \
  "$BIN/mace4" -f "$TMP/no_negprop.in"

# Mace4's own max_megs check runs only during the search, so LADR's
# must stay on to bound the ground clauses built before it.  At domain
# size 10 the first clause alone has 10^8 instances.
cat > "$TMP/ground.in" <<'END'
assign(max_megs, 20).
assign(max_seconds, 5).
formulas(sos).
p(x1,x2) | p(x3,x4) | p(x5,x6) | p(x7,x8) | q(x1,x3,x5,x7).
-p(x1,x2) | -q(x1,x2,x3,x4) | r(x3,x4).
end_of_list.
END
check "mace4: ground clauses larger than max_megs" 7 "exit (max_megs_no)" \
  "$BIN/mace4" -n 10 -N 10 -f "$TMP/ground.in"

# The same with -cores: each child must stop at max_megs, and the
# parent must report max_megs, not that the sizes were exhausted.
check "mace4 -cores 4: ground clauses larger than max_megs" 7 "exit (max_megs_no)" \
  "$BIN/mace4" -cores 4 -n 8 -N 11 -f "$TMP/ground.in"

# get_mem() takes chunks of 500 pointers or more from safe_malloc(),
# not palloc(), so they must be counted too.  Each clause kept here
# holds f(x,x,...,x) with 900 arguments, a 7 KB argument array (the
# variable itself is shared).  By max_given 6000 that is about 85 MB
# of such chunks on top of about 180 MB from palloc().
cat > "$TMP/wide.in" <<END
assign(max_megs, 220).
assign(max_given, 6000).
assign(max_weight, 1000000).
assign(fpa_depth, 1).
formulas(sos).
p(f(x$(awk 'BEGIN { for (i = 1; i < 900; i++) printf ",x" }')), a).
-p(x, y) | p(x, s0(y)).
-p(x, y) | p(x, s1(y)).
end_of_list.
END
check "prover9: large get_mem() chunks count toward max_megs" 3 "exit (max_megs)" \
  "$BIN/prover9" -f "$TMP/wide.in"

echo
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
