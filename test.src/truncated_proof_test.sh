#!/bin/sh
# Regression tests for prooftrans and directproof on truncated proofs.
# Each case feeds a proof cut short (or with one comment line) and
# checks for a clean exit; the unfixed programs loop forever, growing
# memory, or crash.  Run via 'make test10' from the repo root (needs
# bin/ already built -- run 'make all' first if it isn't).

BIN="${1:-bin}"
if [ ! -x "$BIN/prover9" ]; then
  echo "No prover9 binary in $BIN -- run 'make all' first, then 'make test10'." >&2
  exit 2
fi

LIMIT=10                # seconds per run; a fixed build needs well under 1
VMEM=${VMEM:-1000000}   # KB; the unfixed loop grows by about 100 MB a second
                        # (run with VMEM=unlimited on an ASan build)

ulimit -c 0 2>/dev/null   # the unfixed programs crash; no core files

TMP="${TMPDIR:-/tmp}/truncated_proof_test.$$"
mkdir "$TMP" || exit 2
trap 'rm -rf "$TMP"' 0
trap 'exit 2' 1 2 15
OUT="$TMP/out"

# run INPUT CMD...: run CMD reading INPUT, output to $OUT, exit code to
# $rc.  A hang is the failure being tested for, so the time limit is
# enforced here rather than left to 'timeout', which macOS does not
# ship, and memory is capped where the shell allows it.
run() {
  in="$1"; shift
  ( ulimit -v $VMEM 2>/dev/null; exec "$@" ) < "$in" > "$OUT" 2>&1 &
  pid=$!
  ( n=0
    while [ $n -lt $LIMIT ]; do sleep 1; n=$((n+1)); done
    kill -9 $pid ) > /dev/null 2>&1 &
  watcher=$!
  wait $pid
  rc=$?
  kill $watcher 2>/dev/null
  wait $watcher 2>/dev/null
}

pass=0
fail=0

ok() {
  printf "  PASS  %s\n" "$1"
  pass=$((pass+1))
}

bad() {
  printf "  FAIL  %s (%s)\n" "$1" "$2"
  tail -n 3 "$OUT" | cut -c1-100 | sed 's/^/        | /'
  fail=$((fail+1))
}

# check_fatal DESC INPUT CMD...: pass if CMD exits 1 and reports the
# truncated proof.
check_fatal() {
  desc="$1"; in="$2"; shift 2
  run "$in" "$@"
  if [ "$rc" -eq 1 ] && grep "proof ends prematurely" "$OUT" >/dev/null; then
    ok "$desc"
  elif [ "$rc" -eq 137 ]; then
    bad "$desc" "killed after ${LIMIT}s"
  else
    bad "$desc" "exit $rc, expected 1"
  fi
}

# check_blank DESC INPUT CMD...: pass if CMD exits 0 and prints exactly
# one blank line between the proof's comments and its first clause.
check_blank() {
  desc="$1"; in="$2"; shift 2
  run "$in" "$@"
  n=$(awk '/Comments from original proof/ { c = 1; next }
           c && /^%/ && n == 0 { next }
           c && /^$/ { n++; next }
           c { exit }
           END { print n + 0 }' "$OUT")
  if [ "$rc" -eq 0 ] && [ "$n" -eq 1 ]; then
    ok "$desc"
  else
    bad "$desc" "exit $rc, $n blank lines after the comments"
  fi
}

# A small proof to cut up.
cat > "$TMP/x2.in" <<'END'
formulas(sos).
  e * x = x.
  x' * x = e.
  (x * y) * z = x * (y * z).
  x * x = e.
end_of_list.

formulas(goals).
  x * y = y * x.
end_of_list.
END
run "$TMP/x2.in" "$BIN/prover9"
cp "$OUT" "$TMP/proof"

# cut right after the "% Proof" comment line, and after the first clause
awk '{ print } /= PROOF =/ { p = 1 } p && /^% Proof/ { exit }' \
  "$TMP/proof" > "$TMP/trunc_comment"
awk '{ print } /= PROOF =/ { p = 1 } p && /^[0-9]+ / { exit }' \
  "$TMP/proof" > "$TMP/trunc_clause"

# keep only the first comment line: the unfixed programs swallowed every
# other line after a comment, so with an odd number of them the blank
# line after the comments was swallowed and printed back twice
awk '/= PROOF =/ { p = 1 } p && /^%/ && !/^% Proof/ { next }
     p && /^[0-9]+ / { p = 0 } { print }' "$TMP/proof" > "$TMP/one_comment"

echo "Truncated-proof tests:"

for prog in prooftrans directproof; do
  check_fatal "$prog < proof cut after its first comment line" \
    "$TMP/trunc_comment" "$BIN/$prog"
  check_fatal "$prog < proof cut after its first clause" \
    "$TMP/trunc_clause" "$BIN/$prog"
  check_blank "$prog < complete proof: one blank line after the comments" \
    "$TMP/one_comment" "$BIN/$prog"
done

echo
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
