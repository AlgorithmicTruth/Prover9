#!/bin/sh
# Regression checks for the helper scripts in utilities/, which 'make all'
# copies into bin/.  Each case runs one installed script end to end on a
# tiny problem, with bin/ first on PATH (the scripts find prover9, mace4
# and the other programs there).  Run via 'make test14' from the repo
# root (needs bin/ already built -- run 'make all' first if it isn't).

B="${1:-bin}"
if [ ! -x "$B/prover9" ]; then
  echo "No prover9 binary in $B -- run 'make all' first, then 'make test14'." >&2
  exit 2
fi
B=$(cd "$B" && pwd)

echo "Helper scripts:"

if ! command -v python3 >/dev/null 2>&1; then
  echo "  SKIP  all cases: no python3 on PATH (the helper scripts need it)"
  echo
  echo "0 passed, 0 failed (skipped: no python3)"
  exit 0
fi

# 'timeout' is not on stock macOS (see distinctness_test.sh); it is only
# a safety net here, since every input below sets max_seconds.
if command -v timeout >/dev/null 2>&1; then
  TIMEOUT_CMD="timeout 60"
else
  echo "Note: no 'timeout' command on this system -- running without the" >&2
  echo "external safety-net timeout (relying on max_seconds instead)." >&2
  TIMEOUT_CMD=""
fi

PATH="$B:$PATH"
export PATH

# The scripts write temporary files into the current directory.
T="${TMPDIR:-/tmp}/helper_scripts_test.$$"
mkdir "$T" || exit 2
trap 'rm -rf "$T"' 0
trap 'exit 1' 1 2 15

pass=0
fail=0

# run CMD ARGS... -- run CMD in $T; output to $T/out and $T/err, status to rc
run() {
  ( cd "$T" && $TIMEOUT_CMD "$@" ) > "$T/out" 2> "$T/err"
  rc=$?
}

# check DESC FILE PATTERN -- PASS if the last run exited 0 and FILE
# contains PATTERN (an empty PATTERN checks the exit status only)
check() {
  desc="$1"; file="$2"; pattern="$3"
  if [ "$rc" -eq 0 ] &&
     { [ -z "$pattern" ] || grep -e "$pattern" "$file" >/dev/null 2>&1; }; then
    printf "  PASS  %s\n" "$desc"
    pass=$((pass+1))
  else
    printf "  FAIL  %s (exit status %s)\n" "$desc" "$rc"
    cat "$T/out" "$T/err" | tail -n 5 | sed 's/^/        | /'
    fail=$((fail+1))
  fi
}

# A theorem Prover9 proves at once (prover9.examples/x2.in).
cat > "$T/x2.in" <<'EOF'
assign(max_seconds, 10).
formulas(assumptions).
e * x = x.
x' * x = e.
(x * y) * z = x * (y * z).
x * x = e.
end_of_list.
formulas(goals).
x * y = y * x.
end_of_list.
EOF

# prover9-mace4: races Prover9 against Mace4 and prints the winner's output.
run "$B/prover9-mace4" -f x2.in < /dev/null
check "prover9-mace4 -f x2.in (Prover9 wins)" "$T/out" "THEOREM PROVED"

# looper: appends each candidate line to a head file and runs Prover9
# (as a goal) or Mace4 (as an assumption) on it.
sed '/formulas(goals)/,$d' "$T/x2.in" > "$T/head.in"
echo 'x * y = y * x.' > "$T/cands.txt"
run "$B/looper" prover9 goals head.in < "$T/cands.txt"
check "looper prover9 goals (proves the candidate)" "$T/out" \
      "processed 1, successes 1, failures 0"
run "$B/looper" mace4 assumptions head.in < "$T/cands.txt"
check "looper mace4 assumptions (finds a model)" "$T/out" \
      "processed 1, successes 1, failures 0"

# attack: keeps the models Mace4 finds and drops each candidate that one
# of them satisfies.  The first candidate needs Mace4; the model found
# for it (x * y = 0) also satisfies the second.  Comments pass through.
cat > "$T/semigroup.in" <<'EOF'
assign(max_seconds, 10).
formulas(assumptions).
(x * y) * z = x * (y * z).
end_of_list.
EOF
printf 'x * y = y * x.\n%% comment\nx * x = y * y.\n' > "$T/cands.txt"
run "$B/attack" semigroup.in interps < "$T/cands.txt"
check "attack semigroup.in interps (both candidates killed)" "$T/out" \
      "checked 2, passed 0, num_interps 1"
check "attack wrote the model to its interps file" "$T/interps" \
      "interpretation("
# Invalid escapes such as '\s' in a non-raw string are a SyntaxWarning
# today and slated to become errors.
run python3 -W error -c 'import sys
with open(sys.argv[1]) as f: compile(f.read(), sys.argv[1], "exec")' \
    "$B/attack"
check "attack compiles with warnings as errors" "$T/out" ""

# gvizify: turns 'prooftrans xml' output into a graphviz digraph.
$TIMEOUT_CMD "$B/prover9" -f "$T/x2.in" < /dev/null 2> /dev/null |
  "$B/prooftrans" xml > "$T/proof.xml"
run "$B/gvizify" proof.xml
check "gvizify proof.xml (header)" "$T/out" '^strict digraph "proof"'
check "gvizify proof.xml (whole graph)" "$T/out" "last step is plausible root"

echo
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
