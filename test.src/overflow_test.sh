#!/bin/sh
# Regression tests for fixed-size buffers that overflowed on a long
# command-line argument or input token.  Each case runs a program with
# an over-long argument and checks that it exits normally with its
# full message; the unfixed programs abort or crash instead.  Run via
# 'make test9' from the repo root (needs bin/ already built -- run
# 'make all' first if it isn't).

BIN="${1:-bin}"
if [ ! -x "$BIN/prover9" ]; then
  echo "No prover9 binary in $BIN -- run 'make all' first, then 'make test9'." >&2
  exit 2
fi

# 'timeout' is not a stock macOS utility; it is only a safety net here
# (see distinctness_test.sh), so run without it if it is missing.
if command -v timeout >/dev/null 2>&1; then
  TIMEOUT_CMD="timeout 30"
else
  TIMEOUT_CMD=""
fi

ulimit -c 0 2>/dev/null   # the unfixed programs abort; no core files

TMP="${TMPDIR:-/tmp}/overflow_test.$$"
mkdir "$TMP" || exit 2
trap 'rm -rf "$TMP"' 0
trap 'exit 2' 1 2 15
OUT="$TMP/out"

# repeat N: a string of N 'z's (N a multiple of 10)
repeat() {
  awk -v n="$1" 'BEGIN { for (i = 0; i < n; i += 10) printf "zzzzzzzzzz" }'
}

LONG=$(repeat 300)
LONG600=$(repeat 600)
LONG4000=$(repeat 4000)

# A small proof for the prooftrans cases.
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
$TIMEOUT_CMD "$BIN/prover9" -f "$TMP/x2.in" > "$TMP/proof" 2>/dev/null

# The same proof with its first clause id replaced by a 200,000-char token.
awk '/= PROOF =/ { p = 1 }
     p && /^[0-9]+ / {
       t = "x"; while (length(t) < 200000) t = t t
       sub(/^[0-9]+/, substr(t, 1, 200000)); p = 0
     }
     { print }' "$TMP/proof" > "$TMP/longtok"

pass=0
fail=0

# check DESC RC TEXT INPUT CMD...: pass if CMD, reading INPUT, exits
# with RC and its output contains TEXT.
check() {
  desc="$1"; want_rc="$2"; want="$3"; in="$4"; shift 4
  $TIMEOUT_CMD "$@" < "$in" > "$OUT" 2>&1
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

echo "Long-argument and long-token overflow tests:"

# M2: the missing-file message was formatted into char[100].
check "prover9 -f <300-char missing file>" 1 \
  "read_all_input, file $LONG not found" /dev/null "$BIN/prover9" -f "$LONG"
check "mace4 -f <300-char missing file>" 1 \
  "read_all_input, file $LONG not found" /dev/null "$BIN/mace4" -f "$LONG"
check "prover9 -f <4000-char missing file>" 1 \
  "read_all_input, file $LONG4000 not found" /dev/null "$BIN/prover9" -f "$LONG4000"

# M3: the same message, and mace4's -r checkpoint paths (char[512]).
for prog in prooftrans directproof interpformat; do
  check "$prog -f <300-char missing file>" 1 \
    "file $LONG not found" /dev/null "$BIN/$prog" -f "$LONG"
done
check "mace4 -r <600-char missing directory>" 1 \
  "cannot open $LONG600/saved_input.txt" /dev/null "$BIN/mace4" -r "$LONG600"

# M5: prooftrans hints -label was formatted into char[100].
check "prooftrans hints -label <300 chars>" 0 \
  "${LONG}_1" "$TMP/proof" "$BIN/prooftrans" hints -label "$LONG"
check "prooftrans hints -label <300 chars, quoted>" 0 \
  "\"a-${LONG}_1\"" "$TMP/proof" "$BIN/prooftrans" hints -label "a-$LONG"

# D2: proof tokens were read with fscanf("%s") into char[1000].
for prog in prooftrans directproof; do
  check "$prog < proof with a 200,000-char clause id" 1 \
    "Fatal error" "$TMP/longtok" "$BIN/$prog"
done

# M4: an unknown kbo_weights symbol was reported through char[200].
cat > "$TMP/kbo.in" <<END
assign(order, kbo).
list(kbo_weights).
  $LONG = 3.
end_of_list.
formulas(goals).
  p(a) -> p(a).
end_of_list.
END
check "prover9 kbo_weights with a 300-char unknown symbol" 1 \
  "init_kbo_weights, symbol $LONG not found" /dev/null "$BIN/prover9" -f "$TMP/kbo.in"

# T2: tptp_to_ladr cut a missing include's name at 60 characters.
echo "include('$LONG4000')." > "$TMP/inc.p"
check "tptp_to_ladr include('<4000-char missing file>')" 1 \
  "read_tptp_input, file $LONG4000 not found" "$TMP/inc.p" "$BIN/tptp_to_ladr"

echo
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
