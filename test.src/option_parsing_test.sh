#!/bin/sh
# Option-dependency regression checks.  Some parms set others when they
# are assigned (max_minutes sets max_seconds, pick_given_ratio sets
# weight_part, ...).  Each case assigns one parm to a trivial problem,
# then checks the derived assignment that prover9 echoes and that the
# search still runs to a proof.  Run via 'make test12' from the repo root
# (needs bin/prover9 already built -- run 'make all' first if it isn't).

P9="${1:-bin/prover9}"
if [ ! -x "$P9" ]; then
  echo "No prover9 binary at $P9 -- run 'make all' first, then 'make test12'." >&2
  exit 2
fi

# 'timeout' is not a stock macOS utility; see distinctness_test.sh.
if command -v timeout >/dev/null 2>&1; then
  TIMEOUT_CMD="timeout 10"
else
  echo "Note: no 'timeout' command on this system -- running without the" >&2
  echo "external safety-net timeout." >&2
  TIMEOUT_CMD=""
fi

pass=0
fail=0

check() {
  desc="$1"; assignment="$2"; expected="$3"
  out=$(printf '%s\n' "$assignment" "formulas(sos)." "  p." "  -p." \
               "end_of_list." | $TIMEOUT_CMD "$P9" 2>&1)
  if printf '%s\n' "$out" | grep -F -q -e "-> $expected" &&
     printf '%s\n' "$out" | grep -q 'THEOREM PROVED'; then
    printf "  PASS  %-45s (%s)\n" "$desc" "$expected"
    pass=$((pass+1))
  else
    printf "  FAIL  %-45s expected %s\n" "$desc" "$expected"
    printf '%s\n' "$out" | grep -e '->' -e 'range' -e 'Fatal' -e 'runtime error' |
      sed 's/^/        | /'
    fail=$((fail+1))
  fi
}

echo "Option dependency checks:"

# -1 means "no limit".  Scaling it gave max_seconds -60, -3600 or -86400,
# which is out of range, and prover9 stopped with a fatal error.
check "max_minutes -1 (no limit)" "assign(max_minutes, -1)." "assign(max_seconds, -1)."
check "max_hours -1 (no limit)"   "assign(max_hours, -1)."   "assign(max_seconds, -1)."
check "max_days -1 (no limit)"    "assign(max_days, -1)."    "assign(max_seconds, -1)."

# Large limits overflowed int when scaled (signed overflow), and the
# wrapped negative value was then rejected as out of range.
check "max_minutes 50000000 (saturates)" "assign(max_minutes, 50000000)." \
      "assign(max_seconds, 2147483647)."
check "max_hours 1000000 (saturates)"    "assign(max_hours, 1000000)." \
      "assign(max_seconds, 2147483647)."

# pick_given_ratio -1 (unset) was passed on as weight_part -1, which is
# below weight_part's minimum of 0.
check "pick_given_ratio -1 (unset)" "assign(pick_given_ratio, -1)." "assign(weight_part, 0)."

# Controls: in-range derivations are unchanged.
check "max_minutes 2 (control)"      "assign(max_minutes, 2)."      "assign(max_seconds, 120)."
check "max_hours 3 (control)"        "assign(max_hours, 3)."        "assign(max_seconds, 10800)."
check "pick_given_ratio 4 (control)" "assign(pick_given_ratio, 4)." "assign(weight_part, 4)."

# A selector part of INT_MAX means "take everything from this selector
# first".  The cycle size, the sum of the parts of the nonempty
# selectors, overflowed when another selector also had clauses, and the
# wrapped negative value made every new clause look about to be
# selected, so sos_limit never deleted anything.

desc="age_part 2147483647: sos_limit applies"
out=$($TIMEOUT_CMD "$P9" 2>&1 <<'END'
assign(age_part, 2147483647).
assign(weight_part, 1).
assign(false_part, 0).
assign(true_part, 0).
assign(sos_limit, 20).
assign(max_given, 30).
formulas(sos).
  e * x = x.
  x' * x = e.
  (x * y) * z = x * (y * z).
  x * x = e.
end_of_list.
END
)
deleted=$(printf '%s\n' "$out" | sed -n 's/.*Sos_limit_deleted=\([0-9]*\).*/\1/p')
if [ "${deleted:-0}" -gt 0 ]; then
  printf "  PASS  %-45s (Sos_limit_deleted=%s)\n" "$desc" "$deleted"
  pass=$((pass+1))
else
  printf "  FAIL  %-45s expected Sos_limit_deleted > 0, got %s\n" \
         "$desc" "${deleted:-<none>}"
  printf '%s\n' "$out" | grep -e 'Fatal' -e 'runtime error' -e 'exit (' |
    sed 's/^/        | /'
  fail=$((fail+1))
fi

echo
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
