#!/bin/sh
# Regression tests for TPTP input, through both of its readers:
# tptp_to_ladr, whose translation is read back by prover9 and mace4, and
# the native reader in prover9, fof-prover9 and mace4 -tptp.  Each case
# checks what the input means, not just its text: a problem must prove
# what the TPTP says, and must not prove what it does not -- for the
# second kind, mace4 must also find the countermodel.  Run via
# 'make test8' from the repo root (needs bin/ already built -- run
# 'make all' first if it isn't).

BIN="${1:-bin}"
for prog in tptp_to_ladr prover9 fof-prover9 mace4; do
  if [ ! -x "$BIN/$prog" ]; then
    echo "No $prog binary in $BIN -- run 'make all' first, then 'make test8'." >&2
    exit 2
  fi
done
BIN=$(cd "$BIN" && pwd)

# 'timeout' is not a stock macOS utility (see distinctness_test.sh).  It
# is only a safety net here: every prover9 and mace4 run below has its
# own -t limit.
if command -v timeout >/dev/null 2>&1; then
  TIMEOUT_CMD="timeout 30"
else
  echo "Note: no 'timeout' command on this system -- running without the" >&2
  echo "external safety-net timeout (relying on the programs' own -t" >&2
  echo "limits instead)." >&2
  TIMEOUT_CMD=""
fi

W="${TMPDIR:-/tmp}/tptp_translate_test.$$"
rm -rf "$W"
mkdir "$W" || exit 2
trap 'rm -rf "$W"' 0
trap 'exit 1' 1 2 15

# tptp_to_ladr resolves an include() from the current directory, and the
# native reader relative to the including file and then under $TPTP.
# With both at $W, the same inputs work for both readers.
TPTP="$W"
export TPTP

pass=0
fail=0

# mk FILE LINE... -- write a test input, one argument per line
mk() {
  f="$1"; shift
  printf '%s\n' "$@" > "$W/$f"
}

# result DESC EXPECTED GOT
result() {
  if [ "$3" = "$2" ]; then
    printf "  PASS  %-50s (%s)\n" "$1" "$3"
    pass=$((pass+1))
  else
    printf "  FAIL  %-50s expected %s, got %s\n" "$1" "$2" "${3:-<none>}"
    fail=$((fail+1))
  fi
}

# The first SZS status word on stdin.
szs() {
  sed -n 's/.*SZS status \([A-Za-z]*\).*/\1/p' | head -n 1
}

# translate FILE.p -- tptp_to_ladr FILE.p > FILE.in, run in $W so that
# include() paths resolve there.
translate() {
  (cd "$W" && $TIMEOUT_CMD "$BIN/tptp_to_ladr" < "$1" > "${1%.p}.in" 2>&1)
}

# text DESC FILE.p STRING -- the translation must contain STRING
text() {
  if translate "$2" && grep -F -- "$3" "$W/${2%.p}.in" >/dev/null; then
    got=present
  else
    got=absent
  fi
  result "$1" present "$got"
}

# The exit reason prover9 or mace4 reports on stdin: max_proofs,
# sos_empty, max_models, exhausted, max_seconds, ..., or fatal_error.
reason() {
  sed -n -e 's/.* exit (\([a-z_]*\)).*/\1/p' \
         -e 's/^Fatal error.*/fatal_error/p' | head -n 1
}

# ladr DESC FILE.p REASON -- translate, then run prover9 on the
# translation: REASON is max_proofs (proved) or sos_empty (not provable).
# For sos_empty, mace4 must also find a countermodel of the translation:
# no proof is not enough on its own.
ladr() {
  if ! translate "$2"; then
    result "$1" "$3" "translation-failed"
    return
  fi
  got=$(cd "$W" && $TIMEOUT_CMD "$BIN/prover9" -t 5 \
          -f "${2%.p}.in" < /dev/null 2>&1 | reason)
  if [ "$3" = sos_empty ] && [ "$got" = sos_empty ]; then
    m=$(cd "$W" && $TIMEOUT_CMD "$BIN/mace4" -t 5 -N 6 \
          -f "${2%.p}.in" < /dev/null 2>&1 | reason)
    [ "$m" = max_models ] || got="sos_empty,but-mace4:${m:-<none>}"
  fi
  result "$1" "$3" "$got"
}

# native DESC FILE.p STATUS -- prover9's own TPTP reader
native() {
  got=$(cd "$W" && $TIMEOUT_CMD "$BIN/prover9" -t 5 "$2" < /dev/null 2>&1 | szs)
  result "$1" "$3" "$got"
}

# native_fof DESC FILE.p STATUS -- fof-prover9 (the same reader)
native_fof() {
  got=$(cd "$W" && $TIMEOUT_CMD "$BIN/fof-prover9" -t 5 "$2" < /dev/null 2>&1 | szs)
  result "$1" "$3" "$got"
}

# native_mace4 DESC FILE.p STATUS -- mace4's TPTP mode (the same reader)
native_mace4() {
  got=$(cd "$W" && $TIMEOUT_CMD "$BIN/mace4" -tptp -t 5 -N 6 \
          -f "$2" < /dev/null 2>&1 | szs)
  result "$1" "$3" "$got"
}

echo "TPTP input matrix:"

# T4: "~" applied to a quantified formula without parentheses.  The
# parser binds the "~" to the quantifier prefix, and tptp_to_ladr used to
# drop both the negation and the quantifier: "~ ! [X] : p(X)" became
# "p(X)", the opposite of what it says.
mk neg.p      'fof(t,axiom, ~ ! [X] : p(X) ).'
mk neg2.p     'fof(a1,axiom, ~ ! [X] : p(X) ).' \
              'fof(c1,conjecture, ? [X] : ~ p(X) ).'
mk negex.p    'fof(a1,axiom, ~ ? [X] : p(X) ).' \
              'fof(c1,conjecture, ! [X] : ~ p(X) ).'
mk negnest.p  'fof(a1,axiom, ! [X] : ~ ? [Y] : q(X,Y) ).' \
              'fof(c1,conjecture, ~ q(a,b) ).'
mk negneg.p   'fof(a1,axiom, ~ ~ ? [X] : p(X) ).' \
              'fof(c1,conjecture, p(c) ).'
mk neginv.p   'fof(a1,axiom, ~ ! [X] : p(X) ).' \
              'fof(c1,conjecture, p(c) ).'
text   "T4a ~![X]:p(X) translates to -(all X p(X))" neg.p '-(all X p(X))'
ladr   "T4b ~![X]:p(X) |- ?[X]:~p(X)"              neg2.p    max_proofs
ladr   "T4c ~?[X]:p(X) |- ![X]:~p(X)"              negex.p   max_proofs
ladr   "T4d ![X]:~?[Y]:q(X,Y) |- ~q(a,b)"          negnest.p max_proofs
ladr   "T4e ~~?[X]:p(X) |/- p(c)"                  negneg.p  sos_empty
ladr   "T4f ~![X]:p(X) |/- p(c) (was unsound)"     neginv.p  sos_empty
native "T4g native: ~![X]:p(X) |- ?[X]:~p(X)"      neg2.p    Theorem
native "T4h native: ![X]:~?[Y]:q(X,Y) |- ~q(a,b)"  negnest.p Theorem
native "T4i native: ~![X]:p(X) |/- p(c)"           neginv.p  GaveUp
native_mace4 "T4j mace4 -tptp: ~![X]:p(X) |/- p(c)" neginv.p CounterSatisfiable

# T5: a TPTP formula name may be a single-quoted atom.  tptp_to_ladr
# copied it into label(...) as is, but LADR quotes with ", so prover9
# could not read the translation back.
mk qname.p    "fof('EQ-var',axiom, p(a) )." \
              "fof('a b',axiom, p(a) => q(a) )." \
              'fof(g,conjecture, q(a) ).'
ladr   "T5a quoted formula names: readable, proves"  qname.p   max_proofs
native "T5b native: quoted formula names"           qname.p   Theorem

# T6: TPTP's "distinct objects", written in double quotes, are pairwise
# unequal but may equal an ordinary term.  tptp_to_ladr could not lex
# them at all.  T6c also has them in an included file, next to comments
# that contain quotes of both kinds.
mk do.p       'fof(ax,axiom, p("Apple") & p("Microsoft") & p("Sun") ).' \
              'fof(g,conjecture, "Apple" != "Microsoft" ).'
mk dc.p       'fof(ax,axiom, p("a") & p("b") & p(cat) ).' \
              'fof(g,conjecture, "a" != cat ).'
mkdir "$W/ax"
mk ax/do.ax   "% a comment that isn't a \"distinct object\"" \
              'fof(inc,axiom, p("x") ).'
mk doinc.p    "/* a block comment, with 'quotes' and \"quotes\" */" \
              "include('ax/do.ax')." \
              'fof(ax,axiom, p("a b") ).' \
              'fof(g,conjecture, "a b" != "x" ).'
ladr   "T6a \"Apple\" != \"Microsoft\""               do.p      max_proofs
ladr   "T6b \"a\" != cat does not follow"             dc.p      sos_empty
ladr   "T6c distinct objects in an included file"      doinc.p   max_proofs
native "T6d native: \"Apple\" != \"Microsoft\""       do.p      Theorem
native "T6e native: \"a\" != cat does not follow"     dc.p      GaveUp
native_mace4 "T6f mace4 -tptp: \"a\" != cat"          dc.p      CounterSatisfiable
native "T6g native: in an included file"           doinc.p   Theorem

# T7: include('file', [names]) includes only the named formulas.  Both
# readers ignored the list and took the whole file, which can make a
# conjecture provable from an axiom the problem had excluded.  A
# selection applies to everything the file yields, including what it
# includes in turn, so nested selections intersect (as in tptp4X); and
# 'i1' and i1 are the same name.
mk ax/M.ax    'fof(i1,axiom, p(a) ).' \
              'fof(i2,axiom, q(b) ).' \
              'fof(i3,axiom, r(c) ).'
mk ax/N.ax    "include('ax/M.ax',[i1,i2])." \
              'fof(n1,axiom, s(d) ).'
mk ax/N2.ax   "include('ax/M.ax')." \
              'fof(n1,axiom, s(d) ).'
mk selr.p     "include('ax/M.ax',[i1,i3])." 'fof(g,conjecture, r(c) ).'
mk selq.p     "include('ax/M.ax',[i1,i3])." 'fof(g,conjecture, q(b) ).'
mk allq.p     "include('ax/M.ax')."         'fof(g,conjecture, q(b) ).'
mk starq.p    "include('ax/M.ax',*)."       'fof(g,conjecture, q(b) ).'
mk emptyq.p   "include('ax/M.ax',[])."      'fof(g,conjecture, q(b) ).'
mk qselq.p    "include('ax/M.ax',['i1','i3'])." 'fof(g,conjecture, q(b) ).'
mk qselr.p    "include('ax/M.ax',['i3'])."  'fof(g,conjecture, r(c) ).'
mk nestqs.p   "include('ax/N.ax',[i2,n1])." 'fof(g,conjecture, q(b) & s(d) ).'
mk nestp.p    "include('ax/N.ax',[i2,n1])." 'fof(g,conjecture, p(a) ).'
mk nestr.p    "include('ax/N.ax',[i3])."    'fof(g,conjecture, r(c) ).'
mk nests.p    "include('ax/N2.ax',[i2])."   'fof(g,conjecture, s(d) ).'
ladr   "T7a selected formula is kept"              selr.p    max_proofs
ladr   "T7b excluded formula is dropped (unsound)" selq.p    sos_empty
ladr   "T7c control: include/1 takes all"          allq.p    max_proofs
ladr   "T7d control: '*' takes all"                starq.p   max_proofs
ladr   "T7e empty selection takes nothing"         emptyq.p  sos_empty
ladr   "T7f quoted names: excluded is dropped"     qselq.p   sos_empty
ladr   "T7g quoted names: selected is kept"        qselr.p   max_proofs
ladr   "T7h nested: kept by both selections"       nestqs.p  max_proofs
ladr   "T7i nested: dropped by the outer one"      nestp.p   sos_empty
ladr   "T7j nested: dropped by the inner one"      nestr.p   sos_empty
ladr   "T7k nested include/1, outer selection"     nests.p   sos_empty
native "T7l native: selected formula is kept"      selr.p    Theorem
native "T7m native: excluded is dropped (unsound)" selq.p    GaveUp
native_mace4 "T7n mace4 -tptp: excluded is dropped" selq.p   CounterSatisfiable
native_fof   "T7o fof-prover9: excluded is dropped" selq.p   GaveUp
native "T7p native: control: include/1 takes all"  allq.p    Theorem
native "T7q native: empty selection takes nothing" emptyq.p  GaveUp
native "T7r native: quoted names: excluded"        qselq.p   GaveUp
native "T7s native: quoted names: selected"        qselr.p   Theorem
native "T7t native: nested: kept by both"          nestqs.p  Theorem
native "T7u native: nested: dropped by outer"      nestp.p   GaveUp
native "T7v native: nested: dropped by inner"      nestr.p   GaveUp
native "T7w native: nested include/1, outer sel."  nests.p   GaveUp
native_mace4 "T7x mace4 -tptp: nested, dropped"    nestp.p   CounterSatisfiable

# T8: NAND ("~&") and NOR ("~|").  The conversion code has always been
# there, but the parser was never told the operators exist, so every
# problem using them failed to translate.  T8c checks both meanings in
# both directions.
mk nand.p     'fof(a,axiom, p(a) ~& q(b) ).' \
              'fof(g,conjecture, ~ (p(a) & q(b)) ).'
mk nor.p      'fof(a,axiom, p(a) ~| q(b) ).' \
              'fof(g,conjecture, ~ (p(a) | q(b)) ).'
mk nandnor.p  'fof(g,conjecture, ( (p ~& q) <=> ~ (p & q) )' \
              '                  & ( (p ~| q) <=> ~ (p | q) ) ).'
ladr   "T8a p ~& q |- ~(p & q)"                     nand.p    max_proofs
ladr   "T8b p ~| q |- ~(p | q)"                     nor.p     max_proofs
ladr   "T8c (p ~& q) <=> ~(p & q), same for ~|"     nandnor.p max_proofs
native "T8d native: p ~& q |- ~(p & q)"             nand.p    Theorem
native "T8e native: p ~| q |- ~(p | q)"             nor.p     Theorem
native "T8f native: ~& and ~| equivalences"         nandnor.p Theorem

echo
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
