#!/bin/bash
# Gate: the build must succeed, the sources must contain no sorry/axiom/
# native_decide, and every audited declaration must depend only on a subset of
# Lean's three standard axioms (propext, Classical.choice, Quot.sound).
# Depending on fewer is stronger, not weaker.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
if grep -rqn "sorry\|admit\b\|^axiom \|native_decide" Artin/*.lean; then
  echo "FAIL: sorry/axiom/native_decide present"; exit 1
fi
out=$(lake build 2>&1); rc=$?
[ "$rc" -ne 0 ] && { echo "FAIL: build exited $rc"; echo "$out" | grep -E "error:" | head; exit 1; }
echo "$out" | grep -q "Build completed successfully" || { echo "FAIL: build"; echo "$out" | grep -E "error:" | head; exit 1; }
lines=$(echo "$out" | grep "depends on axioms")
n=$(echo "$lines" | grep -c "depends on axioms")
# Pinned so a silently deleted #print axioms line fails the gate.
EXPECTED_MIN=11
if [ "$n" -lt "$EXPECTED_MIN" ]; then
  echo "FAIL: only $n axiom reports, expected >= $EXPECTED_MIN (a #print axioms line was lost?)"; exit 1
fi
bad=$(echo "$lines" | sed 's/.*depends on axioms: \[//; s/\].*//' | tr ',' '\n' \
      | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n theorems, standard axioms only)"
