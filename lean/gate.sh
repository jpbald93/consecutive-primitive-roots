#!/bin/bash
# Gate: build must succeed, no sorry/axiom/native_decide, and every theorem must
# depend only on a SUBSET of Lean's three standard axioms
# (propext, Classical.choice, Quot.sound). Depending on fewer is stronger, not weaker.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
if grep -rqn "sorry\|admit\b\|^axiom \|native_decide" Artin/*.lean; then echo "FAIL: sorry/axiom/native_decide present"; exit 1; fi
out=$(lake build 2>&1)
echo "$out" | grep -q "Build completed successfully" || { echo "FAIL: build"; echo "$out" | grep -E "error:" | head; exit 1; }
lines=$(echo "$out" | grep "depends on axioms")
n=$(echo "$lines" | grep -c "depends on axioms")
bad=$(echo "$lines" | sed 's/.*depends on axioms: \[//; s/\].*//' | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n theorems, standard axioms only)"
