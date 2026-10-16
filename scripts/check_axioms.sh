#!/bin/sh
# encaje: CI script of this Lean repository (not a research tool).
# Axiom audit: prints the axioms of every main result and fails if any depends on `sorryAx`
# or on an axiom outside {propext, Classical.choice, Quot.sound}.
set -e
cd "$(dirname "$0")/.."
OUT=$(lake env lean FormalizationsTest/Axioms.lean 2>&1)
echo "$OUT"
if echo "$OUT" | grep -q "error"; then echo "FAIL: compilation error"; exit 1; fi
if echo "$OUT" | grep -q "sorryAx"; then echo "FAIL: sorryAx"; exit 1; fi
BAD=$(echo "$OUT" | grep "depends on axioms" | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | sed 's/ //g' \
  | grep -v -x -e propext -e Classical.choice -e Quot.sound | sort -u)
if [ -n "$BAD" ]; then echo "FAIL: nonstandard axioms: $BAD"; exit 1; fi
echo "OK: $(echo "$OUT" | grep -c "axioms") results, standard axioms only"
