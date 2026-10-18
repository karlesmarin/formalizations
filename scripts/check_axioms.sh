#!/bin/sh
# Axiom audit: prints the axioms of every main result and fails if any depends on `sorryAx`
# or on an axiom outside {propext, Classical.choice, Quot.sound}.
# The output is joined into one line before parsing: `#print axioms` wraps long declaration names
# over several lines, and parsing line by line reported standard axioms as nonstandard.
# Usage: scripts/check_axioms.sh            (runs FormalizationsTest/Axioms.lean)
#        scripts/check_axioms.sh <file>     (parses a saved output, for testing the parser)
set -e
cd "$(dirname "$0")/.."
if [ -n "$1" ]; then OUT=$(cat "$1"); else OUT=$(lake env lean FormalizationsTest/Axioms.lean 2>&1); fi
echo "$OUT"
if echo "$OUT" | grep -q "error"; then echo "FAIL: compilation error"; exit 1; fi
if echo "$OUT" | grep -q "sorryAx"; then echo "FAIL: sorryAx"; exit 1; fi
ONE=$(echo "$OUT" | tr '\n' ' ' | tr -s ' ')
BAD=$(echo "$ONE" | grep -o 'depends on axioms: *\[[^]]*\]' | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' \
  | sed 's/ //g' | grep -v -x -e propext -e Classical.choice -e Quot.sound -e '' | sort -u || true)
if [ -n "$BAD" ]; then echo "FAIL: nonstandard axioms: $BAD"; exit 1; fi
N=$(echo "$ONE" | grep -o 'depends on axioms\|does not depend on any axioms' | wc -l)
echo "OK: $N results, standard axioms only"
