#!/usr/bin/env bash
# Fails if any audited theorem uses an axiom other than the three standard ones.
set -euo pipefail
out=$(lake env lean scripts/Axioms.lean 2>&1)
echo "$out"
n=$(grep -c "depends on axioms" <<<"$out" || true)
expected=$(grep -c "^#print axioms" scripts/Axioms.lean)
if [ "$n" -ne "$expected" ]; then
  echo "expected $expected axiom reports, got $n"; exit 1
fi
bad=$(grep "depends on axioms" <<<"$out" | sed 's/.*\[\(.*\)\].*/\1/' | tr ',' '\n' \
  | sed 's/ //g' | grep -v -x -E 'propext|Classical.choice|Quot.sound' || true)
if [ -n "$bad" ]; then
  echo "non-standard axioms found: $bad"; exit 1
fi
echo "axiom audit passed: $n theorems, standard axioms only"
