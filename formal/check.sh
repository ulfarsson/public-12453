#!/usr/bin/env bash
# Full check of the Lean certificate: the two libraries and Solution.lean must
# build warning-free and Challenge.lean with exactly its four `sorry` warnings
# (the placeholders of the statement file), the axiom sweep must pass and cover
# every module of both libraries, and no `sorry`/`native_decide`/`admit` may
# occur in the code of the libraries.
set -euo pipefail
cd "$(dirname "$0")/Av12453"
export PATH="$HOME/.elan/bin:$PATH"
out=$(lake build PermPatterns Av12453 Solution 2>&1) || { echo "$out"; echo "BUILD FAILED"; exit 1; }
if grep -qE "warning|error" <<<"$out"; then echo "$out" | grep -E "warning|error"; echo "BUILD NOT CLEAN"; exit 1; fi
# Challenge.lean states the four headline theorems with `sorry` (the Palomar statement file);
# its only permitted warnings are those four.
out=$(lake build Challenge 2>&1) || { echo "$out"; echo "BUILD FAILED"; exit 1; }
nsorry=$(grep -c "Challenge.lean:.*declaration uses .sorry." <<<"$out" || true)
other=$(grep -E "warning|error" <<<"$out" | grep -vc "Challenge.lean:.*declaration uses .sorry." || true)
if [ "$nsorry" != "4" ] || [ "$other" != "0" ]; then echo "$out" | grep -E "warning|error"; echo "CHALLENGE NOT AS EXPECTED"; exit 1; fi
sweep=$(lake env lean Av12453/Axioms.lean 2>&1) || { echo "$sweep" | tail -5; echo "SWEEP FAILED"; exit 1; }
echo "$sweep" | grep -o "checked [0-9]* declarations"
# The sweep discovers modules from the environment; confirm it saw every .lean
# file of the two libraries (the two root modules count, Axioms.lean does not).
swept=$(echo "$sweep" | grep -o "sweeping [0-9]* modules" | grep -o "[0-9]*")
files=$(find PermPatterns Av12453 -name '*.lean' | wc -l)
expected=$(( files - 1 + 2 ))
if [ "$swept" != "$expected" ]; then echo "SWEEP COVERAGE: swept $swept modules but the tree has $expected"; exit 1; fi
echo "sweep covered all $swept modules"
# every module must be opened with `import all` so that its private declarations are swept
for f in $(find PermPatterns Av12453 -name '*.lean' ! -name Axioms.lean); do
  m=$(echo "${f%.lean}" | tr / .)
  grep -qx "import all $m" Av12453/Axioms.lean || { echo "SWEEP MISSES PRIVATE DECLARATIONS OF $m (add 'import all $m' to Axioms.lean)"; exit 1; }
done
echo "sweep opens every module with import all"
bad=$(grep -rnwE "sorry|native_decide|admit" Av12453 Av12453.lean PermPatterns PermPatterns.lean | grep -vE ':\s*(--|/-|\*)|^[^:]+:[0-9]+:[^`]*(`sorry`|`native_decide`|sorry-free|'"'"'sorry'"'"'|sorryAx|no sorry|zero sorry|frozen)' || true)
if [ -n "$bad" ]; then echo "$bad"; echo "SUSPICIOUS TOKENS"; exit 1; fi
echo "CERTIFICATE CHECK PASSED"
