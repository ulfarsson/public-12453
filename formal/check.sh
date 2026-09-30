#!/usr/bin/env bash
# Full check of the Lean certificate: build must be warning-free, the axiom
# sweep must pass and cover every module of both libraries, and no
# `sorry`/`native_decide`/`admit` may occur in code.
set -euo pipefail
cd "$(dirname "$0")/Av12453"
export PATH="$HOME/.elan/bin:$PATH"
out=$(lake build 2>&1) || { echo "$out"; echo "BUILD FAILED"; exit 1; }
if grep -qE "warning|error" <<<"$out"; then echo "$out" | grep -E "warning|error"; echo "BUILD NOT CLEAN"; exit 1; fi
sweep=$(lake env lean Av12453/Axioms.lean 2>&1) || { echo "$sweep" | tail -5; echo "SWEEP FAILED"; exit 1; }
echo "$sweep" | grep -o "checked [0-9]* declarations"
# The sweep discovers modules from the environment; confirm it saw every .lean
# file of the two libraries (the two root modules count, Axioms.lean does not).
swept=$(echo "$sweep" | grep -o "sweeping [0-9]* modules" | grep -o "[0-9]*")
files=$(find PermPatterns Av12453 -name '*.lean' | wc -l)
expected=$(( files - 1 + 2 ))
if [ "$swept" != "$expected" ]; then echo "SWEEP COVERAGE: swept $swept modules but the tree has $expected"; exit 1; fi
echo "sweep covered all $swept modules"
bad=$(grep -rnwE "sorry|native_decide|admit" Av12453 Av12453.lean PermPatterns PermPatterns.lean | grep -vE ':\s*(--|/-|\*)|^[^:]+:[0-9]+:[^`]*(`sorry`|`native_decide`|sorry-free|'"'"'sorry'"'"'|sorryAx|no sorry|zero sorry|frozen)' || true)
if [ -n "$bad" ]; then echo "$bad"; echo "SUSPICIOUS TOKENS"; exit 1; fi
echo "CERTIFICATE CHECK PASSED"
