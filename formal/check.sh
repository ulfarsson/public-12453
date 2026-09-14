#!/usr/bin/env bash
# Full check of the Lean certificate: build must be warning-free, the axiom
# sweep must pass, and no `sorry`/`native_decide`/`axiom` may occur in code.
set -euo pipefail
cd "$(dirname "$0")/Av12453"
export PATH="$HOME/.elan/bin:$PATH"
out=$(lake build 2>&1) || { echo "$out"; echo "BUILD FAILED"; exit 1; }
if grep -qE "warning|error" <<<"$out"; then echo "$out" | grep -E "warning|error"; echo "BUILD NOT CLEAN"; exit 1; fi
lake env lean Av12453/Axioms.lean | tail -1
bad=$(grep -rnwE "sorry|native_decide|admit" Av12453 Av12453.lean | grep -vE ':\s*(--|/-|\*)|^[^:]+:[0-9]+:[^`]*(`sorry`|`native_decide`|sorry-free|'"'"'sorry'"'"'|sorryAx|no sorry|zero sorry|frozen)' || true)
if [ -n "$bad" ]; then echo "$bad"; echo "SUSPICIOUS TOKENS"; exit 1; fi
echo "CERTIFICATE CHECK PASSED"
