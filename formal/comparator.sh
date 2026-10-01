#!/usr/bin/env bash
# Judge Solution.lean against Challenge.lean the way Palomar does: `lake comparator` from
# the pinned toolchain, with the toolchain's bundled independent kernels (nanoda and con-ron)
# besides Lean's own.  Uses the bwrap sandbox when it works; otherwise runs without it and
# says so (acceptable for checking one's own code, not for judging untrusted code).
set -euo pipefail
cd "$(dirname "$0")/Av12453"
export PATH="$HOME/.elan/bin:$PATH"
prefix=$(lean --print-prefix)
config=$(mktemp "${TMPDIR:-/tmp}/comparator.XXXXXX.json")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json, pathlib, sys
source, destination, prefix = sys.argv[1:]
config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY
if command -v bwrap >/dev/null 2>&1 && bwrap --ro-bind / / --dev /dev --proc /proc true 2>/dev/null; then
  lake comparator --config "$config"
else
  echo "warning: bwrap is unavailable; running lake comparator without its sandbox" >&2
  lake comparator --config "$config" --inadvisably-no-sandbox
fi
