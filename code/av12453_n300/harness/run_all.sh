#!/usr/bin/env bash
# run_all.sh -- run one prime at a time through a per-prime engine binary,
# writing residues/<prime>.txt in the shared harness format (see
# residue_io.py), with a log of wall time per prime.  Resumable: an existing
# residue file that passes the quick structural sanity check is skipped.
#
# BINARY CONTRACT (documented assumption -- the GEMM engine that runs this
# is a separate build; see REPORT.md "assumptions" section):
#   Each prime gets its own compiled binary (primes are a compile-time
#   -DMODP constant, following the existing av12453_homog_split.cpp
#   pattern), named by substituting {bindir} and {prime} into --pattern
#   (default '{bindir}/av12453_gemm_{prime}').  The binary is invoked as:
#     BIN --n N --threads K --out OUTFILE
#   writes "# prime P N" then "n residue" lines to OUTFILE, and exits 0 iff
#   every built-in check (CERTIFY, support check, ...) passed.  If your
#   actual engine's CLI differs, adjust --pattern and/or the invocation
#   line marked "ENGINE INVOCATION" below, or use --dry-run to see the
#   planned commands without needing a real binary at all.
#
# Usage:
#   run_all.sh --bindir DIR --primes FILE --n N --threads K
#              [--outdir DIR] [--pattern PATTERN] [--extra-args "..."]
#              [--dry-run]
#
# Exit status: 0 if every prime in the list ends OK or SKIP; 1 if any prime
# FAILed (the script still processes the remaining primes before exiting
# nonzero, so one bad prime does not block the rest of a long sweep).

set -euo pipefail

BINDIR=""
PRIMEFILE=""
N=""
THREADS=""
OUTDIR="residues"
PATTERN='{bindir}/av12453_gemm_{prime}'
EXTRA_ARGS=""
DRY_RUN=0

usage() {
  sed -n '2,27p' "$0" | sed 's/^# \{0,1\}//'
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --bindir) BINDIR=$2; shift 2 ;;
    --primes) PRIMEFILE=$2; shift 2 ;;
    --n) N=$2; shift 2 ;;
    --threads) THREADS=$2; shift 2 ;;
    --outdir) OUTDIR=$2; shift 2 ;;
    --pattern) PATTERN=$2; shift 2 ;;
    --extra-args) EXTRA_ARGS=$2; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown argument: $1" >&2; usage; exit 2 ;;
  esac
done

if [[ -z "$BINDIR" || -z "$PRIMEFILE" || -z "$N" || -z "$THREADS" ]]; then
  echo "ERROR: --bindir, --primes, --n, --threads are all required" >&2
  usage
  exit 2
fi
if [[ ! -f "$PRIMEFILE" ]]; then
  echo "ERROR: prime list not found: $PRIMEFILE" >&2
  exit 2
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RESIDUE_IO="$HERE/residue_io.py"
PY=python3
command -v pypy3 >/dev/null 2>&1 && PY=pypy3

mkdir -p "$OUTDIR"
LOGDIR="$(dirname "$OUTDIR")/logs"
mkdir -p "$LOGDIR"
RUNLOG="$(dirname "$OUTDIR")/run_all.log"

log() {
  # log EVENT prime=P [key=val ...]
  local line
  line="$(date -u +%Y-%m-%dT%H:%M:%SZ) $*"
  echo "$line" | tee -a "$RUNLOG"
}

quick_check() {
  # quick_check FILE PRIME N -> exit 0 if OK, 1 otherwise (also prints reason)
  "$PY" "$RESIDUE_IO" check "$1" "$2" "$3"
}

fail_count=0
ok_count=0
skip_count=0

while IFS= read -r RAW || [[ -n "$RAW" ]]; do
  P="${RAW%%#*}"
  P="$(echo "$P" | tr -d '[:space:]')"
  [[ -z "$P" ]] && continue
  if ! [[ "$P" =~ ^[0-9]+$ ]]; then
    echo "WARN skipping non-integer prime-list line: $RAW" >&2
    continue
  fi

  OUT="$OUTDIR/${P}.txt"

  if [[ -f "$OUT" ]] && quick_check "$OUT" "$P" "$N" >"$LOGDIR/${P}.sanity.log" 2>&1; then
    log "SKIP prime=$P reason=existing-residue-file-passes-sanity-check file=$OUT"
    skip_count=$((skip_count + 1))
    continue
  fi
  if [[ -f "$OUT" ]]; then
    log "WARN prime=$P reason=existing-residue-file-failed-sanity-check will-rerun file=$OUT detail=\"$(grep -v 'cannot find your CPU' "$LOGDIR/${P}.sanity.log" 2>/dev/null | tr '\n' ' ')\""
  fi

  BIN="$(echo "$PATTERN" | sed "s#{bindir}#$BINDIR#g; s#{prime}#$P#g")"

  if [[ "$DRY_RUN" == "1" ]]; then
    log "DRYRUN prime=$P binary=$BIN out=$OUT threads=$THREADS n=$N"
    continue
  fi

  if [[ ! -x "$BIN" ]]; then
    log "FAIL prime=$P reason=binary-not-found-or-not-executable binary=$BIN"
    fail_count=$((fail_count + 1))
    continue
  fi

  TMP="$OUT.tmp.$$"
  ENGLOG="$LOGDIR/${P}.log"
  START=$(date +%s.%N)
  set +e
  # --- ENGINE INVOCATION (adjust here if your binary's CLI differs) ---
  OMP_NUM_THREADS="$THREADS" "$BIN" --n "$N" --threads "$THREADS" --out "$TMP" $EXTRA_ARGS \
    >"$ENGLOG" 2>&1
  RC=$?
  set -e
  END=$(date +%s.%N)
  WALL=$(awk -v a="$START" -v b="$END" 'BEGIN{printf "%.3f", b-a}')

  if [[ "$RC" -ne 0 ]]; then
    log "FAIL prime=$P reason=nonzero-exit rc=$RC wall_s=$WALL log=$ENGLOG"
    rm -f "$TMP"
    fail_count=$((fail_count + 1))
    continue
  fi

  if ! quick_check "$TMP" "$P" "$N" >"$LOGDIR/${P}.sanity.log" 2>&1; then
    log "FAIL prime=$P reason=post-run-sanity-check-failed wall_s=$WALL detail=\"$(grep -v 'cannot find your CPU' "$LOGDIR/${P}.sanity.log" | tr '\n' ' ')\""
    rm -f "$TMP"
    fail_count=$((fail_count + 1))
    continue
  fi

  mv "$TMP" "$OUT"
  log "OK prime=$P wall_s=$WALL out=$OUT log=$ENGLOG"
  ok_count=$((ok_count + 1))
done < "$PRIMEFILE"

log "SUMMARY ok=$ok_count skip=$skip_count fail=$fail_count total=$((ok_count + skip_count + fail_count))"

if [[ "$fail_count" -gt 0 ]]; then
  exit 1
fi
exit 0
