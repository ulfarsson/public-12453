#!/usr/bin/env bash
# build_primes.sh -- build one av12453_gemm_split_v2 binary per prime.
#
# The modulus is a compile-time constant (-DMODP), so a CRT sweep needs one
# binary per prime.  This script compiles them in parallel and names them
# exactly as harness/run_all.sh expects: <outdir>/av12453_gemm_<prime>.
#
# Usage:
#   ./build_primes.sh --primes FILE [--outdir DIR] [--jobs K]
#                     [--store 16|32] [--cblas none|accelerate|openblas|stub]
#                     [--src FILE] [--cxx CXX] [--extra "flags"] [--dry-run]
#                     [--check-primality]
#
#   --primes FILE       one prime per line ('#' comments and blanks ignored);
#                       e.g. ../harness/primes_u16.txt (77 primes < 2^16)
#                       or   ../harness/primes_u32.txt (61 primes < 2^21)
#   --outdir DIR        where the binaries go (default ./bin_primes)
#   --jobs K            parallel compiles (default: all cores)
#   --store 16|32       force -DSTORE_BITS (default: the source's own rule,
#                       u16 for P < 2^16, u32 otherwise)
#   --cblas KIND        none (default; the built-in NEON/portable micro-kernel)
#                       accelerate  -> -DUSE_CBLAS against Apple Accelerate
#                       openblas    -> -DUSE_CBLAS against OpenBLAS
#                       stub        -> -DUSE_CBLAS against cblas_stub/ (a naive
#                                      reference loop: CORRECTNESS TEST ONLY,
#                                      it is much slower than the micro-kernel)
#   --check-primality   verify every modulus is prime before compiling
#                       (needs python3/pypy3; recommended for a new list)
#   --dry-run           print the compile commands and exit
#
# Platform recipes (auto-detected; override with --cxx / --extra):
#
#   Linux, g++            : -O3 -march=native -fopenmp
#   macOS, Apple clang    : -O3 -mcpu=apple-m1 (or -mcpu=native on newer clang)
#                           OpenMP is NOT in Apple clang: install Homebrew
#                           libomp and use
#                             -Xpreprocessor -fopenmp -I$(brew --prefix libomp)/include
#                             -L$(brew --prefix libomp)/lib -lomp
#                           This script does that automatically when it finds
#                           libomp via `brew --prefix libomp`.
#   macOS, Homebrew g++   : set --cxx g++-14 and it behaves like the Linux case.
#
# Every binary is self-testing at run time (binary64 reduction self-test,
# support check, CERTIFY against the certified 0..150 data file), so a build
# that silently used the wrong flags still cannot produce a wrong residue file
# without exiting non-zero.
set -euo pipefail
cd "$(dirname "$0")"

PRIMES=""
OUTDIR="bin_primes"
JOBS=""
STORE=""
CBLAS="none"
SRC="av12453_gemm_split_v2.cpp"
CXX_IN=""
EXTRA=""
DRYRUN=0
CHECKP=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --primes) PRIMES=$2; shift 2 ;;
    --outdir) OUTDIR=$2; shift 2 ;;
    --jobs) JOBS=$2; shift 2 ;;
    --store) STORE=$2; shift 2 ;;
    --cblas) CBLAS=$2; shift 2 ;;
    --src) SRC=$2; shift 2 ;;
    --cxx) CXX_IN=$2; shift 2 ;;
    --extra) EXTRA=$2; shift 2 ;;
    --dry-run) DRYRUN=1; shift ;;
    --check-primality) CHECKP=1; shift ;;
    -h|--help) sed -n '2,50p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

[[ -n "$PRIMES" ]] || { echo "ERROR: --primes FILE is required" >&2; exit 2; }
[[ -f "$PRIMES" ]] || { echo "ERROR: prime list not found: $PRIMES" >&2; exit 2; }
[[ -f "$SRC" ]]    || { echo "ERROR: source not found: $SRC" >&2; exit 2; }

UNAME=$(uname -s)

# ---------------------------------------------------------------- toolchain --
if [[ -n "$CXX_IN" ]]; then
  CXX="$CXX_IN"
elif [[ "$UNAME" == "Darwin" ]]; then
  CXX=${CXX:-clang++}
else
  CXX=${CXX:-g++}
fi

if [[ -z "$JOBS" ]]; then
  if [[ "$UNAME" == "Darwin" ]]; then JOBS=$(sysctl -n hw.ncpu); else JOBS=$(nproc); fi
fi

WARN="-Wall -Wextra"
BASE="-O3 -std=c++17 -funroll-loops $WARN"
ARCH="-march=native"
OMP="-fopenmp"
LIBS=""

if [[ "$UNAME" == "Darwin" ]]; then
  # Apple silicon: -march=native is not accepted by Apple clang on all versions.
  if "$CXX" -x c++ -march=native -c /dev/null -o /dev/null 2>/dev/null; then
    ARCH="-march=native"
  elif "$CXX" -x c++ -mcpu=native -c /dev/null -o /dev/null 2>/dev/null; then
    ARCH="-mcpu=native"
  else
    ARCH="-mcpu=apple-m1"
  fi
  if [[ "$(basename "$CXX")" == clang* ]]; then
    if OMPPFX=$(brew --prefix libomp 2>/dev/null) && [[ -d "$OMPPFX" ]]; then
      OMP="-Xpreprocessor -fopenmp -I$OMPPFX/include"
      LIBS="-L$OMPPFX/lib -lomp"
    else
      echo "WARN: Apple clang without Homebrew libomp -- building SINGLE-THREADED." >&2
      echo "      brew install libomp   (then re-run) for the OpenMP build." >&2
      OMP=""
    fi
  fi
fi

# ------------------------------------------------------------------- CBLAS ---
CBLAS_FLAGS=""
case "$CBLAS" in
  none) ;;
  accelerate)
    [[ "$UNAME" == "Darwin" ]] || { echo "ERROR: --cblas accelerate is macOS only" >&2; exit 2; }
    SDK=$(xcrun --show-sdk-path)
    CBLAS_FLAGS="-DUSE_CBLAS -DACCELERATE_NEW_LAPACK -DACCELERATE_LAPACK_ILP64=0 \
-I$SDK/System/Library/Frameworks/Accelerate.framework/Frameworks/vecLib.framework/Headers"
    LIBS="$LIBS -framework Accelerate"
    ;;
  openblas)
    INC=""
    for d in /usr/include/openblas /usr/include /usr/local/include \
             /opt/homebrew/opt/openblas/include; do
      [[ -f "$d/cblas.h" ]] && { INC="-I$d"; break; }
    done
    [[ -n "$INC" ]] || { echo "ERROR: no cblas.h found for --cblas openblas" >&2; exit 2; }
    CBLAS_FLAGS="-DUSE_CBLAS $INC"
    LIBS="$LIBS -lopenblas"
    [[ -d /opt/homebrew/opt/openblas/lib ]] && LIBS="$LIBS -L/opt/homebrew/opt/openblas/lib"
    ;;
  stub)
    CBLAS_FLAGS="-DUSE_CBLAS -Icblas_stub"
    ;;
  *) echo "ERROR: --cblas must be none|accelerate|openblas|stub" >&2; exit 2 ;;
esac

STOREFLAG=""
[[ -n "$STORE" ]] && STOREFLAG="-DSTORE_BITS=$STORE"

# read + normalise the prime list
mapfile -t PLIST < <(sed 's/#.*//' "$PRIMES" | tr -d '[:blank:]' | grep -E '^[0-9]+$')
[[ ${#PLIST[@]} -gt 0 ]] || { echo "ERROR: no primes in $PRIMES" >&2; exit 2; }

if [[ "$CHECKP" == "1" ]]; then
  PY=$(command -v pypy3 || command -v python3)
  [[ -n "$PY" ]] || { echo "ERROR: --check-primality needs python3 or pypy3" >&2; exit 2; }
  printf '%s\n' "${PLIST[@]}" | "$PY" -c '
import sys
bad = []
for line in sys.stdin:
    n = int(line)
    if n < 2 or (n % 2 == 0 and n != 2):
        bad.append(n); continue
    i = 3
    while i * i <= n:
        if n % i == 0:
            bad.append(n); break
        i += 2
    if n >= 1 << 21:
        print(f"ERROR: {n} >= 2^21, the exactness proof does not cover it", file=sys.stderr)
        sys.exit(2)
if bad:
    print("ERROR: composite moduli in the list: " + ", ".join(map(str, bad)), file=sys.stderr)
    sys.exit(2)
print(f"primality OK for all moduli, all < 2^21")
'
fi

mkdir -p "$OUTDIR"

CBLAS_OBJ=""
if [[ "$CBLAS" == "stub" ]]; then
  CC=${CC:-cc}
  CBLAS_OBJ="$OUTDIR/cblas_ref.o"
  echo "+ $CC -O3 $ARCH -std=c11 $WARN -c cblas_stub/cblas_ref.c -o $CBLAS_OBJ"
  [[ "$DRYRUN" == "1" ]] || $CC -O3 $ARCH -std=c11 $WARN -c cblas_stub/cblas_ref.c -o "$CBLAS_OBJ"
fi

echo "# host          : $UNAME"
echo "# compiler      : $CXX"
echo "# flags         : $BASE $ARCH $OMP $CBLAS_FLAGS $STOREFLAG $EXTRA $LIBS"
echo "# primes        : ${#PLIST[@]} from $PRIMES"
echo "# outdir        : $OUTDIR"
echo "# parallel jobs : $JOBS"

CMDFILE=$(mktemp)
trap 'rm -f "$CMDFILE"' EXIT
for p in "${PLIST[@]}"; do
  printf '%s %s -DMODP=%sull %s %s %s %s %s %s -o %s/av12453_gemm_%s\n' \
    "$CXX" "$BASE $ARCH $OMP" "$p" "$CBLAS_FLAGS" "$STOREFLAG" "$EXTRA" \
    "$SRC" "$CBLAS_OBJ" "$LIBS" "$OUTDIR" "$p" >> "$CMDFILE"
done

if [[ "$DRYRUN" == "1" ]]; then cat "$CMDFILE"; exit 0; fi

# xargs -P: one compile per prime, JOBS at a time; fail the script if any fail.
FAIL=0
xargs -P "$JOBS" -I{} sh -c 'eval "$1" || { echo "BUILD FAILED: $1" >&2; exit 1; }' _ {} \
  < "$CMDFILE" || FAIL=1

BUILT=$(ls -1 "$OUTDIR" | grep -c '^av12453_gemm_[0-9]*$' || true)
echo "# built $BUILT / ${#PLIST[@]} binaries in $OUTDIR"
if [[ "$FAIL" != "0" || "$BUILT" -ne "${#PLIST[@]}" ]]; then
  echo "ERROR: not every prime built" >&2
  exit 1
fi

# one smoke test: the first prime must pass its own checks at a tiny N
SMOKE="$OUTDIR/av12453_gemm_${PLIST[0]}"
echo "# smoke test: $SMOKE --n 30 --threads 1"
"$SMOKE" --n 30 --threads 1 | tail -3
echo "# OK"
