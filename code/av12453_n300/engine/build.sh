#!/usr/bin/env bash
# build.sh -- build every supported flavour of av12453_gemm_split_v2.
#
# Binaries produced in ./bin:
#   gemm_u16_65521       u16 storage, P = 65521    (largest prime < 2^16)
#   gemm_u16_65519       u16 storage, P = 65519
#   gemm_u32_2097143     u32 storage, P = 2097143  (largest prime < 2^21)
#   gemm_u32_2097133     u32 storage, P = 2097133
#   gemm_modp            generic -DMODP build, P taken from $MODP (default 65521)
#   gemm_u32_65521       u32 storage with a 16-bit prime (storage-path cross-check)
#   gemm_portable_65521  portable (non-NEON) micro-kernel, for kernel cross-check
#   gemm_cblas_65521     -DUSE_CBLAS path against the reference cblas_dgemm in
#   gemm_cblas_2097143   cblas_stub/ (correctness test only -- it is a naive
#                        triple loop, NOT a fast BLAS); a real BLAS is picked up
#                        instead when USE_SYSTEM_CBLAS=1 is set, see below.
#
# v2: CXXFLAGS carries -Wall -Wextra and the build is warning-free.
#
# The primality of every hard-wired modulus is verified before compiling.
set -euo pipefail
cd "$(dirname "$0")"
SRC=av12453_gemm_split_v2.cpp
OUT=bin
mkdir -p "$OUT" tmp

CXX=${CXX:-g++}
CC=${CC:-gcc}
WARN=${WARN:--Wall -Wextra}
CXXFLAGS=${CXXFLAGS:--O3 -march=native -std=c++17 -fopenmp -funroll-loops $WARN}
CFLAGS=${CFLAGS:--O3 -march=native -std=c11 $WARN}

PY=$(command -v pypy3 || command -v python3)
check_prime() {
  "$PY" - "$1" <<'PYEOF'
import sys
n = int(sys.argv[1])
if n < 2:
    raise SystemExit(f"{n} is not prime")
if n % 2 == 0 and n != 2:
    raise SystemExit(f"{n} is not prime")
i = 3
while i * i <= n:
    if n % i == 0:
        raise SystemExit(f"{n} is not prime ({i} divides it)")
    i += 2
print(f"prime OK: {n}  (< 2^16: {n < 2**16}, < 2^21: {n < 2**21})")
PYEOF
}

build() {  # build NAME MODP [extra flags...]
  local name=$1 p=$2; shift 2
  echo "=== $name  (P = $p)  $*"
  $CXX $CXXFLAGS -DMODP=${p}ull "$@" "$SRC" -o "$OUT/$name"
}

for p in 65521 65519 2097143 2097133; do check_prime "$p"; done

build gemm_u16_65521    65521
build gemm_u16_65519    65519
build gemm_u32_2097143  2097143
build gemm_u32_2097133  2097133
build gemm_u32_65521    65521   -DSTORE_BITS=32
build gemm_portable_65521 65521 -DNO_NEON

# generic -DMODP build
GENP=${MODP:-65521}
check_prime "$GENP"
build gemm_modp "$GENP"

# ---------------------------------------------------------------- CBLAS path --
# Default: build against the in-tree reference implementation in cblas_stub/,
# which exists purely to exercise the -DUSE_CBLAS code path.  Set
# USE_SYSTEM_CBLAS=1 to link a real BLAS instead (see RUN_ON_LAPTOP.md).
if [ "${USE_SYSTEM_CBLAS:-0}" = "1" ]; then
  CBLAS_INC=""
  for d in /usr/include /usr/include/openblas /usr/local/include \
           /opt/homebrew/opt/openblas/include; do
    if [ -f "$d/cblas.h" ]; then CBLAS_INC="-I$d"; break; fi
  done
  if [ -n "$CBLAS_INC" ]; then
    echo "=== gemm_cblas_65521 (system CBLAS: $CBLAS_INC)"
    $CXX $CXXFLAGS -DMODP=65521ull -DUSE_CBLAS $CBLAS_INC "$SRC" \
         -o "$OUT/gemm_cblas_65521" -lopenblas \
      || echo "!! system CBLAS build failed (library missing?) -- skipped"
  else
    echo "=== USE_SYSTEM_CBLAS=1 but no system cblas.h found -- skipped"
  fi
else
  echo "=== reference CBLAS object (cblas_stub/cblas_ref.c)"
  $CC $CFLAGS -c cblas_stub/cblas_ref.c -o tmp/cblas_ref.o
  for p in 65521 2097143; do
    echo "=== gemm_cblas_$p  (-DUSE_CBLAS against cblas_stub/, reference only)"
    $CXX $CXXFLAGS -DMODP=${p}ull -DUSE_CBLAS -Icblas_stub "$SRC" tmp/cblas_ref.o \
         -o "$OUT/gemm_cblas_$p"
  done
fi

echo "=== built:"
ls -l "$OUT"
