#!/bin/sh
# build.sh -- build sampler, avoid_check, unif_test, brute_avoiders.
#   sh build.sh                 # -O3 -march=native -fopenmp
set -e
DIR=$(cd "$(dirname "$0")" && pwd)
TBL=$DIR
CXX=${CXX:-g++}
ARCHFLAG=${ARCHFLAG:--march=native}
if ! $CXX $ARCHFLAG -x c++ -c /dev/null -o /dev/null 2>/dev/null; then
  ARCHFLAG=-mcpu=native
  if ! $CXX $ARCHFLAG -x c++ -c /dev/null -o /dev/null 2>/dev/null; then ARCHFLAG=""; fi
fi
OMP=-fopenmp
if ! $CXX $OMP -x c++ -c /dev/null -o /dev/null 2>/dev/null; then
  echo "warning: no OpenMP; building single-threaded" >&2; OMP=""
fi
set -x
$CXX -std=c++17 -O3 $ARCHFLAG -funroll-loops $OMP -Wall -Wextra -I"$DIR" -I"$TBL" \
     -o "$DIR/sampler" "$DIR/sampler.cpp"
$CXX -std=c++17 -O2 -Wall -Wextra -I"$DIR" -o "$DIR/avoid_check" "$DIR/avoid_check.cpp"
if [ -f "$DIR/unif_test.cpp" ]; then
  $CXX -std=c++17 -O3 $ARCHFLAG $OMP -Wall -Wextra -I"$DIR" -I"$TBL" \
       -o "$DIR/unif_test" "$DIR/unif_test.cpp"
fi
