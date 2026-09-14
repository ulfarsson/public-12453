#!/bin/sh
# build.sh -- build the AVR1 table generator and the C++ reader/checker.
#   sh build.sh                 # default: -O3 -march=native -fopenmp
#   CXX=clang++ sh build.sh
# Produces ./tables and ./avr_check next to this script.
set -e
DIR=$(cd "$(dirname "$0")" && pwd)
CXX=${CXX:-g++}
ARCHFLAG=${ARCHFLAG:--march=native}
if ! $CXX $ARCHFLAG -x c++ -c /dev/null -o /dev/null 2>/dev/null; then
  ARCHFLAG=-mcpu=native
  if ! $CXX $ARCHFLAG -x c++ -c /dev/null -o /dev/null 2>/dev/null; then ARCHFLAG=""; fi
fi
OMP=-fopenmp
if ! $CXX $OMP -x c++ -c /dev/null -o /dev/null 2>/dev/null; then
  echo "warning: no OpenMP found; building single-threaded" >&2; OMP=""
fi
set -x
$CXX -std=c++17 -O3 $ARCHFLAG -funroll-loops $OMP -Wall -Wextra \
     -o "$DIR/tables" "$DIR/tables.cpp"
$CXX -std=c++17 -O2 -Wall -Wextra -o "$DIR/avr_check" "$DIR/avr_check.cpp"
