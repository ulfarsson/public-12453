#!/bin/sh
# build_all.sh -- build every table the validation of SCALING_BRIEF.md needs.
#
#   sh build_all.sh            # N = 40, 60, 100, 150 (scaled + unscaled), 200 scaled
#   sh build_all.sh 250        # add the N = 250 scaled table (56 min on 8 threads, 2.6 GB)
#   THREADS=8 sh build_all.sh
set -e
DIR=$(cd "$(dirname "$0")" && pwd)
cd "$DIR"
T=${THREADS:-8}
mkdir -p logs
sh build_tables.sh
for N in 40 60 100 150; do
  ./tables --N $N --threads $T          --out N${N}u.avr 2>&1 | tee logs/build_N${N}u.log
  ./tables --N $N --threads $T --scaled --out N${N}s.avr 2>&1 | tee logs/build_N${N}s.log
done
./tables --N 200 --threads $T --scaled --out N200s.avr 2>&1 | tee logs/build_N200s.log
for N in "$@"; do
  ./tables --N $N --threads $T --scaled --out N${N}s.avr 2>&1 | tee logs/build_N${N}s.log
done
