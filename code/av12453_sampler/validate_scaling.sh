#!/bin/sh
# validate_scaling.sh -- the six mandatory checks of SCALING_BRIEF.md.
#
#   sh validate_scaling.sh [WORKDIR]
#
# Assumes the tables N40u/N40s, N60u/N60s, N100u/N100s, N150u/N150s, N200s
# (and optionally N250s) are already built in this directory; build_all.sh
# builds them.  Every check prints the exact command it runs.
set -e
DIR=$(cd "$(dirname "$0")" && pwd)
cd "$DIR"
W=${1:-$DIR/_val}
mkdir -p "$W"
SEED=20260903
TERMS="$(cd "$(dirname "$0")/.." && pwd)/data/av12453_terms_0_300.txt"
run() { echo "\$ $*"; "$@"; }

echo "=============================================================="
echo "(1) scaled vs unscaled tables: bit-identity after x 2^{2*grade}"
echo "=============================================================="
for N in 60 100 150; do run ./avr_cmp "N${N}u.avr" "N${N}s.avr"; echo; done

echo "=============================================================="
echo "(2) G'_(n,0) * 2^{2n} against the known terms (rel < 1e-11)"
echo "=============================================================="
for T in N150s.avr N200s.avr N250s.avr; do
  [ -f "$T" ] || { echo "(skipped: $T not built)"; continue; }
  run pypy3 check_terms.py "$T" --terms "$TERMS" --tol 1e-11 --top 3
  echo
done

echo "=============================================================="
echo "(3) sampler: scaled vs unscaled N=150 table, same seed"
echo "=============================================================="
for n in 150 100; do
  run ./sampler --table N150u.avr --n $n --count 10000 --seed $SEED --threads 4 --quiet --out "$W/u$n.txt"
  run ./sampler --table N150s.avr --n $n --count 10000 --seed $SEED --threads 4 --quiet --out "$W/s$n.txt"
  if cmp -s "$W/u$n.txt" "$W/s$n.txt"; then
    echo "PASS: byte-identical at n = $n ($(wc -c < "$W/u$n.txt") bytes)"
  else echo "FAIL at n = $n"; exit 1; fi
done
echo "--- weight-sum assertions with the scaled table at n = 150"
run ./sampler --table N150s.avr --n 150 --count 200 --seed $SEED --threads 1 --check --stats --out /dev/null
echo "--- and with the unscaled table, for comparison"
run ./sampler --table N150u.avr --n 150 --count 200 --seed $SEED --threads 1 --check --stats --out /dev/null

echo
echo "=============================================================="
echo "(4) avoidance of every sample + exact chi-square at n = 7, 8"
echo "=============================================================="
for n in 7 8 12 100 150; do
  case $n in 7|8|12) T=N40s.avr; C=100000; B=--brute ;;
             100)    T=N150s.avr; C=50000; B= ;;
             150)    T=N150s.avr; C=20000; B= ;; esac
  echo "--- n = $n, $C samples from the scaled table $T"
  run ./sampler --table $T --n $n --count $C --seed $SEED --threads 4 --out "$W/av$n.txt"
  run ./avoid_check $B "$W/av$n.txt"
  rm -f "$W/av$n.txt"
done
run ./unif_test --table N40s.avr --n 7 --seed $SEED --threads 4
echo
run ./unif_test --table N40s.avr --n 8 --seed $SEED --threads 4

echo
echo "--- reader cross-checks on the scaled tables"
echo "\$ ./avr_check N40s.avr --probe 987654321 20000  |  pypy3 avr_table.py N40s.avr --probe ..."
./avr_check N40s.avr --probe 987654321 20000 > "$W/probe_c.txt"
pypy3 avr_table.py N40s.avr --probe 987654321 20000 2>/dev/null > "$W/probe_p.txt"
cmp "$W/probe_c.txt" "$W/probe_p.txt" && echo "C++/Python index cross-check PASS (40000 probes)"
run pypy3 check_ratios.py N150s.avr N150u.avr --n 150
run pypy3 check_r.py N40s.avr dump40.txt

echo
echo "=============================================================="
echo "(5) --binary output and perms_io.py"
echo "=============================================================="
run ./sampler --table N150s.avr --n 150 --count 1000 --seed $SEED --threads 4 --quiet \
     --out "$W/b150.txt" --binary "$W/b150.bin"
ls -l "$W/b150.txt" "$W/b150.bin"
run pypy3 perms_io.py "$W/b150.bin" --n 150 --count
run pypy3 perms_io.py "$W/b150.txt" --compare "$W/b150.bin" --n 150
run pypy3 perms_io.py "$W/b150.bin" --n 150 --validate
echo "--- round trip: binary -> text must reproduce the text file byte for byte"
run pypy3 perms_io.py "$W/b150.bin" --n 150 --to-text "$W/b150r.txt"
if cmp -s "$W/b150.txt" "$W/b150r.txt"; then echo "PASS: round trip byte-identical"; else echo "FAIL"; exit 1; fi
echo "--- binary only (no --out): 2n bytes per record and no text"
run ./sampler --table N150s.avr --n 150 --count 1000 --seed $SEED --threads 4 --quiet --binary "$W/b2.bin"
cmp "$W/b150.bin" "$W/b2.bin" && echo "PASS: same binary with or without --out"

echo
echo "=============================================================="
echo "(6) speed with the scaled tables, 4 threads"
echo "=============================================================="
for spec in "150 N150s.avr 20000" "200 N200s.avr 8000"; do
  set -- $spec
  n=$1; T=$2; C=$3
  [ -f "$T" ] || { echo "(skipped: $T not built)"; continue; }
  echo "--- n=$n, table $T, $C samples"
  run ./sampler --table $T --n $n --count $C --seed $SEED --threads 4 --no-avoid --out /dev/null 2>&1 | grep -E "samples/s"
  echo "    (with the avoidance check on every sample)"
  ./sampler --table $T --n $n --count $C --seed $SEED --threads 4 --out /dev/null 2>&1 | grep -E "samples/s|avoidance"
  echo "    (single thread)"
  ./sampler --table $T --n $n --count $((C/4)) --seed $SEED --threads 1 --no-avoid --out /dev/null 2>&1 | grep -E "samples/s"
done
echo
echo "validate_scaling finished"
