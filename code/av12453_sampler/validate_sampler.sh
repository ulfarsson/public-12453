#!/bin/sh
# validate.sh -- the full validation suite of SAMPLER_BRIEF.md, section
# "Validation of the sampler".  Usage:  sh validate.sh [WORKDIR]
# Writes its sample files into WORKDIR (default: ./_val), which may be large.
set -e
DIR=$(cd "$(dirname "$0")" && pwd)
TBL=$DIR
W=${1:-$DIR/_val}
mkdir -p "$W"
cd "$DIR"
SEED=20260903

echo "=============================================================="
echo "(0) determinism: --threads 1 and --threads 4 must agree exactly"
echo "=============================================================="
./sampler --table $TBL/N100.avr --n 100 --count 3000 --seed $SEED --threads 1 --quiet --out "$W/d1.txt"
./sampler --table $TBL/N100.avr --n 100 --count 3000 --seed $SEED --threads 4 --quiet --out "$W/d4.txt"
if cmp -s "$W/d1.txt" "$W/d4.txt"; then echo "PASS: identical output"; else echo "FAIL"; exit 1; fi

echo
echo "=============================================================="
echo "(1) avoidance at n = 7, 8, 12, 50, 100, 150"
echo "=============================================================="
for n in 7 8 12 50 100 150; do
  case $n in 7|8|12) T=$TBL/N40.avr; C=200000; B=--brute ;;
             50)     T=$TBL/N60.avr;  C=200000; B= ;;
             100)    T=$TBL/N100.avr; C=100000; B= ;;
             150)    T=$TBL/N150.avr; C=100000; B= ;; esac
  echo "--- n = $n, $C samples (table $(basename $T))"
  ./sampler --table $T --n $n --count $C --seed $SEED --threads 4 --out "$W/av$n.txt" 2>&1 | sed 's/^/    /'
  ./avoid_check $B "$W/av$n.txt" | sed 's/^/    /'
  echo "    distinct permutations sampled: $(sort -u "$W/av$n.txt" | wc -l)"
  rm -f "$W/av$n.txt"
done

echo
echo "=============================================================="
echo "(2) exact uniformity at n = 7 and n = 8 (chi-square)"
echo "=============================================================="
./unif_test --table $TBL/N40.avr --n 7 --seed $SEED --threads 4
echo
./unif_test --table $TBL/N40.avr --n 8 --seed $SEED --threads 4

echo
echo "=============================================================="
echo "(3) first-letter distribution at n = 100 and n = 150, 100000 samples"
echo "=============================================================="
for n in 100 150; do
  T=$TBL/N$n.avr
  ./sampler --table $T --n $n --count 100000 --seed $SEED --threads 4 --quiet --out "$W/f$n.txt"
  pypy3 firstletter_test.py --table $T --n $n --in "$W/f$n.txt" 2>/dev/null || \
    python3 firstletter_test.py --table $T --n $n --in "$W/f$n.txt"
  rm -f "$W/f$n.txt"
  echo
done

echo "=============================================================="
echo "(4) --check (weight-sum assertions) at n = 100, 100 samples"
echo "=============================================================="
./sampler --table $TBL/N100.avr --n 100 --count 100 --seed $SEED --threads 1 --check --stats --out /dev/null
echo "--- also at n = 150, 100 samples"
./sampler --table $TBL/N150.avr --n 150 --count 100 --seed $SEED --threads 1 --check --stats --out /dev/null
echo "--- also at n = 12, 20000 samples"
./sampler --table $TBL/N40.avr --n 12 --count 20000 --seed $SEED --threads 4 --check --out /dev/null

echo
echo "=============================================================="
echo "(5) speed: samples/s at n = 50, 100, 150; 1 and 4 threads"
echo "=============================================================="
for n in 50 100 150; do
  case $n in 50) T=$TBL/N60.avr; C=20000 ;; 100) T=$TBL/N100.avr; C=20000 ;; 150) T=$TBL/N150.avr; C=20000 ;; esac
  for th in 1 4; do
    echo "--- n=$n threads=$th (with the mandatory avoidance check on every sample)"
    ./sampler --table $T --n $n --count $C --seed $SEED --threads $th --out /dev/null 2>&1 | grep samples/s | sed 's/^/    /'
    echo "--- n=$n threads=$th (--no-avoid, raw sampling speed)"
    ./sampler --table $T --n $n --count $C --seed $SEED --threads $th --no-avoid --out /dev/null 2>&1 | grep samples/s | sed 's/^/    /'
  done
done
rm -f "$W/d1.txt" "$W/d4.txt"
echo
echo "validation finished"
