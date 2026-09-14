#!/bin/sh
# validate.sh -- build the tables and run every check reported in REPORT.md.
#   sh validate.sh [N ...]        (default: 60 100 150)
set -e
DIR=$(cd "$(dirname "$0")" && pwd)
cd "$DIR"
THREADS=${THREADS:-4}
REF="$(cd "$(dirname "$0")/.." && pwd)/av12453_n300/pyref/ref.py"
TERMS="$(cd "$(dirname "$0")/.." && pwd)/data/av12453_terms_0_300.txt"
LIST=${*:-60 100 150}

sh build_tables.sh

echo "=== (b) exact R check at N = 40 ==============================="
./tables --N 40 --threads "$THREADS" --out N40.avr
[ -f dump40.txt ] || pypy3 "$REF" 40 --dump-r dump40.txt
pypy3 check_r.py N40.avr dump40.txt

for N in $LIST; do
  echo "=== N = $N ===================================================="
  # tables prints its own wall-clock phase timings and peak RSS
  ./tables --N "$N" --threads "$THREADS" --out "N$N.avr"
  ls -l "N$N.avr"
  echo "--- (a) terms check"
  python3 check_terms.py "N$N.avr" --terms "$TERMS" --tol 1e-11
  echo "--- C++/Python index cross-check (40000 probes)"
  ./avr_check "N$N.avr" --probe 987654321 20000 > /tmp/avrp_c.$$
  pypy3 avr_table.py "N$N.avr" --probe 987654321 20000 > /tmp/avrp_p.$$
  cmp /tmp/avrp_c.$$ /tmp/avrp_p.$$ && echo "index cross-check PASS"
  rm -f /tmp/avrp_c.$$ /tmp/avrp_p.$$
done

echo "=== N-independence (bit-identity of shared entries) ==========="
prev=""
for N in 40 $LIST; do
  [ -n "$prev" ] && pypy3 check_prefix.py "N$prev.avr" "N$N.avr"
  prev=$N
done
