#!/bin/sh
# bench_speed.sh -- samples/s with the scaled tables, for planning the n = 300 run.
set -e
DIR=$(cd "$(dirname "$0")" && pwd); cd "$DIR"
SEED=20260903
for spec in "100 N150s.avr 40000" "150 N150s.avr 20000" "200 N200s.avr 8000"; do
  set -- $spec; n=$1; T=$2; C=$3
  [ -f "$T" ] || continue
  for th in 1 4 8; do
    c=$C
    [ $th = 1 ] && c=$((C/4))
    printf "n=%3d threads=%d  " $n $th
    /usr/bin/time -f "%M" ./sampler --table $T --n $n --count $c --seed $SEED \
        --threads $th --no-avoid --quiet --out /dev/null 2>&1 >/dev/null \
      | tr '\n' ' ' > /tmp/rss.$$ || true
    ./sampler --table $T --n $n --count $c --seed $SEED --threads $th --no-avoid --out /dev/null 2>&1 \
      | awk -v th=$th '/samples\/s/{for(i=1;i<=NF;i++) if($i=="samples/s"){printf "%s samples/s   %.3f ms per sample per thread\n", $(i-1), th*1000/$(i-1)}}'
  done
done
