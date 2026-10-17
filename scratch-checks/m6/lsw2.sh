#!/bin/bash
cd /dev/shm/tmpb/m6 || exit 1
one() { f=$1; set -- $(echo $f | sed 's/L_\([0-9]*\)_\([0-9]*\)_\([0-9]*\).txt/\1 \2 \3/'); N=$(( 2**$1 * 3**$2 * $3 )); python3 lchain.py $N 2 $f > R_${f#L_} 2>&1; }
export -f one
ls L_*_{11,13,17,19}.txt | xargs -P 4 -I{} bash -c 'one {}'
for e in 11 13 17 19; do for vw in "4 1" "3 2" "1 3"; do set -- $vw; ./locD $e $1 $2 > L_$1_$2_$e.txt 2> L_$1_$2_$e.err; done; done
ls L_4_1_{11,13,17,19}.txt L_3_2_{11,13,17,19}.txt L_1_3_{11,13,17,19}.txt | xargs -P 4 -I{} bash -c 'one {}'
echo lsw2 done
