#!/bin/bash
cd /dev/shm/tmpb/m6 || exit 1
one() { f=$1; set -- $(echo $f | sed 's/L_\([0-9]*\)_\([0-9]*\)_\([0-9]*\).txt/\1 \2 \3/'); N=$(( 2**$1 * 3**$2 * $3 )); python3 lchain.py $N 2 $f > R_${f#L_} 2>&1; }
export -f one
ls L_*_5.txt L_*_7.txt L_*_35.txt L_*_55.txt | xargs -P 4 -I{} bash -c 'one {}'
echo lsw done
