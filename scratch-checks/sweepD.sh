#!/bin/sh
# usage: sweepD.sh v w primes...
cd /dev/shm/tmpb/m6
v=$1; w=$2; shift 2
for p in "$@"; do echo $p; done | xargs -P 4 -I{} sh -c "./locD {} $v $w > L_${v}_${w}_{}.txt 2> L_${v}_${w}_{}.err"
echo "sweep $v $w done" >> sweep.log
