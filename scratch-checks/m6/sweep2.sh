#!/bin/bash
cd /dev/shm/tmpb/m6 || exit 1
run() { ./locD "$1" "$2" "$3" > "L_$2_$3_$1.txt" 2> "L_$2_$3_$1.err"; echo "$2 $3 $1 done" >> sweep.log; }
( run 35 2 1; run 35 1 2; run 55 2 1 ) &
( for vw in "3 1" "4 1" "3 2" "1 3" "2 3"; do set -- $vw; run 5 $1 $2; done ) &
( for vw in "3 1" "4 1" "3 2" "1 3"; do set -- $vw; run 7 $1 $2; done ) &
wait
echo "sweep2 all done" >> sweep.log
