#!/bin/sh
# Sequential (one core): local configurations at D = 2^v 3^w for e', then the
# top-move statistics and the local chains of the configurations with 2-part >= 16
# or 3-part >= 27.
cd /dev/shm/tmpb/forkA
ulimit -v 3100000
: > out/progress.txt
while read e v w kp; do
  f=out/L_${v}_${w}_${e}.txt
  python3 timed.py $f out/L_${v}_${w}_${e}.err ./locDK $e $v $w 6 $kp
  python3 topmoves.py $f 4 > out/T_${v}_${w}_${e}.txt 2>&1
  python3 chains.py $f 4 3 3 > out/A_${v}_${w}_${e}.txt 2>&1
  echo "$e $v $w done $(tail -1 out/L_${v}_${w}_${e}.err) nochain=$(grep -c 'NO CHAIN' out/A_${v}_${w}_${e}.txt)" >> out/progress.txt
done <<LIST
5 5 1 1
7 5 1 1
5 4 2 1
5 3 3 2
7 4 2 2
35 4 1 4
35 1 3 4
11 5 1 2
13 5 1 4
7 3 3 4
11 4 2 8
13 4 2 16
5 1 5 16
11 3 3 32
13 3 3 32
7 1 5 64
11 1 5 256
LIST
echo ALLDONE >> out/progress.txt
