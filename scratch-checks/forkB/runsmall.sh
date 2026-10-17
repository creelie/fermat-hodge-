#!/bin/sh
cd /dev/shm/tmpb/forkB || exit 1
export TMPDIR=/dev/shm/tmpb
for p in 5 7 11 13 17 19; do
  python3 levelchain.py 72 $p 2 lchain /dev/shm/tmpb/m6/L_3_2_$p.txt > LC_3_2_$p.txt 2>&1
done
python3 levelchain.py 72 23 2 lchain L_3_2_23.txt > LC_3_2_23.txt 2>&1
echo smalldone >> run.log
