#!/bin/sh
cd /dev/shm/tmpb/forkB || exit 1
./locDm 23 3 2 8 > L_3_2_23.txt 2> L_3_2_23.err
echo done23 >> run.log
