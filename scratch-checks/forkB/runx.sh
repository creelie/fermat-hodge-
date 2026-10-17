#!/bin/sh
cd /dev/shm/tmpb/forkB || exit 1
./locDm 29 2 2 2 > L_2_2_29.txt 2> L_2_2_29.err
./prop 2 2 29 > P_2_2_29.txt 2> P_2_2_29.err
python3 cmp.py 1044 P_2_2_29.txt L_2_2_29.txt > X_2_2_29.txt
./locDm 29 3 2 16 > L_3_2_29.txt 2> L_3_2_29.err
python3 cmp.py 2088 modp/P_3_2_29.txt L_3_2_29.txt > X_3_2_29.txt
echo xdone >> run.log
