#!/bin/bash
# usage: scan.sh M
cd /dev/shm/hc
M=$1
[ -f l$M.txt ] || ./lev1 $M 0 > l$M.txt 2>/dev/null
timeout 5000 python3 pairs2.py l$M.txt $M > s$M.pairs 2>&1
timeout 5000 python3 cpairs2.py l$M.txt $M > s$M.curve 2>&1
echo "M=$M pairs: $(tail -n1 s$M.pairs) | curve: $(tail -n1 s$M.curve)" >> scan.log
