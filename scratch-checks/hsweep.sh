#!/bin/bash
# move graphs for even levels prime to 3 up to 400
cd /dev/shm/hc
for M in $(seq 4 2 400); do [ $((M % 3)) -ne 0 ] && echo $M; done | xargs -P 4 -I{} sh -c './movesH {} > t{}.txt 2>> hsweep.err'
echo done >> hsweep.err
