#!/bin/sh
cd /dev/shm/hc
for M in $(seq 4 2 520); do [ $((M % 3)) -ne 0 ] && echo $M; done | xargs -P 4 -I{} sh -c './lowmove {} > L{}.txt 2>> lsweep.err'
echo done >> lsweep.err
