#!/bin/sh
cd /dev/shm/loc
mkdir -p fm
for M in $(seq 4 2 400); do echo $M; done | xargs -P 4 -I{} sh -c './fullmove {} 4 12 > fm/F{}.txt 2>> fm/err.txt'
echo done > fm/done
