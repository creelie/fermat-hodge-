#!/bin/sh
cd /dev/shm/loc
for es in $(seq 5 2 301); do [ $((es % 3)) -ne 0 ] && echo $es; done | xargs -P 3 -I{} sh -c './loc3 {} > D{}.txt 2> D{}.err'
echo done > run3.done
