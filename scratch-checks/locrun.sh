#!/bin/sh
cd /dev/shm/loc
for es in 5 7 11 13 17 19 23 25 29 31 35 37 41 43 47 49 53 55 59 61 65 67 71 73 77 79 83 85; do echo $es; done | xargs -P 4 -I{} sh -c './loc2 {} > C{}.txt 2> C{}.err'
echo done > run.done
