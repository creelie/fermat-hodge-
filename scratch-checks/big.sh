#!/bin/sh
cd /dev/shm/loc
for es in 175 275 325 385 425 455 475 539 595 605 637 665 715 805 845 935 1001 1225; do echo $es; done | xargs -P 3 -I{} sh -c 'timeout 3000 ./loc3 {} > D{}.txt 2> D{}.err'
echo done > big.done
