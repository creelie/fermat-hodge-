#!/bin/bash
cd /dev/shm/tmpb/glob || exit 1
> s35.txt
while read D n colon rest; do
  [ "$n" = 6 ] && continue
  for a in 1 2 3 4 5 6; do for b in 1 2 3 4; do
    M=$(( 35 * 2**a * 3**b ))
    echo "B $D $n : $rest  M=$M" >> s35.txt
    ./single $M 35 $D $rest >> s35.txt
  done; done
done < residuals_35.txt
echo run35 done >> s35.txt
