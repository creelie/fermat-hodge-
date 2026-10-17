#!/bin/sh
# Resumable, sequential (one core) version of runall.sh: each job "e v w kp chunk"
# runs locDK2 over the passes [p, p+chunk) one chunk at a time, appending to
# out/P_v_w_e.txt; a marker file records each finished chunk, so a killed run
# resumes where it stopped.  After the last chunk the canonical forms are
# deduplicated into out/L_v_w_e.txt and topmoves.py / chains.py are run.
cd /dev/shm/tmpb/forkA
ulimit -v 3100000
while read e v w kp ch; do
  b=${v}_${w}_${e}; p=0
  while [ $p -lt $kp ]; do
    if [ ! -e out/done_${b}_$p ]; then
      ./locDK2 $e $v $w 6 $kp $p $((p+ch)) >> out/P_$b.txt 2>> out/P_$b.err || { echo "$e $v $w chunk $p FAILED" >> out/progress.txt; exit 1; }
      : > out/done_${b}_$p
    fi
    p=$((p+ch))
  done
  if [ ! -e out/merged_$b ]; then
    grep '^C' out/P_$b.txt | sort -u > out/L_$b.txt
    python3 topmoves.py out/L_$b.txt 4 > out/T_$b.txt 2>&1
    python3 chains.py out/L_$b.txt 4 3 3 > out/A_$b.txt 2>&1
    echo "$e $v $w done found=$(grep -c '^C' out/L_$b.txt) nochain=$(grep -c 'NO CHAIN' out/A_$b.txt)" >> out/progress.txt
    : > out/merged_$b
  fi
done <<LIST
13 3 3 32 4
7 1 4 2 1
11 1 4 8 2
13 1 4 16 4
7 1 5 32 4
LIST
echo CHUNKSDONE >> out/progress.txt
