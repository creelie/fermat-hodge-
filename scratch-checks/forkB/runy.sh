#!/bin/sh
# Cross-checks at the non-exceptional primes 541 and 739 (the two least primes
# >= 29 outside P_cand), run after runx.sh; one process at a time.
cd /dev/shm/tmpb/forkB || exit 1
export TMPDIR=/dev/shm/tmpb
while ! grep -q xdone run.log; do tail --pid="$1" -f /dev/null 2>/dev/null || break; done
for L in 6 12 24; do python3 chainprimes.py $L fdump/F_3_2.txt.L$L.out; done > CP.txt 2>&1
for p in 541 739; do
  for vw in "1 1" "2 1" "3 1"; do
    set -- $vw; V=$1; W=$2; case "$V$W" in 11) D=6;; 21) D=12;; 31) D=24;; esac; N=$((D*p))
    [ $p = 739 ] && [ $V = 3 ] && continue
    ./prop $V $W $p > Y/Q_${V}_${W}_$p.txt 2> Y/Q_${V}_${W}_$p.err
    python3 specialize.py $D $p F_${V}_${W}.txt Y/Q_${V}_${W}_$p.txt > Y/S_${V}_${W}_$p.txt 2>&1
    ./prop $V $W $p 5 > Y/Q5_${V}_${W}_$p.txt 2> Y/Q5_${V}_${W}_$p.err
    K=1; [ $V = 3 ] && K=4
    ./locDm $p $V $W $K 5 > Y/M5_${V}_${W}_$p.txt 2> Y/M5_${V}_${W}_$p.err
    python3 cmp.py $N Y/Q5_${V}_${W}_$p.txt Y/M5_${V}_${W}_$p.txt > Y/X5_${V}_${W}_$p.txt 2>&1
    echo "y $p $V $W" >> run.log
  done
done
echo ydone >> run.log
