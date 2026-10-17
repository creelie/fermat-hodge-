#!/bin/sh
cd /dev/shm/tmpb/forkB || exit 1
export TMPDIR=/dev/shm/tmpb
python3 direct.py Pcand.txt modp > direct.log 2>&1
echo directdone >> run.log
