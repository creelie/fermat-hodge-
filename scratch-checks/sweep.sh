#!/bin/bash
# usage: sweep.sh start step end G
cd /dev/shm/hc
for ((M=$1; M<=$3; M+=$2)); do ./span4g $M $4 >> sw$4.out 2>> sw$4.err; done
