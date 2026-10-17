#!/bin/bash
# Record the peak resident memory (VmHWM, kB) of every locG process, one line
# per process when it ends; usage: memmon.sh outfile (runs until killed).
out=$1; declare -A hw cmd
while true; do
  for p in $(pgrep -x locG); do
    h=$(awk '/VmHWM/{print $2}' /proc/$p/status 2>/dev/null); [ -n "$h" ] || continue
    hw[$p]=$h; cmd[$p]=$(tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null)
  done
  for p in "${!hw[@]}"; do
    if ! kill -0 $p 2>/dev/null; then echo "${cmd[$p]} VmHWM_kB=${hw[$p]}" >> $out; unset hw[$p] cmd[$p]; fi
  done
  sleep 20
done
