#!/usr/bin/env bash
# Independent re-check in bash arithmetic of part of the finite arithmetic
# certified in lean/FermatFourfolds.lean: the balanced multisets, the angle
# tables of the five character pairs, the block patterns, the parity of
# nu at level 110 and the first open degrees.
set -u
pass=0
fail=0
ok() { if [ "$2" = 1 ]; then pass=$((pass + 1)); else fail=$((fail + 1)); echo "FAIL $1"; fi; }

gcd() { local a=$1 b=$2 r; while [ "$b" -ne 0 ]; do r=$((a % b)); a=$b; b=$r; done; echo "$a"; }

# balanced M a1 a2 ...
balanced() {
	local M=$1; shift
	local n=$# s=0 a t h
	for a in "$@"; do
		[ $((a % M)) -eq 0 ] && { echo 0; return; }
		s=$((s + a))
	done
	[ $((s % M)) -ne 0 ] && { echo 0; return; }
	for ((t = 1; t < M; t++)); do
		[ "$(gcd $t $M)" -ne 1 ] && continue
		h=0
		for a in "$@"; do h=$((h + t * a % M)); done
		[ $((2 * h)) -ne $((n * M)) ] && { echo 0; return; }
	done
	echo 1
}

# angles M "a1 a2 ..." : <t a> for the units t < M/2
angles() {
	local M=$1 a=$2 t h x out=""
	for ((t = 1; 2 * t < M; t++)); do
		[ "$(gcd $t $M)" -ne 1 ] && continue
		h=0
		for x in $a; do h=$((h + t * x % M)); done
		out="$out $((h / M))"
	done
	echo $out
}

# Sections 4, 6, 9, 10: balanced multisets
while read -r M rest; do
	ok "balanced $M $rest" "$(balanced $M $rest)"
done <<'EOF'
21 1 4 9 15 16 18
33 1 4 16 22 25 31
39 1 7 16 22 34 37
21 1 4 18 19
66 1 25 44 62
66 2 8 32 44 50 62
78 2 7 73 74
78 2 14 32 44 68 74
28 3 5 13 17 19 27
28 5 6 13 14 19 27
28 1 9 16 17 20 21
114 1 25 39 43 57 63 68 80 92 102
44 1 5 8 9 33 37 41 42
52 1 5 16 17 18 29 37 42 45 50
102 1 7 26 34 51 57 60 85 91 98
35 1 2 16 17 21 22 30 31
30 1 19 25 15
30 1 24 20 15
60 1 49 40 30
15 1 6 13 10
20 1 12 17 10
30 1 7 27 25
60 2 21 57 40
28 1 9 25 21
42 1 24 38 21
42 1 25 37 21
42 1 30 32 21
66 1 25 62 44
78 1 55 61 39
110 19 29 39 55 79 109
EOF

# Section 6: the angle tables
check_angles() {
	local got
	got=$(angles "$1" "$2")
	[ "$got" = "$3" ] && ok "angles $1 $2" 1 || ok "angles $1 $2" 0
}
check_angles 114 "1 25 43 57 102" "2 2 2 2 3 2 2 2 3 3 2 2 3 2 2 3 3 2"
check_angles 114 "39 63 68 80 92" "3 3 3 3 2 3 3 3 2 2 3 3 2 3 3 2 2 3"
check_angles 44 "1 5 8 33 41" "2 2 3 2 2 2 3 3 2 3"
check_angles 44 "9 37 42" "2 2 1 2 2 2 1 1 2 1"
check_angles 52 "1 5 16 37 45" "2 2 2 2 3 2 3 2 3 2 2 3"
check_angles 52 "29 18 42 50 17" "3 3 3 3 2 3 2 3 2 3 3 2"
check_angles 102 "1 7 51 60 85" "2 2 2 2 3 2 2 3 2 2 2 3 2 3 2 3"
check_angles 102 "91 34 26 98 57" "3 3 3 3 2 3 3 2 3 3 3 2 3 2 3 2"
check_angles 35 "1 2 16 21 30" "2 2 2 2 2 3 2 2 2 3 3 3"
check_angles 35 "17 22 31" "2 2 2 2 2 1 2 2 2 1 1 1"

# Section 6: block patterns. Each line: m D a1..a5 | e(5):delta ...
pattern() {
	local m=$1 D=$2; shift 2
	local a=("$1" "$2" "$3" "$4" "$5"); shift 6
	local -a col=(0 0 0 0 0)
	local sd=0 good=1 c e d w k pos zero
	for c in "$@"; do
		e=${c%%:*}; d=${c##*:}
		IFS=, read -r -a ev <<<"$e"
		w=0; pos=0; zero=0
		for k in 0 1 2 3 4; do
			w=$((w + ev[k] * a[k]))
			col[k]=$((col[k] + ev[k] * d))
			[ "${ev[k]}" -gt 0 ] && pos=1
			[ "${ev[k]}" -eq 0 ] && zero=1
		done
		[ $((w % m)) -ne 0 ] || [ $pos -ne 1 ] || [ $zero -ne 1 ] && good=0
		sd=$((sd + d))
	done
	for k in 0 1 2 3 4; do [ "${col[k]}" -ne "$D" ] && good=0; done
	[ $sd -ne $((D + 1)) ] && good=0
	ok "pattern $m ${a[*]}" $good
}
pattern 114 3 51 21 86 14 56 '|' 0,0,1,2,0:1 0,0,2,0,1:1 1,3,0,0,0:1 2,0,0,1,2:1
pattern 114 24 1 25 43 57 102 '|' 3,1,2,0,0:7 0,1,5,0,1:2 0,0,0,2,0:12 1,5,0,0,1:3 0,0,0,0,19:1
pattern 44 11 1 5 8 33 41 '|' 3,0,0,0,1:1 0,0,11,0,0:1 1,1,0,0,2:5 1,2,0,1,0:3 0,0,0,4,0:2
pattern 52 14 1 5 16 37 45 '|' 0,0,0,3,1:4 0,1,1,0,3:1 2,1,0,0,1:7 0,0,13,0,0:1 0,3,0,1,0:2
pattern 52 5 1 6 14 34 49 '|' 0,0,5,1,0:1 3,0,0,0,1:1 2,0,0,3,0:1 0,3,0,1,0:1 0,1,0,0,2:2
pattern 102 6 1 34 44 56 69 '|' 0,0,0,3,2:1 0,0,3,0,4:1 0,3,0,0,0:2 2,0,1,1,0:3
pattern 102 18 5 35 51 96 17 '|' 0,0,0,0,6:2 0,0,0,17,0:1 0,0,2,0,0:9 0,6,0,1,0:1 3,2,0,0,1:6
pattern 35 50 1 2 16 21 30 '|' 0,0,0,5,0:10 1,1,2,0,0:25 1,2,0,0,1:10 3,1,0,0,1:5 0,0,0,0,35:1

# Section 10: nu counts an odd number of entries of A_110
c=0
for y in 19 29 39 55 79 109; do r=$((y % 10)); [ $r -ge 4 ] && [ $r -le 6 ] && c=$((c + 1)); done
ok "nu(A_110) = 1" $((c % 2))

# Section 1: the first open degrees
strip() { local M=$1 p; shift; for p in "$@"; do while [ $((M % p)) -eq 0 ]; do M=$((M / p)); done; done; echo $M; }
primepower() {
	local M=$1 p=2
	[ "$M" -lt 2 ] && { echo 0; return; }
	while [ $((M % p)) -ne 0 ]; do p=$((p + 1)); done
	[ "$(strip $M $p)" -eq 1 ] && echo 1 || echo 0
}
covered() {
	local M=$1
	[ "$M" -le 100 ] || [ $((M % 2)) -eq 1 ] && { echo 1; return; }
	if [ "$M" -le 250 ]; then case $M in 110 | 114 | 220 | 228) ;; *) echo 1; return ;; esac; fi
	[ "$(primepower $M)" = 1 ] && { echo 1; return; }
	[ $((M % 4)) -eq 2 ] && [ "$(primepower $((M / 2)))" = 1 ] && { echo 1; return; }
	[ "$(strip $M 2 3 5 7)" -eq 1 ] && [ $((M % 420)) -ne 0 ] && { echo 1; return; }
	[ "$(strip $M 2 3 11)" -eq 1 ] || [ "$(strip $M 2 3 13)" -eq 1 ] && { echo 1; return; }
	{ [ "$(strip $M 2 3 17)" -eq 1 ] || [ "$(strip $M 2 3 19)" -eq 1 ]; } && [ $((M % 4)) -ne 0 ] &&
		{ echo 1; return; }
	echo 0
}
open=""
for ((M = 1; M <= 266; M++)); do
	[ $((M % 110)) -eq 0 ] && continue
	[ "$(covered $M)" = 0 ] && open="$open $M"
done
[ "$open" = " 228 258 260 266" ] && ok "first open degrees" 1 || ok "first open degrees:$open" 0

echo "$pass checks passed, $fail failed"
[ $fail -eq 0 ]
