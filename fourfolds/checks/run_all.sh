#!/usr/bin/env bash
# Runs the four independent re-checks of the finite arithmetic and the Lean
# certificate. Usage: bash run_all.sh   (from any directory)
set -eu
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
echo "== Python";  python3 "$here/finite.py"
echo "== C";       cc -O2 -o "$tmp/finite_c" "$here/finite.c" && "$tmp/finite_c"
echo "== C++";     c++ -O2 -std=c++17 -o "$tmp/finite_cpp" "$here/finite.cpp" && "$tmp/finite_cpp"
echo "== shell";   bash "$here/finite.sh"
if command -v lean >/dev/null 2>&1; then
	echo "== Lean"
	(cd "$here/../lean" && lean FermatFourfolds.lean)
else
	echo "== Lean not found; skipped"
fi
