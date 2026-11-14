#!/usr/bin/env bash
# Differential check for the Godunov local solver.
#
# Generates the same 200,000 seeded pseudo-random sorted triples on both
# sides (same LCG, same value mapping, same insertion sort). The C driver
# (scripts/godunov_c.c) prints "i a b c h out" with %.17e; the Lean exe
# (Vdb.GodunovCheck) re-parses the C output, recomputes the solver on the
# parsed inputs, and reports any case violating
# |a-b| <= max(1e-12, 1e-12 * max(|a|, |b|)).
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/godunov.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 "$here/scripts/godunov_c.c" -lm -o "$tmp/godunov_c"

lake -d "$here" build godunovcheck

"$tmp/godunov_c" > "$tmp/c.txt"
"$here/.lake/build/bin/godunovcheck" "$tmp/c.txt"
echo "OK godunov: 200000 cases match (1e-12)"
