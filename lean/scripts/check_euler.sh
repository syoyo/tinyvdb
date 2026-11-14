#!/usr/bin/env bash
# Differential check for the Euler characteristic of the dense SDF solid.
#
# Generates the same seeded 5x5x5 random grids on both sides (same LCG,
# same value mapping u/100000-0.5, isovalue 0). The C driver prints the
# tvdb_level_set_euler_characteristic return value (2 * chi(solid));
# the Lean exe prints chi(solid) directly with Vdb.chiOf. Every case must
# satisfy c == 2 * lean.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/eulercheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/euler_c.c" \
  "$root/src/tinyvdb_levelset.c" "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_ops.c" "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_poisson.c" \
  "$root/src/tinyvdb_sample.c" "$root/src/tinyvdb_thread.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/euler_c"

lake -d "$here" build eulercheck

"$tmp/euler_c" > "$tmp/c.txt"
"$here/.lake/build/bin/eulercheck" > "$tmp/lean.txt"

python3 - "$tmp/c.txt" "$tmp/lean.txt" <<'PY'
import sys
bad = 0
with open(sys.argv[1]) as fa, open(sys.argv[2]) as fb:
    for i, (la, lb) in enumerate(zip(fa, fb), 1):
        _, ci, cval = la.split()
        _, ii, lval = lb.split()
        cidx, cval = ci, float(cval)
        lidx, lval = ii, int(lval)
        if cidx != lidx or abs(cval - 2 * lval) > 0.5:
            bad += 1
            if bad <= 5:
                print(f"MISMATCH case {cidx}: c={cb} lean={lval} (expected 2x={2 * lval})")
    if fa.readline() or fb.readline():
        print("MISMATCH: different line counts"); bad += 1
print(f"bad={bad}")
sys.exit(1 if bad else 0)
PY
echo "OK eulercheck: 400 cases match (c == 2 * chi)"
