#!/usr/bin/env bash
# Differential check for the dense signed flood fill.
#
# Generates the same 400 seeded 8x8x8 random grids on both sides (same LCG,
# same value mapping u/100000-0.5, band=0.25) and byte-compares the post-fill
# sign maps ('+' exterior far, '-' interior far, '.' band voxel).
set -euo pipefail

# CTest maps 77 to "skipped", not passed. Skip cleanly if the Lean
# toolchain is absent; a real build/check failure still exits non-77.
if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)

# The package pins its Lean toolchain in lean/lean-toolchain. CTest invokes
# these scripts from the build directory, where elan would otherwise select
# the ambient toolchain (possibly incompatible with the pinned mathlib).
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/fillcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/fill_c.c" \
  "$root/src/tinyvdb_ops.c" "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_thread.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/fill_c"

lake -d "$here" build fillcheck

"$tmp/fill_c" > "$tmp/c.txt"
"$here/.lake/build/bin/fillcheck" > "$tmp/lean.txt"

if cmp -s "$tmp/c.txt" "$tmp/lean.txt"; then
  printf 'OK fillcheck: %s cases identical\n' "$(wc -l < "$tmp/c.txt")"
else
  python3 - "$tmp/c.txt" "$tmp/lean.txt" <<'PY'
import sys
with open(sys.argv[1]) as a, open(sys.argv[2]) as b:
    for i, (la, lb) in enumerate(zip(a, b), 1):
        if la != lb:
            print(f"MISMATCH case {i}:")
            print(f"  c:    {la.rstrip()}")
            print(f"  lean: {lb.rstrip()}")
            sys.exit(1)
    print("MISMATCH after common prefix"); sys.exit(1)
PY
  exit 1
fi
