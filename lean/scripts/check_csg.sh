#!/usr/bin/env bash
# Differential check for the dense CSG ops (union/intersection/difference).
#
# Generates the same seeded 8x8x8 random grids on both sides (same LCG, same
# value mapping, tie/zero/NaN injection) and compares float bit patterns of
# every voxel: C (real tvdb_csg_*, scripts/csg_c.c) vs the Lean Float32 twin
# (Vdb.CsgCheck, comparison-ternary form). Bit-exact comparison, no tolerance.
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
tmp=$(mktemp -d "${TMPDIR:-/tmp}/csgcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/csg_c.c" \
  "$root/src/tinyvdb_ops.c" "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/csg_c"

lake -d "$here" build csgcheck

"$tmp/csg_c" > "$tmp/c.txt"
out="$("$here/.lake/build/bin/csgcheck" "$tmp/c.txt")"
echo "$out"
case "$out" in
  *cases=400*voxels=614400*bad=0*) ;;
  *) echo "FAIL: expected cases=400 ops=3 voxels=614400 bad=0, got: $out" >&2; exit 1;;
esac
echo "OK csg: 400 seeded grids x 3 ops x 512 voxels bit-exact"
