#!/usr/bin/env bash
# Differential check for voxel DDA along a ray (PH-4 follow-up).
# The C driver calls the real tvdb_voxels_along_ray_dense; the Lean twin uses
# the exact-rational DDA in Vdb/RayDda. Voxel sequences are compared exactly.
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/rayddacheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/ray_dda_c.c" "$root/src/tinyvdb_ray.c" \
  "$root/src/tinyvdb_sample.c" "$root/src/tinyvdb_mesh.c" \
  "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_ops.c" "$root/src/tinyvdb_poisson.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/ray_dda_c"

lake -d "$here" build rayddacheck

"$tmp/ray_dda_c" > "$tmp/c.txt"
"$here/.lake/build/bin/rayddacheck" "$tmp/c.txt" > "$tmp/lean.txt"

grep -E '^(out|voxel) ' "$tmp/c.txt" > "$tmp/c.out"
grep -E '^(out|voxel) ' "$tmp/lean.txt" > "$tmp/lean.out"

if ! diff -u "$tmp/c.out" "$tmp/lean.out" > "$tmp/diff.txt"; then
  echo "FAIL: C and Lean ray-DDA voxel sequences disagree" >&2
  head -60 "$tmp/diff.txt" >&2
  exit 1
fi

cases=$(grep -c '^case ' "$tmp/c.txt" || true)
voxels=$(grep -c '^voxel ' "$tmp/c.out" || true)
echo "OK ray-dda: cases=$cases voxels=$voxels sequences exact"
