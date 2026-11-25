#!/usr/bin/env bash
# Differential check for the dense 3D fast sweeping (Eikonal) solver.
#
# Generates the same seeded 8x8x8 random grids on both sides (same LCG, same
# value mapping u/100000-0.5), runs tvdb_fast_sweeping with frozen_band=0.25,
# voxel_size=0.25, max_iters=10, tol=1e-6, and compares the FINAL grids
# voxel by voxel: exact sign identity and |diff| <= 1e-5 * h.
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
tmp=$(mktemp -d "${TMPDIR:-/tmp}/fastsweep.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/fastsweep_c.c" \
  "$root/src/tinyvdb_ops.c" "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/fastsweep_c"

lake -d "$here" build fastsweepcheck

"$tmp/fastsweep_c" > "$tmp/c.txt"
out="$("$here/.lake/build/bin/fastsweepcheck" "$tmp/c.txt")"
echo "$out"
case "$out" in
  *voxel-lines=102400*) ;;
  *) echo "FAIL: expected 102400 voxel comparisons, got: $out" >&2; exit 1;;
esac
echo "OK fastsweep: 200 cases x 512 voxels match (1e-5*h abs, exact sign)"
