#!/usr/bin/env bash
# Differential check for the sparse/tree mesh→level-set arm (VS-1, first
# slice): tvdb_mesh_to_level_set in src/tinyvdb_sparse_tools.c.
#
# treemeshsdf_c.c builds two closed meshes (cube, octahedron), runs the real
# C tree API and dumps the generated mesh, the options, the result counters,
# grid topology and the stored (active, Float32 bit pattern) on a fixed 9^3
# index lattice. The Lean bounded twin (Vdb.TreeMeshSdfCheck) recomputes, in
# exact Rat arithmetic from the dumped mesh alone, the final clamped signed
# distance and active flag at every sampled voxel and compares them.
#
# MIRRORED: unsigned closest-triangle distance (exact ℚ), inside/outside sign
# (exact ray parity, orientation independent like C's |winding| > 1/2), the
# ±band clamp (signedFill_eq_clamp) and the keep-rule active predicate; plus
# a topology cross-check that the dumped active count equals the grid's
# reported active voxels and that the background equals exterior_width.
#
# MIRRORED SEED STAGE: the C harness additionally exposes the barycentric seed
# generator's intermediate output (per-face `steps = ceil(2 l / h)` and the
# unique snapped seed voxels). The twin recomputes the whole loop in native
# IEEE-754 doubles, in the C operation order, and compares the per-face counts
# and the seed set bit-exactly (badSeed / badSteps counters).
#
# NOT MIRRORED (loudly reported by the twin's stages_unmirrored line):
# 6-neighbour dilation, BVH traversal and its Float32 closest point kernel /
# double hypot, winding-number evaluation, flood fill reachability, tree
# construction/prune and the tree_find layout. Values are therefore compared
# with a documented 1e-6 relative tolerance (C rounds a double distance to
# Float32); active flags and the seed set are compared exactly.
#
# Negative controls: corrupting one dumped value bit pattern makes the twin
# report badValue>0; corrupting one dumped seed coordinate makes it report
# badSeed>0. Both must exit non-zero; the script asserts both failures.
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
tmp=$(mktemp -d "${TMPDIR:-/tmp}/treemeshsdfcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/treemeshsdf_c.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_winding.c" \
  "$root/src/tinyvdb_tree.c" "$root/src/tinyvdb_sparse_tools.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/tinyvdb_lifecycle.c" \
  "$root/src/tinyvdb_volume.c" "$root/src/tinyvdb_sparse_tree.c" \
  "$root/src/tinyvdb_sparse.c" "$root/src/tinyvdb_stats.c" \
  "$root/src/tinyvdb_sdf_tree.c" "$root/src/tvdb_memory.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/treemeshsdf_c"

"$tmp/treemeshsdf_c" > "$tmp/c.txt"

# Executable harness: no proof group, so no `lake build Vdb.X` target and no
# lakefile change is needed. `lean --run` typechecks and runs the file with
# the package's import path; the 600 s cap is the plan's per-group budget.
twin() { timeout 600 lake -d "$here" env lean --run "$here/Vdb/TreeMeshSdfCheck.lean" "$1"; }

out="$(twin "$tmp/c.txt")"
echo "$out"
case "$out" in
  *"meshes=2 voxels=1458 badValue=0 badActive=0 badTopo=0"*"seeds=196 badSeed=0 badSteps=0"*"stages_unmirrored=dilate,bvh,winding,floodfill,prune,tree-layout"*) ;;
  *) echo "FAIL: expected meshes=2 voxels=1458 badValue=0 badActive=0 badTopo=0, seeds=196 badSeed=0 badSteps=0 and the unmirrored-stage banner" >&2; exit 1;;
esac

# Negative control: corrupt the first dumped voxel's value bits. The twin
# must detect it (badValue>=1) and fail; a silent pass would be a broken gate.
awk 'BEGIN{done=0} /^mesh [0-9]+ voxel / && !done {$NF="00000000"; done=1} {print}' \
  "$tmp/c.txt" > "$tmp/corrupt.txt"
if twin "$tmp/corrupt.txt" > "$tmp/neg.txt" 2>&1; then
  echo "FAIL: negative control passed (corrupted voxel not detected)" >&2
  cat "$tmp/neg.txt" >&2
  exit 1
fi
grep -q 'badValue=[1-9]' "$tmp/neg.txt" || {
  echo "FAIL: negative control did not report badValue>0" >&2
  cat "$tmp/neg.txt" >&2
  exit 1
}

# Second negative control: corrupt one dumped seed coordinate. The mirrored
# seed generator must detect the wrong seed set (badSeed>0) and fail.
awk 'BEGIN{done=0} /^mesh [0-9]+ seed / && !done {$NF="999"; done=1} {print}' \
  "$tmp/c.txt" > "$tmp/corrupt_seed.txt"
if twin "$tmp/corrupt_seed.txt" > "$tmp/neg_seed.txt" 2>&1; then
  echo "FAIL: seed negative control passed (corrupted seed not detected)" >&2
  cat "$tmp/neg_seed.txt" >&2
  exit 1
fi
grep -q 'badSeed=[1-9]' "$tmp/neg_seed.txt" || {
  echo "FAIL: seed negative control did not report badSeed>0" >&2
  cat "$tmp/neg_seed.txt" >&2
  exit 1
}
echo "OK treemeshsdf: 2 closed meshes x 729 voxels, mirrored seed generation (196 seeds), value/topology differential + two negative controls"
