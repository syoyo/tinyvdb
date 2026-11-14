#!/usr/bin/env bash
# Differential check for the dense mesh→SDF arm (tvdb_mesh_to_sdf_ex):
#
# Generates three closed meshes (cube, icosahedron, jittered icosahedron)
# and the dense signed-distance grids the real C API produces
# (scripts/meshsdf_c.c), dumped as float bit patterns. The Lean Float32 twin
# (Vdb.MeshSdfCheck) recomputes every voxel from the dumped mesh alone —
# brute-force closest triangle (lowest-face-index tie-break, same acceptance
# rule the BVH preserves), closest-feature pseudo-normal sign
# (Bærentzen & Aanæs) — and compares bits, bit-exact.
#
# Not mirrored: the C double-precision closest-point fallback
# (mesh_triangle_double), which needs double→float32 rounding that core Lean
# lacks. The twin detects every branch into it as a Float32 predicate and
# counts it in fallback_hits; the gate asserts fallback_hits=0 (unreachable
# for these meshes — finite, non-degenerate geometry).
#
# Negative control: corrupting a single voxel's bit pattern in the dump makes
# the twin report bad=1 and exit 1 (verified during development).
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/meshsdfcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/meshsdf_c.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/meshsdf_c"

lake -d "$here" build meshsdfcheck

"$tmp/meshsdf_c" > "$tmp/c.txt"
out="$("$here/.lake/build/bin/meshsdfcheck" "$tmp/c.txt")"
echo "$out"
case "$out" in
  *voxels=6488*bad=0*fallback_hits=0*) ;;
  *) echo "FAIL: expected voxels=6488 bad=0 fallback_hits=0, got: $out" >&2; exit 1;;
esac
echo "OK meshsdf: 3 closed meshes x 6488 voxels bit-exact (mesh→SDF differential)"
