#!/usr/bin/env bash
# Sparse/tree marching-cubes TOPOLOGY differential gate (tier 3).
#
# Compares the REAL C `tvdb_grid_volume_to_mesh` (tool_surface_cells + tool_mesh,
# scripts/mc_sparse_topology_c.c) against the independent exact-Q twin
# Vdb.McSparseTopologyCheck:
#
#   MIRRORED:  case mask from decoded Float32 samples; used cube edges and
#              triangles from Vdb.McTable (T-MC-EDGE / T-MC-COMPLETE / F10);
#              welded keys as lower-lattice-corner + axis (the sparse analogue
#              of Vdb.GridEdge.key, T-MC-WELD); first-appearance vertex ids and
#              exact-Q interpolation mapped by the dumped grid transform;
#              determinant-derived winding flip.
#   NOT MIRRORED (printed by the twin, never counted as a pass): the region
#              collect walk, owner-side classification, the x-slab ring cache
#              and open-addressed slots, count-then-emit allocation, tool_adapt
#              (adapt = 0 here), and the C's double-precision interpolation
#              (twin uses exact rationals, so positions are compared with an
#              explicit Float32 tolerance).
#
# Corpus (2 fields): one analytic sphere on a 16^3 index tree (~380 stored
# voxels), with an isotropic and a y-stretched transform. NOT covered:
# large trees, tile boundaries on the surface, NaN/Inf paths, exact-iso
# samples, adaptive clustering, winding beyond the determinant flip.
#
# Negative controls: corrupting one vertex bit must give bad_pos>0 and a
# non-zero exit; corrupting one face index must give bad_topo>0 with a
# non-zero exit (both verified below).
#
# CTest maps 77 to "skipped", not passed: skip cleanly when lake is absent;
# a real build/check failure still exits non-77.
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)

# CTest invokes this script from the build directory, where elan would
# otherwise select the ambient toolchain and corrupt the mathlib cache. Pin
# the package's toolchain and cd into lean/ for the lake calls.
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/mcsparsetopology.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/mc_sparse_topology_c.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_winding.c" \
  "$root/src/tinyvdb_tree.c" "$root/src/tinyvdb_sparse_tools.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/tinyvdb_lifecycle.c" \
  "$root/src/tinyvdb_volume.c" "$root/src/tinyvdb_sparse_tree.c" \
  "$root/src/tinyvdb_sparse.c" "$root/src/tinyvdb_stats.c" \
  "$root/src/tinyvdb_sdf_tree.c" "$root/src/tvdb_memory.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/mc_sparse_topology_c"

# Hard 600 s cap per group (this module compiles in seconds here).
(cd "$here" && timeout 600 lake build Vdb.McSparseTopologyCheck)

# Preferred: the registered lean_exe target (root Vdb.McSparseTopologyCheck).
# Until registration lands, fall back loudly to running the module directly.
if (cd "$here" && timeout 600 lake build mcsparsetopocheck >/dev/null 2>&1); then
  twin="$here/.lake/build/bin/mcsparsetopocheck"
  run_twin() { timeout 600 "$twin" "$1"; }
else
  echo "NOTE: lean_exe target 'mcsparsetopocheck' is not registered yet; using 'lake env lean --run' fallback"
  run_twin() { (cd "$here" && timeout 600 lake env lean --run Vdb/McSparseTopologyCheck.lean "$1"); }
fi

"$tmp/mc_sparse_topology_c" > "$tmp/c.txt"
out=$(run_twin "$tmp/c.txt")
echo "$out"

cnt() { printf '%s\n' "$out" | grep -o "$1=[0-9]*" | head -1 | cut -d= -f2; }
pass=0
check() {
  local label=$1 got=$2 want=$3
  if [ "$got" = "$want" ]; then
    echo "PASS: $label ($got)"; pass=$((pass + 1))
  else
    echo "FAIL: $label: expected $want, got $got" >&2; exit 1
  fi
}

# Pin the full deterministic corpus so a silently dropped dump line fails.
check "fields"       "$(cnt fields)"       2
check "verts"        "$(cnt verts)"        720
check "faces"        "$(cnt faces)"        1432
check "exact_pos"    "$(cnt exact_pos)"    720
check "bad_count"    "$(cnt bad_count)"    0
check "bad_key"      "$(cnt bad_key)"      0
check "bad_topo"     "$(cnt bad_topo)"     0
check "bad_pos"      "$(cnt bad_pos)"      0
check "bad_flip"     "$(cnt bad_flip)"     0

if printf '%s\n' "$out" | grep -q '^stages_unmirrored=region-collect,owner-classify,x-slab-cache,count-emit,tool-adapt,double-intermediate$'; then
  echo "PASS: unmirrored stages reported"; pass=$((pass + 1))
else
  echo "FAIL: unmirrored stages banner missing" >&2; exit 1
fi

# Negative control 1: flip one output vertex position bit (keep its welded
# key); the position must disagree.
awk '$1=="vertex" && $2=="0" && $3=="0" { $4="00000000" } {print}' \
  "$tmp/c.txt" > "$tmp/neg_pos.txt"
if cmp -s "$tmp/c.txt" "$tmp/neg_pos.txt"; then
  echo "FAIL: position negative control did not modify the dump" >&2; exit 1
fi
set +e
neg=$(run_twin "$tmp/neg_pos.txt" 2>&1); neg_rc=$?
set -e
if [ "$neg_rc" -eq 0 ]; then
  echo "FAIL: position negative control exited 0" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'bad_pos=[1-9][0-9]*'; then
  echo "FAIL: position negative control did not report bad_pos>0" >&2; exit 1
fi
echo "PASS: negative control (corrupt vertex bits -> bad_pos>0, exit $neg_rc)"; pass=$((pass + 1))

# Negative control 2: corrupt one emitted face index; the welded-key multiset
# must disagree (an out-of-range index yields no key triple).
awk '$1=="face" && $2=="0" && $3=="0" { $4="999" } {print}' \
  "$tmp/c.txt" > "$tmp/neg_face.txt"
if cmp -s "$tmp/c.txt" "$tmp/neg_face.txt"; then
  echo "FAIL: face-index negative control did not modify the dump" >&2; exit 1
fi
set +e
neg=$(run_twin "$tmp/neg_face.txt" 2>&1); neg_rc=$?
set -e
if [ "$neg_rc" -eq 0 ]; then
  echo "FAIL: face-index negative control exited 0" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'bad_topo=[1-9][0-9]*'; then
  echo "FAIL: face-index negative control did not report bad_topo>0" >&2; exit 1
fi
echo "PASS: negative control (corrupt face index -> bad_topo>0, exit $neg_rc)"; pass=$((pass + 1))

echo "passes=$pass"
[ "$pass" -eq 12 ]
echo "OK mc-sparse-topology: sphere tree (16^3, 2 transforms), welded-key topology exact, positions bit-exact (tolerance checked)"
