#!/usr/bin/env bash
# Differential check for the C BVH closest-face traversal used by dense
# mesh→SDF (tvdb_bvh_closest, src/tinyvdb_mesh.c), against the exact-ℚ twin
# Vdb.MeshSdfBvhCheck built on the proven Vdb.search_eq_brute model.
#
# scripts/meshsdf_bvh_c.c #includes tinyvdb_mesh.c so the REAL static BVH code
# is exercised on the exact cell centres of the dense lattice, with the same
# row-major seed chain as mesh_fill_rows. It dumps the mesh, the tree stats,
# each query point/seed and the C (squared distance bits, face index, feature).
# The Lean twin rebuilds a balanced tree, checks WF and the per-face AABB bound
# hypothesis, runs Vdb.search (the proven pruned traversal), cross-checks it
# against Vdb.brute, and compares the result with C.
#
# MIRRORED: AABB lower-bound prune, strict improvement + lowest-index tie-break,
# seed materialization, tree WF, per-face AABB bound, pruned traversal.
# NOT MIRRORED (loudly reported by the twin, never counted as a pass): the C
# build heuristic, DFS stack order, Float32 kernel and its double fallback.
# Distance is compared within |dq - dc| <= (dc + 1)/10000; face/feature are
# compared exactly. A face/feature disagreement with agreeing distance is
# reported as f32_tie_{face,feature} (a documented Float32-kernel artifact),
# not as a passing comparison; only distance-disagreeing mismatches fail.
#
# Negative control: zeroing one query's returned distance bits makes the twin
# report bad_dist=1 and exit non-zero (verified in this script).
set -euo pipefail

# CTest maps 77 to "skipped", not passed. Skip cleanly when lake is absent;
# a real build/check failure still exits non-77.
if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/meshsdfbvhcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/meshsdf_bvh_c.c" \
  "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/meshsdf_bvh_c"

# Build with cwd = lean/ so elan honours lean/lean-toolchain (v4.35.0),
# independent of the caller's cwd. Hard 600 s cap (proof budget).
(cd "$here" && timeout 600 lake build Vdb.MeshSdfBvhCheck)

# Preferred: the registered lean_exe target (root Vdb.MeshSdfBvhCheck).
# Until registration lands, fall back loudly to running the module directly.
if (cd "$here" && timeout 600 lake build meshsdfbvhcheck >/dev/null 2>&1); then
  twin="$here/.lake/build/bin/meshsdfbvhcheck"
  run_twin() { "$twin" "$1"; }
else
  echo "NOTE: lean_exe target 'meshsdfbvhcheck' is not registered yet; using 'lake env lean --run' fallback"
  run_twin() { (cd "$here" && timeout 600 lake env lean --run Vdb/MeshSdfBvhCheck.lean "$1"); }
fi

"$tmp/meshsdf_bvh_c" > "$tmp/c.txt"
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

check "queries"             "$(cnt queries)"             280
check "wf_ok"               "$(cnt wf_ok)"               2
check "bound_ok"            "$(cnt bound_ok)"            280
check "search_eq_brute_ok"  "$(cnt search_eq_brute_ok)"  280
check "dist_ok"             "$(cnt dist_ok)"             280
check "bad_dist"            "$(cnt bad_dist)"            0
check "bad_face_unexplained"    "$(cnt bad_face_unexplained)"    0
check "bad_feature_unexplained" "$(cnt bad_feature_unexplained)" 0

# Structural invariants: every query is either an exact face match or a
# documented Float32-kernel tie; every exact face match also matches feature.
face_ok=$(cnt face_ok); tie_face=$(cnt f32_tie_face)
if [ "$((face_ok + tie_face))" -eq 280 ]; then
  echo "PASS: face_ok + f32_tie_face = queries ($face_ok + $tie_face = 280)"; pass=$((pass + 1))
else
  echo "FAIL: face_ok + f32_tie_face != 280 ($face_ok + $tie_face)" >&2; exit 1
fi
check "feature_ok"          "$(cnt feature_ok)"          "$face_ok"

# Negative control: zero one returned distance bit pattern; the twin must
# detect a distance disagreement and fail (unexplained mismatch, not a tie).
awk '$1=="query" && $2=="0" && $3=="0" {
        for (i=1;i<=NF;i++) if ($i=="rd") $(i+1)="00000000"
      } {print}' "$tmp/c.txt" > "$tmp/neg.txt"
set +e
neg=$(run_twin "$tmp/neg.txt" 2>&1); neg_rc=$?
set -e
echo "$neg" | tail -2
if [ "$neg_rc" -eq 0 ]; then
  echo "FAIL: negative control exited 0 (expected non-zero)" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'bad_dist=[1-9][0-9]*'; then
  echo "FAIL: negative control did not report bad_dist>0" >&2; exit 1
fi
echo "PASS: negative control (corrupted rd -> bad_dist>0, exit $neg_rc)"; pass=$((pass + 1))

echo "passes=$pass"
[ "$pass" -eq 11 ]
echo "OK meshsdf-bvh: 2 closed meshes x 280 cell-centre queries; C BVH traced against exact-Q pruned search (f32_tie_face=$tie_face documented, not mirrored)"
