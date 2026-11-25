#!/usr/bin/env bash
# Tie-explanation gate for the C BVH closest-face traversal used by dense
# mesh→SDF (tvdb_bvh_closest, src/tinyvdb_mesh.c).
#
# Companion to check_meshsdf_bvh.sh. scripts/meshsdf_bvh_ties_c.c #includes
# tinyvdb_mesh.c and regenerates the same cube + icosahedron corpus (same
# h/band, same row-major seed chain, same C winner). For EVERY query it dumps
# the Float32 squared distance of EVERY face, computed with the identical
# expression tvdb_bvh_closest uses (tri_closest_point_c -> sub_c -> dot_c),
# as 8-hex IEEE-754 bits.
#
# The exact-ℚ twin Vdb.MeshSdfBvhTieCheck recomputes exact squared distances,
# finds the exact-minimum face set and its lowest index (the exact-ℚ winner),
# and checks that EVERY exact tie has its C winner explained by Float32
# rounding: the C winner is the (Float32 dsq, face index) minimum of the exact
# tie set. The 11 documented C/Lean face disagreements are the 11 exact ties
# where the C winner's Float32 dsq is strictly smaller than that of the
# lower-index exact winner. Nothing is weakened or called a pass: this is an
# explanation of unmirrored Float32 behaviour, with a loud NOT MIRRORED banner.
#
# Negative control: corrupt the C winner's dumped Float32 dsq (and its rd) in
# the first disagreement query to the largest finite Float32; the twin must
# report ties_unexplained>0 and exit non-zero.
set -euo pipefail

# CTest maps 77 to "skipped", not passed. Skip cleanly when lake is absent;
# a real build/check failure still exits non-77.
if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/meshsdfbvhties.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/meshsdf_bvh_ties_c.c" \
  "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/meshsdf_bvh_ties_c"

# Build with cwd = lean/ so elan honours lean/lean-toolchain (v4.36.0),
# independent of the caller's cwd. Hard 600 s cap (exact-ℚ proof/eval budget).
(cd "$here" && timeout 600 lake build Vdb.MeshSdfBvhTieCheck)

# Preferred: the registered lean_exe target (root Vdb.MeshSdfBvhTieCheck).
# Until registration lands, fall back loudly to running the module directly.
if (cd "$here" && timeout 600 lake build meshsdfbvhtiecheck >/dev/null 2>&1); then
  twin="$here/.lake/build/bin/meshsdfbvhtiecheck"
  run_twin() { "$twin" "$1"; }
else
  echo "NOTE: lean_exe target 'meshsdfbvhtiecheck' is not registered yet; using 'lake env lean --run' fallback"
  run_twin() { (cd "$here" && timeout 600 lake env lean --run Vdb/MeshSdfBvhTieCheck.lean "$1"); }
fi

"$tmp/meshsdf_bvh_ties_c" > "$tmp/ties.txt"
out=$(run_twin "$tmp/ties.txt")
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

check "queries"         "$(cnt queries)"         280
check "ties_exact"      "$(cnt ties_exact)"      148
check "ties_explained"  "$(cnt ties_explained)"  148
check "ties_unexplained" "$(cnt ties_unexplained)" 0
check "f32_dsq_diff"    "$(cnt f32_dsq_diff)"    11
check "disagreements"   "$(cnt disagreements)"   11
check "rd_consistent"   "$(cnt rd_consistent)"   280
check "bad_non_tie"     "$(cnt bad_non_tie)"     0
check "bad_dump"        "$(cnt bad_dump)"        0

# Structural invariants: every exact tie is explained; the 11 disagreements
# are a subset of the exact ties and each has a differing Float32 dsq.
te=$(cnt ties_exact); tx=$(cnt ties_explained); d=$(cnt disagreements); fd=$(cnt f32_dsq_diff)
if [ "$tx" -eq "$te" ] && [ "$d" -le "$te" ] && [ "$fd" -eq "$d" ]; then
  echo "PASS: explained ties cover exact ties (ties_explained=$tx = ties_exact=$te; f32_dsq_diff=$fd = disagreements=$d)"; pass=$((pass + 1))
else
  echo "FAIL: tie structure inconsistent (te=$te tx=$tx d=$d fd=$fd)" >&2; exit 1
fi
if printf '%s\n' "$out" | grep -q '^NOT MIRRORED:'; then
  echo "PASS: unmirrored banner present"; pass=$((pass + 1))
else
  echo "FAIL: missing NOT MIRRORED banner" >&2; exit 1
fi

# Negative control: in the first disagreement (mesh 1 query 9, C winner 18),
# overwrite the C winner's per-face Float32 dsq AND its returned rd with the
# largest finite Float32. rd stays consistent, but Float32 no longer explains
# the C winner, so the twin must report ties_unexplained>0 and fail.
awk '$1=="tie" && $2=="1" && $3=="9" {
       for (i=1;i<=NF;i++) { if ($i=="rd") prd=i; if ($i=="rf") prf=i; if ($i=="dsq") pdsq=i }
       f = pdsq + 1 + $(prf+1)
       $(prd+1) = "7f7fffff"
       $(f) = "7f7fffff"
     } {print}' "$tmp/ties.txt" > "$tmp/neg.txt"
set +e
neg=$(run_twin "$tmp/neg.txt" 2>&1); neg_rc=$?
set -e
echo "$neg" | tail -2
if [ "$neg_rc" -eq 0 ]; then
  echo "FAIL: negative control exited 0 (expected non-zero)" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'ties_unexplained=[1-9][0-9]*'; then
  echo "FAIL: negative control did not report ties_unexplained>0" >&2; exit 1
fi
echo "PASS: negative control (corrupted Float32 dsq -> ties_unexplained>0, exit $neg_rc)"; pass=$((pass + 1))

echo "passes=$pass"
[ "$pass" -eq 12 ]
echo "OK meshsdf-bvh-ties: 2 closed meshes x 280 queries; 148 exact ties all explained by real-C Float32 per-face dsq; 11 documented disagreements now explained (f32_dsq_diff=11)"
