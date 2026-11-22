#!/usr/bin/env bash
# Dense marching-cubes TOPOLOGY differential gate (next VS-3 slice).
#
# Compares the REAL C `tvdb_sdf_to_mesh_ex` (scripts/mc_topology_c.c, which
# includes src/tinyvdb_mesh.c so the shipped MC tables, weld cache and emitter
# are exercised) against the independent exact-Q twin Vdb.McTopologyCheck:
#
#   MIRRORED:  cell case from decoded Float32 samples; used cube edges and
#              triangles from Vdb.McTable (T-MC-EDGE / T-MC-COMPLETE / F10);
#              welded grid-edge keys via Vdb.GridEdge.key (T-MC-WELD);
#              first-appearance vertex ids in the C sweep order; exact-Q
#              crossing interpolation; both TABLE and OUTWARD winding.
#   NOT MIRRORED (printed by the twin, never counted as a pass): the C
#              count-then-emit two-pass allocation, the rolling/hash slot
#              cache, the arena layout, and the double-precision intermediate
#              of mesh_edge_interpolate (twin uses exact rationals, so
#              positions are compared with an explicit Float32 tolerance).
#
# Corpus: 256 Bourke corner patterns in a padded 4^3 lattice + analytic sphere
# and plane on 8^3 lattices (258 fields), 2 windings per field.
# NOT covered: sparse/tree tool_mesh, NaN/Inf rejection, winding values beyond
# the two enum constants, grids with a dimension < 2, exact-iso samples.
#
# Negative controls: corrupting one vertex bit must give bad_pos>0 and a
# non-zero exit; corrupting one face index must give bad_index_table>0 and
# bad_topo_table>0 with a non-zero exit (both verified below).
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

# The package pins Lean v4.35.0 in lean/lean-toolchain. CTest invokes this
# script from the build directory, where elan would otherwise select the
# ambient toolchain and corrupt the mathlib cache. Also cd into lean/ for the
# lake calls so the pin is honoured regardless of the caller's cwd.
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/mctopology.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/mc_topology_c.c" \
  "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/mc_topology_c"

# Hard 600 s cap per proof group (the module compiles in seconds here).
(cd "$here" && timeout 600 lake build Vdb.McTopologyCheck)

# Preferred: the registered lean_exe target (root Vdb.McTopologyCheck).
# Until registration lands, fall back loudly to running the module directly.
if (cd "$here" && timeout 600 lake build mctopocheck >/dev/null 2>&1); then
  twin="$here/.lake/build/bin/mctopocheck"
  run_twin() { timeout 600 "$twin" "$1"; }
else
  echo "NOTE: lean_exe target 'mctopocheck' is not registered yet; using 'lake env lean --run' fallback"
  run_twin() { (cd "$here" && timeout 600 lake env lean --run Vdb/McTopologyCheck.lean "$1"); }
fi

"$tmp/mc_topology_c" > "$tmp/c.txt"
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
check "fields"              "$(cnt fields)"              258
check "verts"               "$(cnt verts)"               4884
check "faces_table"         "$(cnt faces_table)"         8300
check "faces_outward"       "$(cnt faces_outward)"       8300
check "exact_pos"           "$(cnt exact_pos)"           4884
check "bad_count"           "$(cnt bad_count)"           0
check "bad_index_table"     "$(cnt bad_index_table)"     0
check "bad_index_outward"   "$(cnt bad_index_outward)"   0
check "bad_topo_table"      "$(cnt bad_topo_table)"      0
check "bad_topo_outward"    "$(cnt bad_topo_outward)"    0
check "bad_pos"             "$(cnt bad_pos)"             0

if printf '%s\n' "$out" | grep -q '^stages_unmirrored=count-pass,rolling-hash-cache,arena-layout,double-intermediate$'; then
  echo "PASS: unmirrored stages reported"; pass=$((pass + 1))
else
  echo "FAIL: unmirrored stages banner missing" >&2; exit 1
fi

# Negative control 1: flip one output vertex bit; the position must disagree.
awk '$1=="vertex" && $2=="1" && $3=="0" { $5="00000000" } {print}' \
  "$tmp/c.txt" > "$tmp/neg_pos.txt"
if cmp -s "$tmp/c.txt" "$tmp/neg_pos.txt"; then
  echo "FAIL: negative control did not modify the dump" >&2; exit 1
fi
set +e
neg=$(run_twin "$tmp/neg_pos.txt" 2>&1); neg_rc=$?
set -e
if [ "$neg_rc" -eq 0 ]; then
  echo "FAIL: vertex-bit negative control exited 0" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'bad_pos=[1-9][0-9]*'; then
  echo "FAIL: vertex-bit negative control did not report bad_pos>0" >&2; exit 1
fi
echo "PASS: negative control (corrupt vertex bits -> bad_pos>0, exit $neg_rc)"; pass=$((pass + 1))

# Negative control 2: corrupt one emitted face index; both the raw index and
# the welded-key multiset must disagree.
awk '$1=="face" && $2=="1" && $3=="TABLE" && $4=="0" { $6="999" } {print}' \
  "$tmp/c.txt" > "$tmp/neg_face.txt"
if cmp -s "$tmp/c.txt" "$tmp/neg_face.txt"; then
  echo "FAIL: negative control did not modify the dump" >&2; exit 1
fi
set +e
neg=$(run_twin "$tmp/neg_face.txt" 2>&1); neg_rc=$?
set -e
if [ "$neg_rc" -eq 0 ]; then
  echo "FAIL: face-index negative control exited 0" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'bad_index_table=[1-9][0-9]*'; then
  echo "FAIL: face-index negative control did not report bad_index_table>0" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'bad_topo_table=[1-9][0-9]*'; then
  echo "FAIL: face-index negative control did not report bad_topo_table>0" >&2; exit 1
fi
echo "PASS: negative control (corrupt face index -> bad_index_table>0, bad_topo_table>0, exit $neg_rc)"; pass=$((pass + 1))

echo "passes=$pass"
[ "$pass" -eq 14 ]
echo "OK mc-topology: 258 dense fields x 2 windings (256 padded corner patterns + sphere + plane), welded-key topology exact, positions bit-exact (tolerance checked)"
