#!/usr/bin/env bash
# Bounded DMC-1 TOPOLOGY differential gate (VS-3 / DMC-1 slice).
#
# Compares the REAL C `tvdb_sdf_to_mesh_dual_one_ex` (scripts/dmc1_topology_c.c,
# which includes src/tinyvdb_mesh_dual.c so the shipped cube-local patch table,
# QEF placement and quad emitter are exercised) against the independent
# landed-model twin Vdb.Dmc1TopologyCheck over all 256 shell-pinned sign fields
# of the 3^3-cell (4^3-sample) padded grid:
#
#   MIRRORED (exact): crossed edges, mesh vertex count, quad count, quad-graph
#   component count, directed-edge closure (0/1), and V - E + F.
#   NOT MIRRORED (printed by the twin, never counted as a pass): C vertex-index
#   allocation/order, QEF/centroid vertex positions, and C patch-id allocation.
#
# Negative control: corrupting one dumped `verts` field must give badVerts>0
# and a non-zero exit (verified below).
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
tmp=$(mktemp -d "${TMPDIR:-/tmp}/dmc1topology.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -D_POSIX_C_SOURCE=199309L -I"$root/src" \
  -ffunction-sections -Wl,--gc-sections \
  "$here/scripts/dmc1_topology_c.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/tvdb_memory.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/dmc1_topology_c"

# Hard 600 s cap per proof group (the module compiles in seconds here).
(cd "$here" && timeout 600 lake build Vdb.Dmc1TopologyCheck)

# Preferred: the registered lean_exe target (root Vdb.Dmc1TopologyCheck).
# Fall back loudly to running the module directly if it is not registered.
if (cd "$here" && timeout 600 lake build dmc1topocheck >/dev/null 2>&1); then
  twin="$here/.lake/build/bin/dmc1topocheck"
  run_twin() { timeout 600 "$twin" "$1"; }
else
  echo "NOTE: lean_exe target 'dmc1topocheck' is not registered yet; using 'lake env lean --run' fallback"
  run_twin() { (cd "$here" && timeout 600 lake env lean --run Vdb/Dmc1TopologyCheck.lean "$1"); }
fi

"$tmp/dmc1_topology_c" > "$tmp/c.txt"
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

# Pin the full deterministic corpus and the all-clean counters.
check "fields"      "$(cnt fields)"      256
check "badCrossed"  "$(cnt badCrossed)"  0
check "badVerts"    "$(cnt badVerts)"    0
check "badQuads"    "$(cnt badQuads)"    0
check "badComps"    "$(cnt badComps)"    0
check "badClosed"   "$(cnt badClosed)"   0
check "badChi"      "$(cnt badChi)"      0

if printf '%s\n' "$out" | grep -q '^stages_unmirrored=vertex-indices,vertex-positions,patch-ids$'; then
  echo "PASS: unmirrored stages reported"; pass=$((pass + 1))
else
  echo "FAIL: unmirrored stages banner missing" >&2; exit 1
fi

# Negative control: corrupt one dumped verts count (field 105); the twin must
# report badVerts>0 and exit non-zero.
awk '$1=="case" && $2=="105" { $6="999" } {print}' \
  "$tmp/c.txt" > "$tmp/neg.txt"
if cmp -s "$tmp/c.txt" "$tmp/neg.txt"; then
  echo "FAIL: negative control did not modify the dump" >&2; exit 1
fi
set +e
neg=$(run_twin "$tmp/neg.txt" 2>&1); neg_rc=$?
set -e
if [ "$neg_rc" -eq 0 ]; then
  echo "FAIL: negative control exited 0" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'badVerts=[1-9][0-9]*'; then
  echo "FAIL: negative control did not report badVerts>0" >&2; exit 1
fi
echo "PASS: negative control (corrupt verts -> badVerts>0, exit $neg_rc)"; pass=$((pass + 1))

echo "passes=$pass"
[ "$pass" -eq 9 ]
echo "OK dmc1-topology: 256 shell-pinned fields, crossed/verts/quads/comps/closed/chi exact, vertex indices/positions/patch ids not compared"
