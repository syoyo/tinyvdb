#!/usr/bin/env bash
# Differential check for the `mesh_triangle_double` double-precision fallback
# of `tri_closest_point_c` (src/tinyvdb_mesh.c), the one mesh→SDF stage the
# other Float32 twins deliberately do not mirror.
#
# scripts/meshsdf_double_c.c #includes tinyvdb_mesh.c so the REAL static
# `mesh_triangle_double` is exercised. It builds 16 cases that actually divert
# the float32 kernel into that fallback (float32 overflow in d1/d2, overflow
# of vc, collinear / identical vertices), and dumps the float32 inputs, the
# three double closest-point components BEFORE their (float) cast, the real
# float32 result, the final voxel value, the fallback reason and double branch.
#
# Vdb.MeshSdfDoubleCheck (Lean, executable) then checks, bit-exactly:
#   * its own IEEE-754 round-to-nearest-even binary64→binary32 encoder applied
#     to the dumped double bits reproduces the C `(float)` cast (rne_ok);
#   * the float32→double transcription agrees with the real function (txok);
#   * the post-cast Float32 voxel chain (sub/dot/sqrt/sign/clamp) agrees (voxel_ok).
# It also recomputes the closest point from the float32 inputs in exact ℚ,
# checks the Voronoi branch (branch_ok) and compares the double components
# within |qLean-qC| ≤ (|qC|+1)/1e9 (dist_ok) — the double predicates round,
# so only the cast is compared bit-exactly. The encoder has 14 C-computed
# anchors (selftest_ok).
#
# Not a pass/fail on any rounding *artifact*: all 16 cases are exact matches
# on every counter; a single differing bit fails the gate.
#
# Negative control: zeroing one dumped double component makes the twin report
# bad_rne=1 and bad_dist=1 and exit non-zero (verified below).
#
# CTest NAME to register: lean_diff_meshsdf_double
set -euo pipefail

# CTest maps 77 to "skipped", not passed. Skip cleanly if the Lean toolchain
# is absent; a real build/check failure still exits non-77.
if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/meshsdfdouble.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

# Pin the toolchain when invoked from the build directory.
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/meshsdf_double_c.c" \
  "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/meshsdf_double_c"

# Build the module with cwd = lean/ so elan honours lean/lean-toolchain.
(cd "$here" && timeout 600 lake build Vdb.MeshSdfDoubleCheck)

# Preferred: the registered lean_exe target. Until registration lands, fall
# back loudly to running the module directly.
if (cd "$here" && timeout 600 lake build meshsdfdoublecheck >/dev/null 2>&1); then
  twin="$here/.lake/build/bin/meshsdfdoublecheck"
  run_twin() { "$twin" "$1"; }
else
  echo "NOTE: lean_exe target 'meshsdfdoublecheck' is not registered yet; using 'lake env lean --run' fallback"
  run_twin() { (cd "$here" && timeout 600 lake env lean --run Vdb/MeshSdfDoubleCheck.lean "$1"); }
fi

"$tmp/meshsdf_double_c" > "$tmp/c.txt"
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

check "selftest_ok"       "$(cnt selftest_ok)"       14
check "selftest_total"    "$(cnt selftest_total)"     14
check "cases"             "$(cnt cases)"              16
check "fallback_hits"     "$(cnt fallback_hits)"      15
check "txok_ok"           "$(cnt txok_ok)"            16
check "bad_tx"            "$(cnt bad_tx)"             0
check "rne_comp_ok"       "$(cnt rne_comp_ok)"        48
check "rne_ok"            "$(cnt rne_ok)"             16
check "bad_rne"           "$(cnt bad_rne)"            0
check "branch_ok"         "$(cnt branch_ok)"          16
check "bad_branch"        "$(cnt bad_branch)"         0
check "dist_ok"           "$(cnt dist_ok)"            16
check "bad_dist"          "$(cnt bad_dist)"           0
check "voxel_ok"          "$(cnt voxel_ok)"           16
check "bad_voxel"         "$(cnt bad_voxel)"          0

# Negative control: zero one dumped double component (case 0, d[1]); the twin
# must fail the exact cast check and the exact-ℚ distance check.
awk '$1=="case" && $2=="0" { for (i=1;i<=NF;i++) if ($i=="d") $(i+2)="0000000000000000" } {print}' \
  "$tmp/c.txt" > "$tmp/neg.txt"
set +e
neg=$(run_twin "$tmp/neg.txt" 2>&1); neg_rc=$?
set -e
echo "$neg" | tail -2
if [ "$neg_rc" -eq 0 ]; then
  echo "FAIL: negative control exited 0 (expected non-zero)" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'bad_rne=[1-9][0-9]*'; then
  echo "FAIL: negative control did not report bad_rne>0" >&2; exit 1
fi
if ! printf '%s\n' "$neg" | grep -q 'bad_dist=[1-9][0-9]*'; then
  echo "FAIL: negative control did not report bad_dist>0" >&2; exit 1
fi
echo "PASS: negative control (corrupted double -> bad_rne>0, bad_dist>0, exit $neg_rc)"; pass=$((pass + 1))

echo "passes=$pass"
[ "$pass" -eq 16 ]
echo "OK meshsdf-double: 16 fallback cases, exact round-to-nearest-even binary64->binary32 cast (48/48 components), exact-Q branch/distance, Float32 voxel chain, negative control"
