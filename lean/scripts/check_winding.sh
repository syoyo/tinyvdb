#!/usr/bin/env bash
# Executable check of the generalized winding number on closed meshes
# (src/tinyvdb_winding.c) for the two closed meshes used by the mesh→SDF
# differential harness.
#
# For 48 seeded interior + 48 seeded exterior + origin sample points per
# mesh, the C driver (scripts/winding_c.c) evaluates BOTH TVDB_WINDING_EXACT
# (sum of per-face solid angles) and TVDB_WINDING_FAST (AABB tree with a
# dipole far field), printing double bit patterns. The Lean checker
# (Vdb.WindingCheck) asserts:
#   EXACT: |w − expected| ≤ 1e-9   (expected 1 inside, 0 outside)
#   FAST:  |w − expected| ≤ 1e-6   (observed ≈ 4.4e-16 on these meshes; not
#          a universal FAST guarantee on finer meshes)
#
# Not a differential harness: it pins the executable degree-1 claim for
# closed meshes with a consistency check, nothing else.
#
# Negative control: corrupting a single printed value's bit pattern makes the
# checker report bad=1 and exit 1 (verified during development).
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/windingcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/winding_c.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_winding.c" \
  "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/winding_c"

lake -d "$here" build windingcheck

"$tmp/winding_c" > "$tmp/c.txt"
out="$("$here/.lake/build/bin/windingcheck" "$tmp/c.txt")"
echo "$out"
case "$out" in
  *pts=194*inside=98*outside=96*bad=0*) ;;
  *) echo "FAIL: expected pts=194 inside=98 outside=96 bad=0, got: $out" >&2; exit 1;;
esac
echo "OK winding: 2 closed meshes x 97 points exact and fast modes match degree 1"
