#!/usr/bin/env bash
# Differential check for the supporting-plane convex hull.
# C calls tvdb_points_convex_hull_ex; Lean recomputes hull faces over exact
# rationals. Face index triples are compared exactly.
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/convexhullcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/convex_hull_c.c" "$root/src/tinyvdb_convex_decomp.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_lifecycle.c" \
  "$root/src/tvdb_memory.c" "$root/src/tinyvdb_ops.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/convex_hull_c"

lake -d "$here" build convexhullcheck

"$tmp/convex_hull_c" > "$tmp/c.txt"
"$here/.lake/build/bin/convexhullcheck" "$tmp/c.txt" > "$tmp/lean.txt"

grep -E '^(out|face) ' "$tmp/c.txt" > "$tmp/c.out"
grep -E '^(out|face) ' "$tmp/lean.txt" > "$tmp/lean.out"

if ! diff -u "$tmp/c.out" "$tmp/lean.out" > "$tmp/diff.txt"; then
  echo "FAIL: C and Lean convex hulls disagree" >&2
  head -60 "$tmp/diff.txt" >&2
  exit 1
fi

echo "OK convex-hull: $(grep -c '^case ' "$tmp/c.txt") cases, faces exact"
