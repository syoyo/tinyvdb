#!/usr/bin/env bash
# Differential check for convex part decomposition (PH-3).
# The C driver calls the real tvdb_mesh_convex_decompose_ex; the Lean twin
# recomputes union-find components and AABBs from the input. Boxes and labels
# are compared exactly.
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/convexcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/convex_c.c" "$root/src/tinyvdb_convex_decomp.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_lifecycle.c" \
  "$root/src/tvdb_memory.c" "$root/src/tinyvdb_ops.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/convex_c"

lake -d "$here" build convexcheck

"$tmp/convex_c" > "$tmp/c.txt"
"$here/.lake/build/bin/convexcheck" "$tmp/c.txt" > "$tmp/lean.txt"

grep -E '^(part|label) ' "$tmp/c.txt" > "$tmp/c.out"
grep -E '^(part|label) ' "$tmp/lean.txt" > "$tmp/lean.out"

if ! diff -u "$tmp/c.out" "$tmp/lean.out" > "$tmp/diff.txt"; then
  echo "FAIL: C and Lean convex-part dumps disagree" >&2
  head -60 "$tmp/diff.txt" >&2
  exit 1
fi

cases=$(grep -c '^case ' "$tmp/c.txt" || true)
parts=$(grep -c '^part ' "$tmp/c.out" || true)
echo "OK convex-parts: cases=$cases parts=$parts boxes+labels exact"
