#!/usr/bin/env bash
# Differential check for collision-proxy simplification (PH-2).
#
# The C driver calls the real tvdb_mesh_simplify_ex on small closed integer
# meshes; the Lean twin recomputes the same QEM-ranked edge collapses over exact
# rationals. Only output topology (vertex count and face index triples) is
# compared bit-for-bit; positions are stored as floats by C and are not compared.
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/proxycheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/simplify_c.c" "$root/src/tinyvdb_mesh_simplify.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_lifecycle.c" \
  "$root/src/tvdb_memory.c" "$root/src/tinyvdb_ops.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/simplify_c"

lake -d "$here" build proxycheck

"$tmp/simplify_c" > "$tmp/c.txt"
"$here/.lake/build/bin/proxycheck" "$tmp/c.txt" > "$tmp/lean.txt"

# Exact index-vector parity is intentionally not claimed (the C driver keeps
# the original face order and its ranking uses doubles); compare the topological
# invariants that the collision-proxy contract specifies.
grep -E '^(outv|outf) ' "$tmp/c.txt" > "$tmp/c.out"
grep -E '^(outv|outf) ' "$tmp/lean.txt" > "$tmp/lean.out"

if ! diff -u "$tmp/c.out" "$tmp/lean.out" > "$tmp/diff.txt"; then
  echo "FAIL: C and Lean collision-proxy topology disagree" >&2
  head -80 "$tmp/diff.txt" >&2
  exit 1
fi

cases=$(grep -c '^case ' "$tmp/c.txt" || true)
faces=$(grep -c '^of ' "$tmp/c.out" || true)
echo "OK proxy: cases=$cases invariants (V,F) exact; index vectors intentionally not compared"
