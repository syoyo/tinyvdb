#!/usr/bin/env bash
# Differential check for broadphase+narrowphase collision queries.
# The C driver calls tvdb_collision_sphere_mesh_ex; the Lean twin recomputes
# AABB rejection and exact-rational contacts. Counts and face ids compared.
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/collisioncheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/collision_c.c" "$root/src/tinyvdb_contact.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_lifecycle.c" \
  "$root/src/tvdb_memory.c" "$root/src/tinyvdb_ops.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/collision_c"

lake -d "$here" build collisioncheck

"$tmp/collision_c" > "$tmp/c.txt"
"$here/.lake/build/bin/collisioncheck" "$tmp/c.txt" > "$tmp/lean.txt"

grep -E '^(out|contact) ' "$tmp/c.txt" > "$tmp/c.out"
grep -E '^(out|contact) ' "$tmp/lean.txt" > "$tmp/lean.out"

if ! diff -u "$tmp/c.out" "$tmp/lean.out" > "$tmp/diff.txt"; then
  echo "FAIL: C and Lean collision-pipeline dumps disagree" >&2
  head -60 "$tmp/diff.txt" >&2
  exit 1
fi

echo "OK collision-pipeline: $(grep -c '^case ' "$tmp/c.txt") cases, counts+faces exact"
