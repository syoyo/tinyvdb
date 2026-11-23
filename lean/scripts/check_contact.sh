#!/usr/bin/env bash
# Differential check for sphere/mesh contacts and manifold reduction (PH-4).
# The C driver calls the real tvdb_mesh_sphere_contacts_ex; the Lean twin
# recomputes contact faces with an exact-rational Ericson closest point and the
# same greedy reduction. Contact face indices and counts are compared exactly.
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/contactcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/contact_c.c" "$root/src/tinyvdb_contact.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_lifecycle.c" \
  "$root/src/tvdb_memory.c" "$root/src/tinyvdb_ops.c" \
  "$root/src/tinyvdb_poisson.c" "$root/src/tinyvdb_sample.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/contact_c"

lake -d "$here" build contactcheck

"$tmp/contact_c" > "$tmp/c.txt"
"$here/.lake/build/bin/contactcheck" "$tmp/c.txt" > "$tmp/lean.txt"

# Only counts and face indices are compared; C positions are floats and the
# Lean twin keeps them as exact rationals.
awk '/^(out|contact) / { if ($1 == "out") print $0; else print "contact", $2 }' \
  "$tmp/c.txt" > "$tmp/c.out"
awk '/^(out|contact) / { if ($1 == "out") print $0; else print "contact", $2 }' \
  "$tmp/lean.txt" > "$tmp/lean.out"

if ! diff -u "$tmp/c.out" "$tmp/lean.out" > "$tmp/diff.txt"; then
  echo "FAIL: C and Lean contact dumps disagree" >&2
  head -60 "$tmp/diff.txt" >&2
  exit 1
fi

cases=$(grep -c '^case ' "$tmp/c.txt" || true)
contacts=$(grep -c '^contact ' "$tmp/c.out" || true)
echo "OK contact: cases=$cases manifold_contacts=$contacts faces+counts exact"
