#!/usr/bin/env bash
# Differential check for SDF part decomposition and enclosed regions.
#
# The C driver (sdf_parts_c.c) calls the real tvdb_sdf_segmentation and
# tvdb_sdf_extract_enclosed_regions on seeded 6^3 fields (including sealed
# cavities and touch-connected blobs). The Lean twin (Vdb.SdfPartsCheck)
# recomputes the components and cavity from the emitted field using the
# executable mirror of Vdb.Segmentation.Conn. Canonical dumps are diffed:
# component membership and cavity masks must agree exactly.
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/sdfpartscheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/sdf_parts_c.c" \
  "$root/src/tinyvdb_levelset.c" "$root/src/tinyvdb_lifecycle.c" \
  "$root/src/tvdb_memory.c" "$root/src/tinyvdb_ops.c" \
  "$root/src/tinyvdb_mesh.c" "$root/src/tinyvdb_poisson.c" \
  "$root/src/tinyvdb_sample.c" "$root/src/tinyvdb_thread.c" \
  "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/sdf_parts_c"

lake -d "$here" build sdfpartcheck

"$tmp/sdf_parts_c" > "$tmp/c.txt"
"$here/.lake/build/bin/sdfpartcheck" "$tmp/c.txt" > "$tmp/lean.txt"

if ! diff -u "$tmp/c.txt" "$tmp/lean.txt" > "$tmp/diff.txt"; then
  echo "FAIL: C and Lean part/cavity dumps disagree" >&2
  head -60 "$tmp/diff.txt" >&2
  exit 1
fi

cases=$(grep -c '^case ' "$tmp/c.txt" || true)
parts=$(grep -c '^part ' "$tmp/c.txt" || true)
cavities=$(grep -c '^cavity [0-9]' "$tmp/c.txt" || true)
echo "OK sdf-parts: cases=$cases parts=$parts nonempty_cavities=$cavities exact"
