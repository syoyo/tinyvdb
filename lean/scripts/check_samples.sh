#!/usr/bin/env bash
# Build the Lean `vdbcheck` executable and compare its prologue/descriptor
# view of the repository's sample .vdb files against the C reader.
#
# Usage: check_samples.sh [FILE...]
#   VDBDUMP=/path/to/vdbdump overrides the C example (default: build/vdbdump).
set -euo pipefail

# CTest maps 77 to "skipped", not passed. Skip cleanly if the Lean
# toolchain is absent; a real build/check failure still exits non-77.
if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)

# The package pins its Lean toolchain in lean/lean-toolchain. CTest invokes
# these scripts from the build directory, where elan would otherwise select
# the ambient toolchain (possibly incompatible with the pinned mathlib).
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)

lake -d "$here" build vdbcheck

if [ "$#" -gt 0 ]; then
  files=("$@")
else
  files=("$root/sphere.vdb" "$root/cube.vdb" "$root/bunny.vdb" "$root/smoke.vdb"
         "$root/data/utahteapot.vdb" "$root/data/suzanne.vdb"
         "$root/data/sphere-div1.vdb" "$root/data/sphere_points.vdb"
         "$root/data/bunny_bgcolor.vdb" "$root/data/explosion.vdb"
         "$root/data/smoke.vdb" "$root/data/bunny_cloud.vdb"
         "$root/data/dragon.vdb")
fi

python3 "$here/scripts/diff_vdbdump.py" \
  "$here/.lake/build/bin/vdbcheck" \
  "${VDBDUMP:-$root/build/vdbdump}" \
  "${files[@]}"
