#!/usr/bin/env bash
# Build the Lean `vdbcheck` executable and compare its prologue/descriptor
# view of the repository's sample .vdb files against the C reader.
#
# Usage: check_samples.sh [FILE...]
#   VDBDUMP=/path/to/vdbdump overrides the C example (default: build/vdbdump).
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
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
