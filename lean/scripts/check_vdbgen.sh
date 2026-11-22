#!/usr/bin/env bash
# Differential corpus for the generator: emit >= 2000 well-formed .vdb files
# (500 seeds x 4 kinds + 1000 multi files) and compare the Lean model's
# reading (vdbcheck) with the C reader (vdbdump) file by file, via the
# existing diff_vdbdump.py harness.
#
# Usage: check_vdbgen.sh [nseeds]   (default 500)
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
nseeds=${1:-500}

lake -d "$here" build vdbgen vdbcheck

workdir=$(mktemp -d "${TMPDIR:-/tmp}/vdbgen.XXXXXX")
trap 'rm -rf "$workdir"' EXIT

echo "check_vdbgen.sh: emitting corpus in $workdir (seeds 1..$nseeds x empty tiles sparse half multi)"
files=()
for seed in $(seq 1 "$nseeds"); do
  for kind in empty tiles sparse half multi; do
    out="$workdir/seed${seed}_${kind}.vdb"
    "$here/.lake/build/bin/vdbgen" "$out" "$seed" "$kind" >/dev/null
    files+=("$out")
  done
done
printf 'check_vdbgen.sh: %d files emitted\n' "${#files[@]}"

set +e
python3 "$here/scripts/diff_vdbdump.py" \
  "$here/.lake/build/bin/vdbcheck" \
  "${VDBDUMP:-$root/build/vdbdump}" \
  "${files[@]}" > "$workdir/results.txt" 2>&1
python_rc=$?
set -e
tail -5 "$workdir/results.txt"

ok=$(grep -c '^OK' "$workdir/results.txt")
fail=$(grep -c '^FAIL' "$workdir/results.txt" || true)
printf 'check_vdbgen.sh: python_rc=%s OK=%s FAIL=%s\n' "$python_rc" "$ok" "$fail"
if [ "$fail" != "0" ] || [ "$ok" -lt "${#files[@]}" ] || [ "$python_rc" != "0" ]; then
  grep '^FAIL' "$workdir/results.txt" | head -20
  exit 1
fi
