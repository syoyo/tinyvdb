#!/usr/bin/env bash
# Differential check for the mask-compression classifier.
#
# Enumerates every synthetic 8-slot node (all 256 value masks x every
# assignment of the five-symbol alphabet {bg, -bg, 2.5f, 3.5f, 4.5f} to the
# inactive slots; 6^8 = 1,679,616 nodes) and compares the classification
# emitted by the C writer (`tvdb__write_mask_values`, captured at the
# classification prefix; the value payload is not compared) against the Lean
# model (`Vdb.MaskCompress.classify`).
#
# Both sides print one line per node:
#   mask assign code v0hex v1hex selhex
# compared byte-wise. On mismatch the first differing line is reported with
# the case coordinates; the input of any case can be reproduced from
# (mask, assign) alone.
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
tmp=$(mktemp -d "${TMPDIR:-/tmp}/maskclassify.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -std=c11 -O2 -I"$root/src" \
  "$here/scripts/mask_classify_c.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -o "$tmp/mask_classify_c"

lake -d "$here" build maskcheck

"$tmp/mask_classify_c" > "$tmp/c.txt"
"$here/.lake/build/bin/maskcheck" > "$tmp/lean.txt"

if cmp -s "$tmp/c.txt" "$tmp/lean.txt"; then
  printf 'OK maskclassify: %s nodes identical\n' "$(wc -l < "$tmp/c.txt")"
else
  python3 - "$tmp/c.txt" "$tmp/lean.txt" <<'PY'
import sys
with open(sys.argv[1]) as a, open(sys.argv[2]) as b:
    for i, (la, lb) in enumerate(zip(a, b), 1):
        if la != lb:
            print(f"MISMATCH line {i}:")
            print(f"  c:    {la.rstrip()}")
            print(f"  lean: {lb.rstrip()}")
            sys.exit(1)
    la, lb = a.readline(), b.readline()
    print(f"MISMATCH after common prefix: c={la.rstrip()!r} lean={lb.rstrip()!r}")
    sys.exit(1)
PY
  exit 1
fi
