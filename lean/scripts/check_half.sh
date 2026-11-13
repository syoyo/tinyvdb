#!/usr/bin/env bash
# Differential check for the half-float conversions.
#
#   h2f   exhaustive over all 65536 half bit patterns
#         (tvdb__half_to_float vs Vdb.Half.halfToFloatBits)
#   f2h   exhaustive over the float->half RNE rounding fibers (one witness
#         each; tvdb__float_to_half vs Vdb.Half.floatToHalfRNE). The fiber
#         partition is machine-validated by the C harness's `audit` mode:
#         every one of the 2^32 inputs maps to a constant half within its
#         fiber. The number of audited fibers must equal the number of
#         witnesses, so no fiber is ever left out of the comparison.
#
# Both dumps are compared byte-wise; the first mismatching line is reported.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/halfcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -std=c11 -O2 -I"$root/src" \
  "$here/scripts/half_check_c.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -o "$tmp/half_check_c"

lake -d "$here" build halfcheck

mismatch() { # $1/$2 = dumps, $3 = mode
  python3 - "$1" "$2" "$3" <<'PY'
import sys
with open(sys.argv[1]) as a, open(sys.argv[2]) as b:
    for i, (la, lb) in enumerate(zip(a, b), 1):
        if la != lb:
            print(f"MISMATCH {sys.argv[3]} line {i}:")
            print(f"  c:    {la.rstrip()}")
            print(f"  lean: {lb.rstrip()}")
            sys.exit(1)
    print(f"MISMATCH {sys.argv[3]}: common prefix is a prefix of one dump; lengths differ")
    sys.exit(1)
PY
  exit 1
}

"$tmp/half_check_c" h2f > "$tmp/c_h2f.txt"
"$here/.lake/build/bin/halfcheck" h2f > "$tmp/lean_h2f.txt"
cmp -s "$tmp/c_h2f.txt" "$tmp/lean_h2f.txt" || mismatch "$tmp/c_h2f.txt" "$tmp/lean_h2f.txt" h2f

"$tmp/half_check_c" f2h > "$tmp/c_f2h.txt"
"$here/.lake/build/bin/halfcheck" f2h > "$tmp/lean_f2h.txt"
cmp -s "$tmp/c_f2h.txt" "$tmp/lean_f2h.txt" || mismatch "$tmp/c_f2h.txt" "$tmp/lean_f2h.txt" f2h

audit_out=$("$tmp/half_check_c" audit)   # exits 1 on constancy mismatch
fibers=$(printf '%s\n' "$audit_out" | sed -n 's/^audit fibers=\([0-9][0-9]*\) mismatches=0$/\1/p')
witnesses=$(wc -l < "$tmp/lean_f2h.txt")
if [ -z "$fibers" ] || [ "$fibers" != "$witnesses" ]; then
  printf 'halfcheck: audit output unexpected: %s (witnesses=%s)\n' "$audit_out" "$witnesses" >&2
  exit 1
fi
printf 'OK halfcheck: h2f 65536 patterns identical; f2h %s witnesses identical; audit: %s fibers, 0 mismatches over 2^32 inputs\n' "$witnesses" "$fibers"
