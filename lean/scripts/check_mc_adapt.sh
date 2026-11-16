#!/usr/bin/env bash
# Differential check of the C MC-adaptivity Float floor / int64-key path
# (tool_cluster_range, src/tinyvdb_sparse_tools.c) against its Lean twin.
#
# Both sides walk the same seeded xorshift64 corpus (adversarial coordinates:
# +/-0, +/-Inf, NaN payloads, subnormals, the exact +/-2^63 boundary doubles,
# the 2^53 integer boundary; adversarial steps) and print one summary line
#   ok <n> overflow <n> checksum <n>
# where checksum is the wrapping uint64 sum of the raw bits of the accepted (integral) keys.
#
# Usage: check_mc_adapt.sh [n]   (default 1000000 vertices = 3n axis evaluations)
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)

n=${1:-1000000}
scratch=$(mktemp -d "${TMPDIR:-/tmp}/mc_adapt.XXXXXX")
trap 'rm -rf "$scratch"' EXIT

cc -O2 -std=c11 -o "$scratch/mc_adapt_c" "$here/scripts/mc_adapt_c.c" -lm

lake -d "$here" build mckeycheck >&2
lean_out=$(lake -d "$here" exe mckeycheck "$n")
capi_out=$("$scratch/mc_adapt_c" "$n")

echo "lean: $lean_out"
echo "c:    $capi_out"

if [ "$lean_out" = "$capi_out" ]; then
  echo "check_mc_adapt: OK ($n vertices, $((3 * n)) axis evaluations)"
  exit 0
fi
echo "check_mc_adapt: MISMATCH" >&2
exit 1
