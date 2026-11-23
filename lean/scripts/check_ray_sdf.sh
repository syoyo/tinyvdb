#!/usr/bin/env bash
# Differential check for SDF zero-crossing pairs along a ray (PH-4 follow-up).
# Calls the real tvdb_segments_along_ray and compares pair counts and crossing
# times with the exact-rational Vdb/RaySdf model (tolerance 1e-6).
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"
root=$(cd "$here/.." && pwd)
tmp=$(mktemp -d "${TMPDIR:-/tmp}/raysdfcheck.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

cc=${CC:-cc}
"$cc" -O2 -std=c11 -I"$root/src" \
  "$here/scripts/ray_sdf_c.c" "$root/src/tinyvdb_ray.c" \
  "$root/src/tinyvdb_sample.c" "$root/src/tinyvdb_mesh.c" \
  "$root/src/tinyvdb_lifecycle.c" "$root/src/tvdb_memory.c" \
  "$root/src/tinyvdb_ops.c" "$root/src/tinyvdb_poisson.c" \
  "$root/src/tinyvdb_thread.c" "$root/src/lz4.c" "$root/src/miniz.c" \
  -lm -o "$tmp/ray_sdf_c"

lake -d "$here" build raysdfcheck

"$tmp/ray_sdf_c" > "$tmp/c.txt"
"$here/.lake/build/bin/raysdfcheck" "$tmp/c.txt" > "$tmp/lean.txt"

python3 - "$tmp/c.txt" "$tmp/lean.txt" <<'PY'
import sys
from fractions import Fraction

def parse(path, rational):
    cases = []
    cur = None
    for line in open(path):
        p = line.split()
        if not p: continue
        if p[0] == 'out':
            cur = {'n': int(p[1]), 'pairs': []}
            cases.append(cur)
        elif p[0] == 'pair' and cur is not None:
            vals = []
            for tok in p[1:3]:
                tok = tok.replace(' / ', '/')
                vals.append(float(Fraction(tok)) if rational else float(tok))
            cur['pairs'].append(tuple(vals))
    return cases

a = parse(sys.argv[1], False)
b = parse(sys.argv[2], True)
bad = 0
if len(a) != len(b):
    print('FAIL: different case counts'); bad += 1
for i, (x, y) in enumerate(zip(a, b)):
    if x['n'] != y['n'] or len(x['pairs']) != len(y['pairs']):
        print(f'FAIL case {i}: counts {x["n"]}/{y["n"]} pairs {len(x["pairs"])}/{len(y["pairs"])}')
        bad += 1
        continue
    for k, (u, v) in enumerate(zip(x['pairs'], y['pairs'])):
        if max(abs(u[0]-v[0]), abs(u[1]-v[1])) > 1e-6:
            print(f'FAIL case {i} pair {k}: {u} vs {v}')
            bad += 1
print(f'bad={bad}')
sys.exit(1 if bad else 0)
PY

echo "OK ray-sdf: $(grep -c '^case ' "$tmp/c.txt") cases, pairs agree within 1e-6"
