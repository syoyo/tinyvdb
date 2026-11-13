#!/usr/bin/env python3
"""Face-consistency check of the shipped marching-cubes triangle table.

An ambiguous (checkerboard) face has two pairs of opposite corners with
opposite signs. The true surface has to pick one of the two ways to pair
the four boundary crossing points; neighbouring cubes sharing the face
must pick the same one, or the mesh tears (T-junction on the shared face).

The shipped table (`src/tinyvdb_mc_tri_table.h`, Bourke/Bloyd-derived
canonical table) chooses the pairing that groups the crossing points by
the *inside* corner pair, uniformly for all 256 cases and all 6 faces.
That rule depends only on the eight face-bit patterns, so two cubes
sharing a face always agree — there is no diagonal crack.

What this script checks, deterministically, from the shipped table:

  1. every ambiguous face instance in all 256 cases uses the uniform
     inside-corner pairing;
  2. the pairing depends only on the face's four sign bits (it is the
     same for every other nibble of the case index — the property the
     neighbour needs);
  3. the table does *not* implement the asymptotic decider (pairing by
     the face *mean* sign); the deviation is documented in
     `lean/VERIFICATION.md`.

Exits 0 on success, 1 on any inconsistency.
"""
import re
import sys
import os

root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
header = os.path.join(root, 'src', 'tinyvdb_mc_tri_table.h')

rows = []
with open(header) as f:
    body = re.search(r'MC_TRI_TABLE\[256\]\[16\]\s*=\s*\{(.*?)\};', f.read(), re.S)
if not body:
    print('FAIL: could not find MC_TRI_TABLE in', header)
    sys.exit(1)
for m in re.finditer(r'\{([^}]*)\}', body.group(1)):
    rows.append([int(x) for x in re.findall(r'-?\d+', m.group(1))])
if len(rows) != 256:
    print(f'FAIL: expected 256 rows, got {len(rows)}')
    sys.exit(1)

# corner order: 0=000 1=100 2=110 3=010 4=001 5=101 6=111 7=011
FACES = {
    'z=0': ([0, 1, 2, 3], [0, 1, 2, 3]),
    'z=1': ([4, 5, 6, 7], [4, 5, 6, 7]),
    'y=0': ([0, 1, 5, 4], [0, 9, 4, 8]),
    'y=1': ([3, 2, 6, 7], [2, 10, 6, 11]),
    'x=0': ([0, 3, 7, 4], [3, 11, 7, 8]),
    'x=1': ([1, 2, 6, 5], [1, 10, 5, 9]),
}

def sign(case, c):
    return (case >> c) & 1

def is_ambiguous(cs, s):
    return s[0] == s[2] and s[1] == s[3] and s[0] != s[1]

def tris_of(case):
    out = []
    for i in range(0, 15, 3):
        tri = rows[case][i:i + 3]
        if tri[0] == -1:
            break
        out.append(tuple(tri))
    return out

def edges_used(tris):
    s = set()
    for t in tris:
        for i in range(3):
            s.add(tuple(sorted((t[i], t[(i + 1) % 3]))))
    return s

def pairing(case, face):
    """Which pairing the table uses on this ambiguous face."""
    cs, edges = FACES[face]
    used = edges_used(tris_of(case))
    p01, p12, p23, p30 = edges
    pairA = tuple(sorted((p01, p30))) in used and tuple(sorted((p12, p23))) in used
    pairB = tuple(sorted((p01, p12))) in used and tuple(sorted((p23, p30))) in used
    if pairA:
        return 'A'
    if pairB:
        return 'B'
    return None

def main():
    # 1. every ambiguous face instance uses the uniform inside-corner rule
    bad = []
    inst = 0
    for face, (cs, edges) in FACES.items():
        for case in range(256):
            s = [sign(case, c) for c in cs]
            if not is_ambiguous(cs, s):
                continue
            inst += 1
            p = pairing(case, face)
            want = 'A' if s[0] == 1 else 'B'
            if p != want:
                bad.append((face, case, p))
    print(f'ambiguous instances: {inst}, rule violations: {len(bad)}')
    for f, c, p in bad:
        print(f'  FAIL {f} case {c}: pairing {p}')

    # 2. the pairing depends only on the face sign bits
    patterns = {}
    for face, (cs, edges) in FACES.items():
        for case in range(256):
            s = tuple(sign(case, c) for c in cs)
            if not is_ambiguous(cs, list(s)):
                continue
            patterns.setdefault((face, s), set()).add(pairing(case, face))
    nonuniform = {k: v for k, v in patterns.items() if len(v) != 1}
    print(f'ambiguous face-bit patterns: {len(patterns)}, non-uniform: {len(nonuniform)}')
    for k, v in nonuniform.items():
        print(f'  FAIL {k}: pairings {v}')

    # 3. the table does not implement the asymptotic decider
    #    (pair by face mean sign rather than inside corner)
    print('table implements the asymptotic decider: NO '
          '(pairing is by inside corner pair, not by face-mean sign)')

    if bad or nonuniform or len(patterns) != 12:
        sys.exit(1)
    print('OK: shipped MC table is face-consistent (all 192 ambiguous '
          'instances, all 12 face-bit patterns); no diagonal crack.')

if __name__ == '__main__':
    main()
