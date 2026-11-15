#!/usr/bin/env python3
"""Regenerate the tables embedded in lean/Vdb/McTable.lean from the shipped
C headers (`src/tinyvdb_mc_tri_table.h`, `src/tinyvdb_mesh.c`).

  ./scripts/gen_mc_table.py          # rewrite Vdb/McTable.lean in place
  ./scripts/gen_mc_table.py --check  # exit 0 iff the embedded tables match the
                                     # C headers (byte-identical content); 1 otherwise

The Lean theorems in that module quantify over the shipped table values by
`native_decide`, so drift between the C table and the Lean copy would silently
weaken every table-level theorem. The `--check` mode is the guard.
"""
import re
import sys
import os

root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
mc_tri_h = os.path.join(root, 'src', 'tinyvdb_mc_tri_table.h')
mc_mesh_c = os.path.join(root, 'src', 'tinyvdb_mesh.c')
lean_file = os.path.join(root, 'lean', 'Vdb', 'McTable.lean')

BEGIN = '/- BEGIN GENERATED TABLES'
END = '/- END GENERATED TABLES -/'

def tables_from_c():
    src = open(mc_tri_h).read()
    m = re.search(r'MC_TRI_TABLE\[256\]\[16\]\s*=\s*\{(.*?)\};', src, re.S)
    if not m:
        print('FAIL: could not find MC_TRI_TABLE in', mc_tri_h); sys.exit(2)
    rows = []
    for mm in re.finditer(r'\{([^}]*)\}', m.group(1)):
        # -1 (the C's triangle-list terminator) is encoded as 12 in the
        # Lean copy: arrays of Nat cannot hold -1.
        rows.append(', '.join('12' if x == '-1' else x
                              for x in re.findall(r'-?\d+', mm.group(1))))
    if len(rows) != 256:
        print(f'FAIL: expected 256 rows, got {len(rows)}'); sys.exit(2)
    out = ["def mcTriTable : Array (Array Nat) := #["]
    for r in rows:
        out.append(f"  #[{r}],")
    out.append("]")

    src = open(mc_mesh_c).read()
    m = re.search(r'MC_EDGE_TABLE\[256\]\s*=\s*\{(.*?)\};', src, re.S)
    if not m:
        print('FAIL: could not find MC_EDGE_TABLE in', mc_mesh_c); sys.exit(2)
    vals = [int(x, 16) for x in re.findall(r'0x[0-9a-fA-F]+', m.group(1))]
    if len(vals) != 256:
        print(f'FAIL: expected 256 edge entries, got {len(vals)}'); sys.exit(2)
    out.append("def mcEdgeTable : Array Nat := #[")
    for i in range(0, 256, 16):
        out.append("  " + ", ".join(str(v) for v in vals[i:i + 16]) + ",")
    out.append("]")
    return '\n'.join(out)

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else '--write'
    body = tables_from_c()
    src = open(lean_file).read()
    i = src.index(BEGIN)
    i = src.index('-/', i) + 2    # end of the (possibly multi-line) marker comment
    i = src.index('\n', i) + 1   # start of the line after the marker comment
    j = src.index(END)
    head, tail = src[:i], src[j:]
    new = head + '\n' + body + '\n\n' + tail
    if mode == '--check':
        if new == src:
            print('OK: embedded tables match the shipped C headers')
            sys.exit(0)
        print('FAIL: Vdb/McTable.lean tables are out of sync with the C headers')
        sys.exit(1)
    open(lean_file, 'w').write(new)
    print('wrote', lean_file)

if __name__ == '__main__':
    main()
