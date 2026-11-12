#!/usr/bin/env python3
"""Compare the Lean model's `.vdb` prologue/descriptor view with the C reader.

Usage: diff_vdbdump.py VDBCHECK VDBDUMP FILE...

`VDBCHECK` is the Lean executable (lean/.lake/build/bin/vdbcheck) and
`VDBDUMP` the C example (build/vdbdump). The comparison covers the header
(version, library version, UUID), the grid count and each grid's name and
type. The C reader strips the `_HalfFloat` suffix into a `(half)` marker and
the model keeps it on the wire, so the type is compared after removing it.
"""
import re
import subprocess
import sys


def lean_dump(exe, path):
    out = subprocess.run([exe, path], capture_output=True, text=True)
    if out.returncode != 0:
        raise SystemExit(f"{exe} {path}: {out.stdout.strip()} {out.stderr.strip()}")
    m = re.search(r"header version=(\d+) major=(\d+) minor=(\d+) legacy=(\w+) uuid=(\S+)", out.stdout)
    if not m:
        raise SystemExit(f"{exe} {path}: cannot parse header line")
    header = dict(version=int(m.group(1)), major=int(m.group(2)),
                  minor=int(m.group(3)), uuid=m.group(5))
    grids = []
    bodies = {}
    for line in out.stdout.splitlines():
        g = re.match(r"grid (\d+) (\S+) (\S+) instance=(\S*) offsets=", line)
        if g:
            grids.append(dict(name=g.group(2), type=g.group(3),
                              instance="" if g.group(4) == "instance=" else g.group(4)))
        b = re.match(r"  body (\d+) compression=(\d+) transform=(\S+)", line)
        if b:
            bodies[int(b.group(1))] = dict(compression=int(b.group(2)),
                                           transform=b.group(3))
    count = int(re.search(r"^grids (\d+)$", out.stdout, re.M).group(1))
    return header, count, grids, bodies


def c_dump(exe, path):
    out = subprocess.run([exe, path], capture_output=True, text=True)
    if out.returncode != 0:
        raise SystemExit(f"{exe} {path}: failed")
    text = out.stdout
    m = re.search(r"VDB version: (\d+)\s+\(lib (\d+)\.(\d+)\)", text)
    uuid = re.search(r"UUID: (\S+)", text)
    count = re.search(r"Grids: (\d+)", text)
    header = dict(version=int(m.group(1)), major=int(m.group(2)),
                  minor=int(m.group(3)), uuid=uuid.group(1) if uuid else "")
    grids = []
    bodies = {}
    # split into per-grid blocks
    parts = re.split(r"Grid\[(\d+)\]: ", text)
    for k in range(1, len(parts) - 1, 2):
        idx = int(parts[k])
        block = parts[k + 1]
        nm = re.search(r'"([^"]+)"', block)
        typ = re.search(r"Type: (\S+?)(?: \(half\))?\n", block)
        tr = re.search(r"Transform: (\S+)", block)
        co = re.search(r"Compression: [^(]*\(0x([0-9a-fA-F]+)\)", block)
        grids.append(dict(name=nm.group(1) if nm else "",
                          type=typ.group(1) if typ else ""))
        bodies[idx] = dict(transform=tr.group(1) if tr else "",
                           compression=int(co.group(1), 16) if co else -1)
    return header, int(count.group(1)), grids, bodies


def norm_type(t):
    return t[:-len("_HalfFloat")] if t.endswith("_HalfFloat") else t


def main():
    if len(sys.argv) < 4:
        raise SystemExit(__doc__)
    lean_exe, c_exe, files = sys.argv[1], sys.argv[2], sys.argv[3:]
    bad = 0
    for path in files:
        lh, lc, lg, lb = lean_dump(lean_exe, path)
        ch, cc, cg, cb = c_dump(c_exe, path)
        problems = []
        for key in ("version", "major", "minor", "uuid"):
            if lh[key] != ch[key]:
                problems.append(f"header {key}: lean={lh[key]} c={ch[key]}")
        if lc != cc:
            problems.append(f"grid count: lean={lc} c={cc}")
        if len(lg) != len(cg):
            problems.append(f"grid list length: lean={len(lg)} c={len(cg)}")
        for i, (l, c) in enumerate(zip(lg, cg)):
            if l["name"] != c["name"]:
                problems.append(f"grid {i} name: lean={l['name']} c={c['name']}")
            if norm_type(l["type"]) != norm_type(c["type"]):
                problems.append(f"grid {i} type: lean={l['type']} c={c['type']}")
            lbf = lb.get(i)
            cbf = cb.get(i)
            if lbf is not None and cbf is not None:
                if lbf["compression"] != cbf["compression"]:
                    problems.append(f"grid {i} compression: lean={lbf['compression']} c=0x{cbf['compression']:x}")
                ltr = lbf["transform"][:-3] if lbf["transform"].endswith("Map") else lbf["transform"]
                if ltr != cbf["transform"]:
                    problems.append(f"grid {i} transform: lean={lbf['transform']} c={cbf['transform']}")
        if problems:
            bad += 1
            print(f"FAIL {path}")
            for p in problems:
                print(f"  {p}")
        else:
            print(f"OK   {path}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
