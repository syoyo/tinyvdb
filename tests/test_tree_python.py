"""Owning maintenance results, stale views, serialization and buffer contracts."""
import gc
import os
from pathlib import Path
import struct
import sys
import tempfile
import threading
import time
from python_test_bootstrap import load_extensions

load_extensions()
ROOT = Path(__file__).resolve().parent.parent
if os.environ.get("TINYVDB_TEST_INSTALLED") != "1":
    sys.path.insert(0, str(ROOT / "python"))
import tinyvdb


def raises(kind, call):
    try:
        call()
    except kind:
        return
    raise AssertionError("expected " + kind.__name__)


def main():
    f = tinyvdb.open(os.environ.get("TINYVDB_TEST_FIXTURE", str(ROOT / "sphere.vdb")))
    f.read_grids()
    g = f.grid(0)
    tree, node = g.tree, g.tree.node(0)
    initial = g.to_sparse()
    assert g.diagnose()["valid"]
    checked = g.diagnose(kind="level_set", check_gradient=True)
    assert checked["band_count"] > 0
    raises(ValueError, lambda: g.diagnose(tolerance=float("nan")))
    raises(ValueError, lambda: g.signed_flood_fill(inside_width=2))
    result = g.signed_flood_fill().prune()
    assert result.active_voxel_count() == initial["count"]
    assert g.to_sparse() == initial
    f.close()
    raises(ValueError, lambda: g.name)
    raises(ValueError, lambda: tree.num_nodes)
    raises(ValueError, lambda: node.type)
    del f, g, tree, node
    gc.collect()
    assert result.diagnose()["valid"]
    data = result.to_bytes()
    reload = tinyvdb.from_bytes(data)
    reload.read_grids()
    assert reload.grid(0).active_voxel_count() == initial["count"]
    assert reload.grid(0).to_sparse() == result.to_sparse()
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "result.vdb")
        result.save(path)
        saved = tinyvdb.open(path)
        saved.read_grids()
        assert saved.grid(0).to_sparse() == result.to_sparse()
        saved.close()
    reload.close()
    f = tinyvdb.open(os.environ.get("TINYVDB_TEST_FIXTURE", str(ROOT / "sphere.vdb"))); f.read_grids()
    old = f.grid(0); f.read_grids(); raises(ValueError, lambda: old.name)
    g = f.grid(0); tree = g.tree; node = tree.node(0)
    f.replace_grid_from_sparse(0, initial["coords"], initial["values"], "replaced", background=3)
    for call in (lambda: g.to_sparse(), lambda: tree.num_nodes, lambda: node.type):
        raises(ValueError, call)
    fresh = f.grid(0); tree = fresh.tree; node = tree.node(0)
    f.extend_grid_from_sparse(0, struct.pack("3i", 30, 30, 30), struct.pack("f", 1), "extended", background=3)
    raises(ValueError, lambda: fresh.name)
    raises(ValueError, lambda: node.type)
    fresh = f.grid(0); raises(tinyvdb.VDBError, f.read_grids)
    raises(ValueError, lambda: fresh.name)
    f.close()
    # Dense constructors validate before allocation and cannot invalidate an exported buffer.
    for cls in (tinyvdb.DenseGrid, tinyvdb.DenseVecGrid):
        for args in ((-1, 1, 1), (2147483647, 2147483647, 2147483647), (0, 1, 1)):
            raises((ValueError, OverflowError, MemoryError), lambda: cls(*args))
        raises(ValueError, lambda: cls(1, 1, 1, voxel_size=float("inf")))
        empty = cls()
        raises(ValueError, lambda: empty.__init__(1, 1, 1))
        grid = cls(1, 1, 1)
        view = memoryview(grid)
        raises(ValueError, lambda: grid.__init__(2, 2, 2))
        assert view.nbytes in (4, 12)
        view.release()
    raises(ValueError, lambda: tinyvdb.mesh_to_sdf(b"abc", b"", voxel_size=1, band_width=3))
    # A second Python thread must receive a controlled busy error while the GIL is released.
    f = tinyvdb.open(os.environ.get("TINYVDB_TEST_FIXTURE", str(ROOT / "sphere.vdb"))); f.read_grids(); g = f.grid(0)
    failures = []
    def work():
        try:
            g.erode_active(iterations=1000)
        except Exception as exc:
            failures.append(exc)
    worker = threading.Thread(target=work)
    worker.start()
    busy = False
    while worker.is_alive():
        try:
            _ = g.name
        except RuntimeError:
            busy = True
            break
        time.sleep(.0001)
    worker.join()
    assert busy and not failures, failures
    assert g.to_sparse()["count"] == initial["count"]
    f.close()
    # Argument conversion can call Python and invalidate the borrowed view.
    for operation in ("diagnose", "fill", "serialize", "save"):
        f = tinyvdb.open(os.environ.get("TINYVDB_TEST_FIXTURE", str(ROOT / "sphere.vdb")))
        f.read_grids()
        g = f.grid(0)
        class ClosingArgument:
            def __float__(self):
                f.close()
                return 3.0
            def __index__(self):
                f.close()
                return 0
            def __bool__(self):
                f.close()
                return False
        argument = ClosingArgument()
        if operation == "diagnose":
            call = lambda: g.diagnose(tolerance=argument)
        elif operation == "fill":
            call = lambda: g.signed_flood_fill(outside_width=argument, inside_width=-3)
        elif operation == "serialize":
            call = lambda: g.to_bytes(level=argument)
        else:
            call = lambda: g.save(os.path.join(tempfile.gettempdir(), "tinyvdb-invalidated-save.vdb"), use_mmap=argument)
        raises(ValueError, call)
        f.close()
    print("Python tree ownership and maintenance passed")


if __name__ == "__main__":
    main()
