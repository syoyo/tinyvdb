"""Run the native ownership and sparse-tool regressions on the installed wheel."""
from pathlib import Path
import runpy
from importlib.metadata import version
import tinyvdb
import sys
import subprocess
import pytest


@pytest.mark.parametrize("script", [
    "test_tree_python.py", "test_sparse_tools_python.py", "test_bridge_ops.py",
])
def test_installed_sparse_apis(script, data_dir, monkeypatch):
    tests = Path(__file__).resolve().parents[2] / "tests"
    monkeypatch.syspath_prepend(str(tests))
    monkeypatch.setenv("TINYVDB_TEST_INSTALLED", "1")
    monkeypatch.setenv("TINYVDB_TEST_FIXTURE", str(Path(data_dir) / "sphere.vdb"))
    runpy.run_path(str(tests / script), run_name="__main__")


def test_installed_version():
    assert version("tinyvdb") == tinyvdb.__version__


def test_none_return_ownership(tmp_path):
    # A separate interpreter avoids pytest assertion-cache references and also
    # checks shutdown on 3.11, where newer-header borrowed returns can crash.
    script = """
import sys
import tinyvdb
file = tinyvdb.VDBFile()
file.close()
before = sys.getrefcount(None)
for _ in range(10000):
    assert file.close() is None
assert sys.getrefcount(None) == before
"""
    result = subprocess.run([sys.executable, "-c", script], cwd=tmp_path,
                            capture_output=True, text=True)
    assert result.returncode == 0, result.stderr


def test_nanovdb_public_helpers():
    nv = tinyvdb.nanovdb
    assert nv.__version__ == tinyvdb.__version__
    assert nv.grid_type_name(nv.GRID_TYPE_FLOAT) == "Float"
    assert nv.value_size() == 4
    assert nv.value_size(nv.GRID_TYPE_DOUBLE) == 8
    assert nv.value_size(nv.GRID_TYPE_VEC3F) == 12
    assert nv.leaf_node_size() > 512 * 4
