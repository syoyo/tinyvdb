"""Load fresh out-of-tree extensions without copying build products to source."""
import importlib.util
import os
from pathlib import Path
import sys


def load_extensions():
    if os.environ.get("TINYVDB_TEST_INSTALLED") == "1":
        return
    for name in ("_tinyvdb", "_tinyvdb_nanovdb"):
        for directory in sys.path:
            for base in (Path(directory) / "python", Path(directory)):
                candidates = list(base.glob(name + ".*.so"))
                if not candidates:
                    continue
                spec = importlib.util.spec_from_file_location("tinyvdb." + name, candidates[0])
                module = importlib.util.module_from_spec(spec)
                sys.modules[spec.name] = module
                spec.loader.exec_module(module)
                break
            else:
                continue
            break
