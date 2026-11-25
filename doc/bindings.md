# Python and WebAssembly bindings

> Extracted from the [TinyVDB README](../README.md) for detailed reference.

## Python bindings

Install the Python extension:

```bash
pip install tinyvdb
```

Or build from source:

```bash
pip install .  # from the repository root
```

Usage:

```python
import tinyvdb

from contextlib import closing
from tinyvdb import nanovdb

# Open a NanoVDB file
with closing(nanovdb.NanoVDBFile("input.nvdb")) as f:
    print(f"Grids: {f.grid_count()}")
    for i in range(f.grid_count()):
        print(f"Grid {i}: {f.grid_name(i)}")
        print(f"  Type: {f.grid_type(i)}")
        print(f"  BBox: {f.bbox(i)}")
        print(f"  Voxel size: {f.voxel_size(i, 0)}")
    val = f.get(0, 100, 100, 100)
    print(f"Value at (100, 100, 100): {val}")
```

Writing:

```python
# Save to file
f.save("output.nvdb", codec=tinyvdb.CODEC_BLOSC)

# Write to bytes
data = f.to_bytes(codec=tinyvdb.CODEC_ZIP)
```

Writing a dense grid to `.vdb` (value type chosen from the numpy dtype —
`float32`/`float64`/`int32`/`int64`/`bool` scalar grids, or a `(nx, ny, nz, 3)`
`float32` array for a `vec3f` grid):

```python
import numpy as np, tinyvdb

sdf = np.random.randn(32, 32, 24).astype(np.float32)
tinyvdb.write_dense_grid("sdf.vdb", sdf, voxel_size=0.05)     # Tree_float_5_4_3
arr, voxel_size, origin = tinyvdb.read_dense_grid("sdf.vdb")  # dtype preserved
```

See `python/README.md` for the full dtype table and the `bool` caveat (tinyvdb's
1-byte-per-voxel BOOL layout is not byte-compatible with OpenVDB's bit-packed
format).

Utility functions:

```python
import tinyvdb

# Get node sizes
leaf_size = tinyvdb.leaf_node_size()      # Default: Float
leaf_size = tinyvdb.leaf_node_size(tinyvdb.GRID_TYPE_DOUBLE)

# Get value size
val_size = tinyvdb.value_size()            # 4 for Float
val_size = tinyvdb.value_size(tinyvdb.GRID_TYPE_VEC3F)  # 12
```

## JavaScript and WebAssembly

Install the Emscripten module for Node.js:

```bash
npm install tinyvdb
```

The package contains the JavaScript module loader and its companion
`tinyvdb.wasm` binary. The module factory is asynchronous:

```js
const createTinyVDB = require("tinyvdb");

async function main() {
  const tvdb = await createTinyVDB();
  const grid = new tvdb.DenseGrid(16, 16, 16, 1.0);
  console.log(grid.size());
}

main();
```

For browser usage, see the [WebAssembly demo](../web/demo.html).
