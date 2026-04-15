# tinyvdb tasks

Outstanding work and known gaps in tinyvdb's reader/writer, as discovered while
integrating it into the lightgeom_gui VDB viewer. Items are ordered roughly by
priority for general-purpose VDB I/O parity with libopenvdb.

## Status legend

- [x] done in `fix/half-and-vec-types` branch
- [ ] open

## Reader fixes (already landed)

- [x] **Vec3 value reader** — `tvdb__sr_read_value` now handles `VEC3I/F/D`,
  so a grid whose root or inactive-tile background is a vec3 (e.g. velocity
  `Tree_vec3s_5_4_3`) loads instead of failing with
  "Failed to read root background value".
- [x] **Vec3 negate** — `tvdb__negate_value` negates the three components for
  vec3 types, used to derive `inactive_val0 = -background` on signed-flood-
  filled vec3 level sets.
- [x] **Half-precision empty-node read** — `tvdb__read_mask_values` now
  matches OpenVDB's `HalfReader::read` early-return: when `is_half &&
  read_count == 0` no blosc size header is read. Without this, every
  all-inactive half-precision internal node drifted 8 bytes and exploded
  downstream.
- [x] **Root background propagation** — `tvdb__read_root_topology` builds a
  local `child_params` with the just-read `root->background` and passes it
  into the recursive descent. Previously every internal-tile inactive value
  came back as 0 because the caller-supplied `params.background` was still
  zero-initialised when child topology started.
- [x] **PointDataGrid (`ptdataidx32_*`) recognition** — `tvdb__parse_grid_type`
  maps the prefix to `INT32` for topology parsing, and `tvdb__read_grid`
  detects any grid type containing `ptdataidx` and seeks to
  `end_byte_offset` after topology, so the embedded `AttributeSet` blob does
  not misalign subsequent grids.

## Writer fixes (already landed)

- [x] **Interleaved grid layout** — `tvdb_write_to_memory` now emits each grid
  as `[descriptor][grid data]` immediately, instead of writing all
  descriptors up front and grid data after. OpenVDB and tinyvdb's own
  reader both expect the interleaved form; the old layout corrupted every
  multi-grid file. Single-grid files happened to work and hid the bug.
- [x] **Uncompressed-fallback sentinel** — when blosc/zip cannot shrink a
  block, the writer used to emit `-1` as the size header. OpenVDB's
  `bloscFromStream` interprets `numCompressedBytes <= 0` as
  "uncompressed of length `-numCompressedBytes`", so `-1` is read as
  "expected 0-byte chunk, got 1-byte chunk" and throws. The writer now
  emits `-(int64_t)total_size`, matching openvdb's `bloscToStream`. Fixed
  in all three (BLOSC, system zlib, miniz) fallback branches.
- [x] **Zero-length sentinel** — for `total_size == 0` the writer used to
  emit `-1` (same problem). It now emits `0`, matching openvdb.
- [x] **Half-precision write empty-node guard** — mirror of the read-side
  fix. When `is_half && write_count == 0`, `tvdb__write_mask_values` skips
  `tvdb__compress_and_write` entirely so we don't emit a header that
  `HalfWriter::write` never would have written.
- [x] **`MASK_AND_NO_INACTIVE_VALS` selection-mask convention** — the
  writer's analysis swaps `inactive_val0/val1` to put the "special" value
  first for storage, but the reader has a fixed convention for that flag
  (`val0 = -bg, val1 = +bg`). The local swap silently flipped the meaning
  and turned interior tiles into +bg on round-trip. The writer now re-pins
  `val0 = -bg, val1 = +bg` for that flag and the mask-build loop tests
  only `v == inactive_val1` (no longer ORed with `bg_bytes`, which was
  marking every cell ON for the no-inactive-vals case).
- [x] **Vec3 value writer** — `tvdb__sw_write_value` emits VEC3I/F/D as
  three components. Without this the root background of a vec3 grid was
  silently skipped, the stream went out of alignment, and subsequent
  reads saw "0 children" — dropping the entire tree.
- [x] **Vec3 inactive value negate on write** — already covered by the
  vec3 negate read fix; the writer's analysis loop now sees the right
  bytes for the `-background` comparison.

## Verified round-trips

All checked bit-exact through libopenvdb's `pyopenvdb`:

| file | grids | type(s) | result |
| --- | --- | --- | --- |
| `suzanne.vdb` | 1 | `Tree_float_5_4_3` (fog volume) | bit-exact |
| `fire.vdb` | 2 | `Tree_float_5_4_3` density + temperature | bit-exact |
| `explosion.vdb` | 3 | `Tree_float_5_4_3` density+temperature, `Tree_vec3s_5_4_3` velocity | bit-exact |
| `bunny_half.vdb` | 1 | `Tree_float_5_4_3` (level set, `save_float_as_half=true`) | within 1 ULP at half precision (lossless modulo half quantisation) |

## Open tasks

### Easy / medium

- [ ] **Audit scalar writer paths for `BOOL` / `INT32` / `INT64` / `DOUBLE`
      grids.** None of the test files exercise them, but the per-type code
      paths in `tvdb__sw_write_value`, `tvdb__compress_and_write`, and
      `tvdb__write_mask_values` should be smoke-tested by writing a
      synthesized grid of each type and reading it back through openvdb.
      Risk: low (the leaf buffer write path is type-agnostic).

- [ ] **Compression flag preservation across grids.** When tinyvdb writes a
      multi-grid file via `tvdb_file_save`, the same `compression_flags`
      argument is applied to every grid, so per-grid compression mode (e.g.
      one grid blosc, another zip-only) is not preserved. Either thread a
      per-grid flag, or document the limitation.

- [ ] **`AffineMap` transform write path.** The reader parses an
      `AffineMap` into `xform->matrix[4][4]` and extracts translation, but
      the writer side has not been audited or exercised for affine
      transforms. All current test fixtures use `UniformScaleTranslate`.

- [ ] **Reader: integrate-and-test with delayed-load metadata grids.** The
      `__delayedload` metadata key shows up on every Houdini-written file;
      tinyvdb currently treats it as type `0` and skips the body
      (handled in the metadata loop), but a regression test would be nice.

- [ ] **`tvdb_value_type_size(BOOL) = 1`** is an over-approximation; openvdb
      packs bool grids bit-per-voxel. tinyvdb's read/write of bool leaves
      may need a dedicated path, otherwise mask-compressed bool round-trips
      will be wrong. Untested.

- [ ] **Public regression suite for openvdb interop.** Add a CI job that
      reads each `examples/data/*.vdb`, writes it back via `tvdb_file_save`,
      and re-reads with openvdb (or `vdb_print` from the openvdb source
      tree) to confirm topology + value parity. Would have caught every
      bug in the "Writer fixes" list above.

### Larger features

- [ ] **PointDataGrid (`Tree_ptdataidx32_*`) attribute set parser.**
      tinyvdb currently recognises the type, parses topology, and seeks
      past the leaf buffer (the serialised `AttributeSet`). Reading the
      actual point data (positions, per-point attributes, codecs) requires
      implementing OpenVDB's `AttributeSet`, `AttributeArray` codecs
      (`UnitVec`, `FixedPointCodec`, `TruncateCodec`, group attribute
      handling, etc.) and `PointDataLeafNode` serialisation. Substantial
      work. Until then, point grids are **topology-only** in tinyvdb.

- [ ] **MeshToVolume / mesh → SDF voxeliser.** Useful as a builder API so
      callers can convert a triangle mesh to a level set / fog grid
      without depending on libopenvdb. Out of scope for the current I/O
      library, but would round out the package.

- [ ] **`MultiPassIO` ≥ v224.** The reader currently doesn't handle the
      `numPasses` prefix that openvdb's `Grid::readBuffers` reads for
      grids with `hasMultiPassIO()`. In practice only PointDataGrid hits
      this path so it is moot until the AttributeSet work above lands,
      but worth noting.

- [ ] **Half-precision file format prior to v225.** Files written by very
      old openvdb releases (`file_version < 225`) with a separate
      `is_saved_as_half_float` per-grid metadata flag may exhibit a
      slightly different leaf buffer layout. The current fix has been
      tested only against v225+ half files re-saved by current openvdb.
      Older v223/v224 half files re-written by Houdini have not been
      checked end-to-end.

## Notes for downstream consumers

- After applying the writer fixes above, any tinyvdb-produced VDB should
  open in DCCs that use libopenvdb (Houdini, Blender, Maya, Hydra). If you
  hit a "blosc decompression failed" or "expected an N-byte uncompressed
  chunk" message from openvdb, the most likely culprit is the
  `total_size` sentinel on the write side — verify you have all four
  fixes from the "Writer fixes" section.

- For the lightgeom_gui debug-roundtrip flow: the current
  `tvdb_file_save` reuses the file-level compression flags from grid 0
  and re-emits the data uncompressed if blosc cannot shrink it, so the
  output file may be larger than the input. Bit-exact data round-trip is
  preserved (verified above).
