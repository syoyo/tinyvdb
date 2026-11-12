# Formalization and verification status

Scope and phase plan: `../plan-lean.md`. This file records what is **proven**,
what is deliberately partial, and the findings raised against the C code.

Toolchain: Lean `v4.35.0`, mathlib `v4.35.0`. Build gate: `lake build`
(`warningAsError` on). `sorry` count in landed modules: **0**.

## Landed modules

| Module | Contents |
| --- | --- |
| `Vdb/Bytes.lean` | Total little-endian readers (`getU8?`, `getU16LE`, `getU32LE`, `getU64LE`, `getI32LE`, `getI64LE`, `getF32Bits`, `getF64Bits`), `Emit` difference lists, `pushBytes`, round trips for every width, in-bounds lemmas (`getU32LE_ibounds`, `getU64LE_ibounds`), push/append read lemmas (`getU8?_push`, `getU8?_pushBytes_add`, `getU8?_append_left/right`, `getU32LE_append_left/right'`, `getU64LE_append_left/right'`, `getU8?_nested`), extract/append lemmas. |
| `Vdb/Value.lean` | The ten `ValueType`s with on-disk sizes matching `tvdb_value_type_size`, tree-name and metadata-name tables matching the C `strcmp` chains, half-grid component/element-size rules (`tvdb__half_components`), `VoxelValue` (raw bit patterns) and `MetaValue`. |
| `Vdb/Mask.lean` | `nodeSlots L = 2^(3L)`, serialized byte counts for `L = 3/4/5` (64/512/4096), `NodeMask L = Vector Bool (2^(3L))`, bit accessors, `popCount`, `rank` (C `tvdb_tree_mask_rank`), `rank 0 = 0`, `rank (nodeSlots L) = popCount`, `rank ≤ popCount`, byte-serialization definitions (`byteAt`, `serialize`, `parse`). |
| `Vdb/Coord.lean` | `Coord`, box membership, `Layout` + `WellFormed` (root level 0, depth 3–8, per-level `log2dim` bound, total ≤ 31), `spanShift`/`span`, `localIndex` (arithmetic shift), non-negativity and `< 2^L` bounds, `origin + span * localIndex ≤ c`, `slotOf`, `childOrigin`, `rootKey` with floor-division bounds. |
| `Vdb/Layout.lean` | `Tree_<type>_<L...>` strict parser and printer, the lenient reader model (`parseGridTypeLenient`), `GridType.WellFormed`, checked parse of `Tree_float_5_4_3`. |

## Theorem inventory (landed)

| Theorem | Statement |
| --- | --- |
| `getU16LE_putU16LE`, `getU32LE_putU32LE`, `getU64LE_putU64LE` | reading a just-written scalar returns it |
| `getI32LE_putI32LE`, `getI64LE_putI64LE` | signed round trips |
| `getF32Bits_putF32Bits`, `getF64Bits_putF64Bits` | float bit-pattern round trips |
| `getU8?_pushBytes_add` | reading `pushBytes bs acc` at `acc.size + k` is `bs[k]?` |
| `pushBytes_size` | emitted length is `acc.size + bs.length` |
| `getU8?_append_left/right`, `getU8?_append_right'`, `getU8?_nested` | append-offset arithmetic used by all parse/emit proofs |
| `getU32LE_append_left/right'`, `getU64LE_append_left/right'` | same for 4/8-byte fields |
| `extract_append_size_head`, `extract_append_right_eq`, `foldl_append_eq_foldr` | extract/fold plumbing for nested parsers |
| `getU32LE_ibounds`, `getU64LE_ibounds` | successful reads imply the field lies in the buffer |
| `List.count_take_le` | a prefix never has more set bits than the whole list |
| `NodeMask.rank_zero`, `NodeMask.rank_full`, `NodeMask.rank_le_popCount` | rank/count invariants |
| `nodeSlots_three`, `nodeMaskBytes_three/four/five` | 512 slots, 64/512/4096 mask bytes |
| `localIndex_nonneg`, `localIndex_lt`, `origin_add_localIndex` | arithmetic-shift local index bounds |
| `rootKey_le`, `lt_rootKey_add`, `rootKey_dvd` | root key is the floor-multiple box containing the coordinate |
| `slotOf_lt` | in-range components give a slot below `2^(3L)` |
| `slotOf_inj` | the slot map is injective on the node box (x, then y, then z recovered) |
| `slotOf_localOfSlot` | `slotOf` of a slot's components is the slot |
| `localOfSlot_slotOf` | component extraction is a two-sided inverse of `slotOf` on the node box |
| `Layout.standard_wf`, `float543_wellFormed`, `parseGridType_float543` | the standard `5_4_3` float layout parses and validates |

Test-level checks: `parseGridType "Tree_float_5_4_3" = some float543` is proven
by `decide`.

## Explicitly not yet done (next increments)

1. **Mask byte round trip** (`parse (serialize m) = m` slot-wise, all `L`):
   definitions exist, proof is the next target. This closes the topology byte
   layer together with the readers.
2. **Tree model** (`Root`/`Internal`/`Leaf` with well-formedness matching
   `validate_node`), semantics (`lookup`) and `lookup_eq_treeFind`.
4. **Mask compression** (the 7 `NO_MASK_*` codes) `encode`/`decode` round trip.
5. **Half float** bit model (`halfToFloat`, trunc vs round-to-nearest).
6. **Header/metadata/transform/chunk/grid/file** parse + emit + file round trip.
7. **Oracle harness**: `VdbCheck`/`VdbGen` executables, C dump program,
   differential scripts (`vdb-diff`).
8. Phase P2–P4 (level sets, MC/DMC, mesh→volume).

## Findings awaiting model confirmation

These are hypotheses from the C survey (details in `../plan-lean.md` §0.2).
Each is confirmed or refuted by the corresponding Lean model, then fixed in C
(or documented). None is resolved yet.

| ID | Hypothesis |
| --- | --- |
| F1 | scalar `tvdb__float_to_half` truncates, flushes subnormal to 0, maps NaN→Inf; F16C path rounds, so SIMD/scalar writers differ |
| F2 | `tvdb_header_t.half_precision` never set by the reader |
| F3 | no maximum file-version check; `block_byte_offset` unvalidated; writer duplicates `grid_byte_offset` |
| F4 | grid-type grammar accepts trailing junk as zero levels |
| F5 | `log2dim ≤ 10` allows huge internal allocations before byte-count checks; tree read not bounded by `end_byte_offset` |
| F6 | half grid with `read_count == 0` reads no chunk header; non-half reads 8 bytes |
| F7 | bool-leaf writer emits `node->origin` (zeros for reader-produced trees) |
| F8 | instance grids are not resolved from the parent (stay empty) |
| F9 | `tvdb_grid_to_nanovdb` trusts `child_indices`/node types |
| F10 | classic MC table may not be crack-free on ambiguous faces |
| F11 | dense mesh→SDF sign uses the closest face normal (not pseudonormals) |
| F12 | dense CSG silences dimension/origin/voxel-size mismatches |
| F13 | `tvdb_gradient` boundary divides the clamped difference by `2h` |
