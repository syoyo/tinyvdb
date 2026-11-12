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
| `Vdb/Mask.lean` | `nodeSlots L = 2^(3L)`, serialized byte counts for `L = 3/4/5` (64/512/4096), `NodeMask L = Nat` (low `2^(3L)` bits are the slots), bit accessor, `popCount`, `rank` (C `tvdb_tree_mask_rank`), `rank 0 = 0`, `rank (i+1) = rank i + bit i`, `rank (nodeSlots L) = popCount`, `rank ≤ index`, base-256 byte serialization (`serializeNat`, `parseNat`) and the full round trip. |
| `Vdb/Coord.lean` | `Coord`, box membership, `Layout` + `WellFormed` (root level 0, depth 3–8, per-level `log2dim` bound, total ≤ 31), `spanShift`/`span`, `localIndex` (arithmetic shift), non-negativity and `< 2^L` bounds, `origin + span * localIndex ≤ c`, `slotOf`, `childOrigin`, `rootKey` with floor-division bounds. |
| `Vdb/Tree.lean` | sparse tree model (`Node` leaf/internal, `Root` tiles/children, `Tree` with layout), node slot and child-origin geometry, total `lookup` semantics (root key → tile/child → node descent) with fuel `t.depth`, `Equiv`, and the well-formedness predicate `WellFormed`/`NodeWFuel` mirroring `validate_node`; a worked `5_4_3` tree with three checked lookups. |
| `Vdb/MaskCompress.lean` | the seven `MaskCompress` codes as `MaskCode`, code byte round trip, `readCount`, `VoxelValue.negate` (bit flip for floats, integer negation, bool identity), the `decodeSlot`/`decodeAll` decoder (active values by rank, code 6 reads the full list), the faithful encoder `classify` (unique-inactive scan seeded with the background, `val0`/`val1`, selection mask, including the background swap), the selection-mask semantics, the scan invariant, and the **general mask-compression round trip** for all seven codes. |
| `Vdb/Header.lean` | the string/blob wire primitives (`putBytes`/`getBytes?`, `putString`/`getString?`) with round trips, and the file header: magic, version range, library version, grid-offset flag, the 220–221 legacy compression byte, 36-byte UUID, with `Header.Canonical` and total emit/parse definitions. |
| `Vdb/Half.lean` | binary16 model: the exact reader bit pattern (`halfToFloatBits`, including the subnormal normalisation loop), the truncating scalar encoder (`floatToHalfTrunc`), the round-to-nearest-even encoder (`floatToHalfRNE`, as used by F16C and OpenVDB), and concrete F1 evidence. |
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
| `NodeMask.rank_zero`, `NodeMask.rank_succ`, `NodeMask.rank_full`, `NodeMask.rank_le_index` | rank/count invariants |
| `paddedDigits_length`, `ofDigits_paddedDigits`, `serializeNat_size` | base-256 digit padding is length `n` and still evaluates to the mask |
| `nodeMaskBytes_three/four/five`, `nodeSlots_three` | 512 slots; 64/512/4096 mask bytes |
| `parseNat_serializeNat`, `NodeMask.parse_serialize` | **mask byte round trip**: any mask below `2^(3L)` serializes to `nodeMaskBytes L` bytes and parses back unchanged |
| `nodeSlots_three`, `nodeMaskBytes_three/four/five` | 512 slots, 64/512/4096 mask bytes |
| `localIndex_nonneg`, `localIndex_lt`, `origin_add_localIndex` | arithmetic-shift local index bounds |
| `rootKey_le`, `lt_rootKey_add`, `rootKey_dvd` | root key is the floor-multiple box containing the coordinate |
| `slotOf_lt` | in-range components give a slot below `2^(3L)` |
| `slotOf_inj` | the slot map is injective on the node box (x, then y, then z recovered) |
| `slotOf_localOfSlot` | `slotOf` of a slot's components is the slot |
| `localOfSlot_slotOf` | component extraction is a two-sided inverse of `slotOf` on the node box |
| `Layout.standard_wf`, `float543_wellFormed`, `parseGridType_float543` | the standard `5_4_3` float layout parses and validates |
| `pushBytes_eq_append` | `pushBytes bs acc = acc ++ pushBytes bs empty` (exposes every emitter as an append chain) |
| `getBytes?_append`, `getBytes?_putBytes`, `getString?_putString`, `putString_size` | string/blob wire round trips and emitted sizes |
| `nodeSlot_lt` | an in-box coordinate gives a slot below `2^(3L)` |
| `exampleTree_lookup_origin/inactive/background` | the worked tree reads the active voxel, an inactive stored value, and the background correctly (checked by `decide`) |
| `lookup_outside_children` | no root child and no root tile means the background, inactive |
| `NodeMask.rank_mono`, `getElem?_setBits_rank` | rank is monotone; the value-mask compaction order maps the `k`-th stored value to the `k`-th set slot |
| `MaskCode.ofNat?_toNat`, `readCount_le` | code byte round trip and stored-value count bound |
| `VoxelValue.type_negate`, `negate_negate_float/double/bool` | negation preserves the type and is an involution for float/bool values |
| `decodeSlot_active`, `decodeSlot_active_stored` | an active slot decodes from the compacted list; with `active = map values (setBits mask n)` it returns exactly `values i` |
| `floatToHalfTrunc_nan`, `floatToHalfRNE_nan` | **F1 evidence**: the truncating encoder maps NaN to Inf; the RNE encoder keeps NaN |
| `trunc_vs_rne_differ`, `floatToHalfTrunc_tiny_flush`, `..._negzero` | truncation vs rounding on a concrete mantissa, subnormal flush, signed-zero preservation |
| `floatToHalfTrunc_halfToFloat_normal`, `floatToHalfRNE_halfToFloat_normal`, `floatToHalfRNE_halfToFloat_subnormal` | every normal half round trips through both encoders; subnormal halves round trip through RNE (checked over all 65536 halves) |
| `mem_inactiveSlots`, `inactiveValues_eq_bg` | inactive slot membership and constant-background inactive lists |
| `fold_const_bg`, `scan_uniform` | the unique-value scan stays at count ≤ 1 with `u0 = bg` for a constant background |
| `classify_uniform`, `classify_uniform_decode` | mask-compression round trip for a constant-background inactive set (code 0) |
| `foldl_cond_eq_foldl_filter`, `testBit_foldl_lor`, `selectionOf_bit` | the selection mask is exactly the OR of single-bit shifts of the matching slots, so its bit `i` is set iff `values i = val1` |
| `selectionOf_bit_of_eq/of_ne`, `mem_inactiveSlots`, `inactiveValues_eq_bg` | selection-bit corollaries and inactive-slot membership |
| `Scan.Inv`, `Scan.inv_zero`, `Scan.step_inv`, `Scan.fold_inv`, `scanValues_inv` | the unique-inactive-value scan keeps every seen value within `{u0}` (count 1) or `{u0, u1}` (count 2), with `u0 ≠ u1` at count 2 |
| `decodeAll_active` | an active slot decodes to its stored value for every code (code 6 reads the full per-slot list, others by rank) |
| `classify_decode` | **general mask-compression round trip**: for every background, value function, mask and node size, the classified node decodes to the original value on every slot, covering codes 0–6, all inactive-value combinations and the background swap |

Test-level checks: `parseGridType "Tree_float_5_4_3" = some float543` is proven
by `decide`.

## Explicitly not yet done (next increments)

1. **Indexed lookup equivalence**: prove the spec `lookup` equals the C
   `tree_find`/accessor model (root hash map, per-level slot descent, rank
   compaction).
2. **Mask compression vs. the C writer**: the model now proves the
   round trip; the next step is a differential check that `classify` picks the
   same code/`val0`/`val1`/selection as `tvdb__write_mask_values` (needed for
   byte-identical output, not for correctness).
3. **Half float** bit model (`halfToFloat`, trunc vs round-to-nearest).
4. **Header round trip** (`Header.parse_emit` for canonical headers) and then
   metadata, transform, chunk framing, grid body and the file round trip.
5. **Oracle harness**: `VdbCheck`/`VdbGen` executables, C dump program,
   differential scripts (`vdb-diff`).
6. Phase P2–P4 (level sets, MC/DMC, mesh→volume).

## Findings awaiting model confirmation

These are hypotheses from the C survey (details in `../plan-lean.md` §0.2).
Each is confirmed or refuted by the corresponding Lean model, then fixed in C
(or documented). None is resolved yet.

| ID | Hypothesis |
| --- | --- |
| F1 | **confirmed and fixed** in C: the scalar encoder truncates, flushes to 0 and maps NaN→Inf while F16C rounds. The scalar path now implements round-to-nearest-even with NaN preservation (matching the Lean `floatToHalfRNE` and OpenVDB); `tests/test_half_rounding.c` fails on the old encoder with `TINYVDB_SIMD=OFF`. |
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
