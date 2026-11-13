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
| `Vdb/GridHeader.lean` | the grid body prefix: per-grid compression flags (v222+), the metadata list and the transform, with total emit/parse. `Canonical` bundles the metadata-list bounds and the transform's well-formedness. |
| `Vdb/File.lean` | a full `.vdb` file: the prologue and the interleaved grid entries. `FileGrid.descriptorAt` derives the descriptor's `gridOffset`/`blockOffset`/`endOffset` from the emitted position and the body size; `VdbFile.emitFrom` folds the grids; `VdbFile.parseFrom` follows the descriptor offsets like the C reader. |
| `Vdb/File.lean` (proof support) | `FileGrid.totalSize`/`bytesAt`, `gridsChunksAt`/`gridsBytesAt`, and `emitGrids_acc` (`emitGrids gs acc = acc ++ gridsBytesAt gs acc.size`); descriptor canonical/offset lemmas (`descriptorAt_canonical`, `gridOffset_toNat`, `endOffset_toNat`, `desc_prefix_size`). These are the pieces of the `VdbFile.parseFrom_emitFrom` induction. |
| `VdbFile.parseFrom_emitFrom`, `VdbFile.parse_emit` | **full-file round trip (any number of grids)**: a canonical `VdbFile` parses back to itself from its emitted bytes, composing `FilePrefix.parseFromChunks` and the multi-grid `parseGrids_emit` |
| `VdbFile.parseFrom_emitFrom_single`, `VdbFile.parse_emit_single` | single-grid specialisation (kept as the simpler statement) |
| `parseGrids_emit` | **multi-grid sequence round trip**: any list of emitted grids parses back to itself from `concatChunks (acc :: gridsChunksAt gs acc.size)` at the exact end offset (induction over the list, composing `parseGrid_one`'s steps with the tail hypothesis) |
| `parseGrid_one` | **single-grid sequence round trip**: `parseGrids` parses one emitted grid (descriptor + body) back to `[g]` at the exact end offset, composing the descriptor parse, `GridBody.parseFromChunks` and the trivial tail |
| `Vdb/Topology.lean` | the tree data inside a grid body: the tree-base buffer count and the root node topology (background, tile/child counts, tiles). Roots with children and the internal/leaf records are rejected/unmodelled for now. |
| `parseTile_emit`, `parseTiles_emit` | **root-tile round trips**: one tile (`i32` origin, full-width value, active byte) and any tile list parse back exactly, with the following tiles as trailing bytes |
| `RootTopo.parseFrom_emitFrom` | **root-topology round trip**: background, tile/child counts (`i32`→`u32` count check, children must be 0) and the tile list parse back to the node |
| `TreeData.parseFrom_emitFrom` | **tree-data round trip**: the tree-base buffer count (`i32` = 1) + root topology parse back to the tree |
| `RootTopo.parseFrom_emitFrom_empty` | the empty-root specialisation (background + zero counts) |
| `Vdb/GridBody5.lean` | a grid body with a fully structured tree: header + `TreeData5` topology + the buffer pass (`TreeData5.fullChunks`). `Canonical` bundles the header, tree and buffer well-formedness (`BufMatch`). This supersedes the opaque `GridBody.tree : Bytes` for the 5/4/3 layout. |
| `GridBody5.parseFrom_emit` | **structured grid-body round trip**: header, tree topology and buffers parse back exactly |
| `Vdb/TreeBuffer.lean` | the tree buffer pass: `LeafBuffer` (value mask again + compressed value record), the leaf-buffer list, per-node buffer flattening (`Node4.bufferChunks`), the level-5 child-buffer list (`Child5Buffers`) and the whole tree payload (`TreeData5.fullChunks` = topology chunks ++ buffers). Internal nodes carry no buffer of their own, so the blob is the depth-first flattening of the leaf buffers. |
| `LeafBuffer.parseFrom_emitFrom`, `parseLeafBuffers_emit` | leaf-buffer and leaf-buffer-list round trips |
| `Node4.parseBuffers_emit`, `parseChild5Buffers_emit`, `Node5.parseBuffers_emit`, `parseChildRootBuffers_emit`, `RootNode.parseBuffers_emit` | level-4 node, level-5 node, root child list and root buffer round trips (`BufMatch`/`BufMatchRoot` tie the nested list lengths to the topology child counts) |
| `TreeData5.parseFull_emit` | **full tree payload round trip**: topology parse followed by the buffer parse at its end offset; the grid body's tree region is `TreeData5.fullChunks` |
| `Vdb/TreeNode.lean` | node topology for the standard `Tree_float_5_4_3` layout: `LeafNode` (log2dim 3, value mask), `Child4` (leaf slot, **no serialized origin** — the origin is implicit in the child-mask slot index), `Node4` (log2dim 4: masks + `ValueRecord` + leaves), `Child5` (`Node4` slot, **no serialized origin**), `Node5` (log2dim 5: masks + `ValueRecord` + `Child5`s), `ChildRoot` (origin + `Node5`) and `RootNode` (tiles + `ChildRoot`s). Only the root's children carry explicit `i32 x3` origins, matching `tvdb__read_root_topology` versus `tvdb__read_internal_topology`. The value-chunk size is a parameter (it depends on compression flags/value size/active count). |
| `LeafNode.parseFrom_emitFrom`, `Child4.parseFrom_emitFrom` | leaf and level-4 child-slot round trips (the slot is just the leaf: internal children have no origins) |
| `Node5.parseFrom_emitFrom`, `Child5.parseFrom_emitFrom`, `Child5.parseMany_emit`, `ChildRoot.parseFrom_emitFrom`, `ChildRoot.parseMany_emit` | level-5 internal node, its child slots and the root's child slots (the full root → L5 → L4 → leaf topology) |
| `Child4.parseMany_emit` | **child-slot list round trip**: a list of child slots parses back with the following siblings as trailing bytes |
| `Child5.parseFrom_emitFrom`, `Child5.parseMany_emit` | level-5 child slot (just the level-4 subtree) and its list round trip |
| `RootNode.parseFrom_emitFrom` | **root node round trip**: background, tile count, child count, the tile list (reusing `parseTiles_emit`) and the level-5 child subtrees (reusing `Child5.parseMany_emit`) |
| `TreeData5.parseFrom_emitFrom` | **full tree-data round trip for the 5/4/3 layout**: tree-base buffer count (`i32` = 1) + root with tiles and children (internal level 4, leaves) |
| `Node4.parseFrom_emitFrom` | **level-4 internal-node topology round trip**: child mask, value mask, compressed value record and the recursive child list, with the child count derived from the child mask (`children.length = popCount childMask`) |
| `Vdb/NodeRecord.lean` | per-node value records: the `MaskCompress` code byte, the inactive values (full width), the selection mask, and the value chunk (`tvdb__read_mask_values` / `tvdb__write_mask_values`). `ValueRecord.WellFormed` pins the fields each code carries and the stored-payload size. |
| `parseNat_append/left/chunk`, `parseNat_chunk_serialize` | reading a serialized `NodeMask` at a chunk boundary (prefix size in, exact mask out) |
| `MaskCode.flag`, `MaskCode.ofNat?_flag` | the wire code byte and its decoder inverse |
| `ValueRecord.parseFrom_emitFrom` | **mask-compression record round trip**: for every code 0–6 the record (code byte, optional `val0`/`val1`, optional selection mask, raw value chunk) parses back exactly, with the exact end offset |
| `Vdb/ValueCount.lean` | the stored-value count rule (`tvdb__read_mask_values`): every slot for the all-values code / non-mask-compressed grids / pre-222 files, the value mask's active count otherwise (`storedCount`, `storedCount_le`), and `ValueRecord.parseFromCount` which derives the value-chunk size from the code instead of an external `expected`. |
| `Vdb/TreeDerived.lean` | the tree parsers with the value-chunk size derived from the mask/code (`storedCount`): `Node4/Node5/Child5/ChildRoot/RootNode/TreeData5/GridBody5` and the buffer pass (`LeafBuffer`, `parseLeafBuffers`, node/root buffers) count variants, all with their round trips. `WellFormedCount`/`CanonicalCount` carry `record.stored.size = storedCount … * elemSize`, so `GridBody5.parseFromCount` needs only `elemSize`, the active-mask flag and the file version. |
| `Vdb/GlobalSurface.lean` | global dual-surface assembly: `IxQuad` (a quad by vertex *indices*), `ixSurfaceEdges`, `IxWatertight` (every directed index edge appears with its reverse) and **`watertight_of_ix`** — a combinatorially watertight index mesh is watertight under *any* vertex placement (`IxQuad.mem_edges_of_mem_map_edges`/`mem_map_edges_of_mem_edges` handle the collisions). `boxFaces` is the six outward faces of the unit box, `boxFaces_ixWatertight` verifies it exhaustively over the 64 corner pairs, and `watertight_box` places it anywhere. The DMC assembly therefore reduces to establishing the primal edge/face pairing. |
| `Vdb/Reconstruct.lean` | planar reconstruction (the composition half of the operators) over exact `Q3 = Fin 3 → ℚ`: `dot`, `planeF` (the rational plane field), `dot_lerpQ`/`planeF_lerpQ` (affine under edge interpolation), **`planeF_crossing`** and **`planeF_cube_crossings`** (a marching-cubes crossing of a plane sampled at the cube corners lands exactly on the plane), `triWeight` with `triWeight_sum`/`triWeight_moment`, and **`trilinear_planeF`**/**`trilinear_planeF_offset`** (trilinear interpolation of the corner values reproduces the plane field at every point of any cube). **`plane_level_set_rebuild`** bundles both: for a grid sampling a linear field, both halves of the rebuild composition are exact. The dual-vertex bridge: `fin3_sum_list_sum`, `dot_avgQ` (the inner product commutes with the average) and `planeF_avgQ` (a nonempty list of plane points averages onto the plane), giving **`planeF_dualVertex`** — the DMC dual vertex of a sampled plane lies exactly on the plane. |
| `Vdb/DualSurface.lean` | the dual (DMC) surface as an oriented quad complex: `Quad` (four vertices in cyclic order) with oriented `edges`, `Quad.reverse`, `surfaceEdges`, and `Watertight` (every oriented edge appears with its reverse). Lemmas: `Quad.mem_reverse_edges` (reversal swaps every edge orientation), `watertight_nil`, `watertight_append`, `watertight_pair` (a quad plus its reverse cancels). The local stencil `EdgeStencil` of the four cubes around a crossed primal edge: `quad`, `rotate`, `reverse`, with `mem_rotate_edges` (the starting cube does not matter), `mem_reverse_edges` (walking from the opposite side reverses the edges) and **`adjacent_quads_watertight`** — the two descriptions of the edge's quad cancel, the local watertightness condition. |
| `Vdb/MeshDistance.lean` | mesh-to-volume geometry: `segDist` (the inf-distance to a segment), `segDist_abs_sub_le`/`segDist_isSDF` (1-Lipschitz), `segDist_exists_nearest` (a nearest segment point is attained — the segment is compact and the space proper), and the capsule field `sdfCapsule = segDist - r` with `sdfCapsule_isSDF`, `sdfCapsule_zero_iff` (the capsule surface is the set at distance `r`) and `sdfCapsule_exact`. Plus `IsSDF.min`: the pointwise minimum of two signed distance fields is one. **Finite meshes**: `meshSet` (the union of a finite set of segments), `isCompact_meshSet` (finite union of compact segments), `meshDist` (its inf-distance) with `meshDist_abs_sub_le`/`meshDist_isSDF` and `meshDist_exists_nearest` (attainment), and the mesh band field `sdfMesh = meshDist - r` with `sdfMesh_isSDF` and `sdfMesh_zero_iff`. **Triangles**: `triangleSet` (the convex hull of three vertices), `isCompact_triangleSet`, `triangleDist` with `triangleDist_abs_sub_le`/`triangleDist_isSDF`, `triangleDist_exists_nearest`, and the triangle band field `sdfTriangle` with `sdfTriangle_isSDF`/`sdfTriangle_zero_iff`. **Zero sets**: `segDist_eq_zero_iff`, `meshDist_eq_zero_iff` and `triangleDist_eq_zero_iff` (the distance field vanishes exactly on the segment/triangle/mesh, since those are compact hence closed), with the matching `*_pos_iff_notMem` forms. **Field algebra**: `IsSDF.sub_const` (adding a constant keeps a signed field) and `IsSDF.max` (the intersection of two surfaces is again a signed field), next to the existing `IsSDF.min` (union). |
| `Vdb/DualVertex.lean` | DMC vertex placement over `ℚ³`: `cornerPos` (the 0/1 corner positions), `lerpQ`, `crossing` (the edge crossing point at `edgeParam`), `avgQ`, and `dualVertex` (the average of the crossed-edge crossings). Theorems: `cornerPos_zero_or_one`, `crossing_eq` (a crossing is the convex combination of its edge endpoints), `crossing_mem` (a crossing with parameter in [0,1] stays in the unit cube), `avgQ_mem` and `dualVertex_mem_cube` (the dual vertex lies in the unit cube, i.e. the convex hull of the eight corner positions), plus the `Cube.dualEdges`/`Cube.dualVertex` packaging with `Cube.dualVertex_mem_cube` under the sign-change hypothesis. **Existence**: `cubeEdges` is the closed 12-edge list, `Cube.signs` the corner sign pattern, and `cube_signs_connected` proves the cube's corner graph connected (adjacent agreement forces unanimity, by exhaustive `decide`); hence `Cube.dualEdges_ne_nil_of_mixed` (a cube with both an inside and an outside corner has a crossed edge) and, with `edgeCrosses_signs` (a crossing of nonzero values is one negative and one positive endpoint) and `Cube.dualVertex_mem_cube_of_mixed`, every mixed cube has an in-cube dual vertex. |
| `Vdb/MarchingCubes.lean` | the marching-cubes sign rule: `isInside` (negative), `Face` (four cyclic corner values, diagonals `(a,c)`/`(b,d)`), `Face.Ambiguous` (checkerboard), the **consistent face rule** `negConnected` (negative diagonal iff the face mean is negative), its invariance under all dihedral symmetries (`negConnected_all_symmetries`), sign-flip behaviour, all-inside/all-outside non-ambiguity, the opposite-diagonal lemma, and the symmetric edge-crossing test `edgeCrosses_comm`. Also the linear edge interpolation (`lerp`, `edgeParam`): the crossing parameter is the zero of the linear edge (`lerp_zero`), independent of which endpoint the edge is walked from (`edgeParam_symm`), and lies strictly inside the edge for a sign change (`edgeParam_mem_Ioo`); and the cube classification (`Cube`, its 12 edges, `crossedEdges`) with the edge-count bound, the all-inside/all-outside empty classifications and the membership characterization. **DMC face connectivity**: `Face.edges`/`crossedEdges`, `ambiguous_iff_crossed` (an ambiguous face has all four boundary edges crossed), the even-parity of the boundary crossing count, exactly 4 crossings for an ambiguous face and 0/2 otherwise, and the **face quad consistency** (`FaceQuad`, `Face.quad`, `Face.quad_rev`): the quad (the four boundary edges as unordered pairs plus the rule's diagonal) is identical when the face is seen from the neighbouring cube. |
| `Vdb/LevelSet.lean` (band) | `activeSet f band = {p | |f p| < band}`, `insideSet`/`outsideSet`/`surface`, their disjointness/cover (`surface_subset_compl`), `surface ⊆ activeSet`, and the sphere band as a shell (`sdfSphere_activeSet_eq = {r - band < |p| < r + band}`) with its ball bound. **Exact distance**: `planeProject` (the orthogonal projection onto the plane), `planeProject_mem`, `planeProject_dist` (the projection is at distance `|sdfPlane|`), the lower bound `sdfPlane_abs_le_dist` for every plane point, and `sdfPlane_exact` combining them: the unit-normal plane field is the exact distance to the plane (a mesh-to-volume primitive). **Sphere exactness**: `sdfSphere_exact` exhibits a nearest sphere point attaining `|sdfSphere|` (scaling `p`, or a fixed unit vector at the origin), so the sphere field is also the exact distance to the sphere. **Level sets of SDFs**: `IsSDF.isClosed_levelSet` (a level set is closed), `IsSDF.abs_sub_le_dist_of_level` and `IsSDF.abs_sub_le_infDist` (`|f p - c|` bounds the distance to every level-set point, hence the infimum distance) and `IsSDF.exists_nearest_levelSet` (the nearest level-set point is attained, from closedness in the proper space). |
| `Vdb/LevelSet.lean` | the geometry layer for the operators: `Point` (ℝ³), `levelSet f c` (the zero/surface set), `IsSDF` (1-Lipschitz scalar field, the definition of a signed *distance* field). Fields: sphere `sdfSphere`, plane `sdfPlane` (unit normal) and the Chebyshev box `sdfBox` (`max_i (|p_i| - h_i)`, exact sign test, L∞ magnitude). |
| `IsSDF.continuous`, `IsSDF.abs_le_dist_of_eq` | a 1-Lipschitz field is continuous, and `|f p| ≤ dist p q` for every surface point `q`: the lower half of "the field is the distance to the surface" |
| `sdfSphere_zero_iff/neg_iff/pos_iff`, `sdfSphere_isSDF`, `sdfSphere_levelSet` | the sphere field's zero/negative/positive sets, its 1-Lipschitz property, and `levelSet = {p | ‖p‖ = r}` |
| `sdfPlane_zero_iff`, `sdfPlane_isSDF`, `sdfPlane_levelSet` | the plane field (unit normal): zero set `⟪n,p⟫ = d`, 1-Lipschitz via Cauchy–Schwarz |
| `sdfBox_le_zero_iff`, `sdfBox_isSDF`, `abs_coord_le_dist` | the box field: `sdfBox ≤ 0 ↔ |p_i| ≤ h_i` for all three axes, and 1-Lipschitz (coordinate bound + `max` difference) |
| `Vdb/Stable.lean` | read stability under a trailing append (`getU8?`, `getBytes?`, `getU32LE`, `getU64LE`, `getI32LE`, `getI64LE`, `getString?`): a successful read is unchanged when bytes follow, which lets a record parser be reused inside a larger file. |
| `Vdb/GridDescriptor.lean` | grid descriptors: unique name, grid type, instance-parent name, then the grid/block/end byte offsets. Emit follows the writer (always emits the instance-parent string); parse follows the reader (reads it for version ≥ 221). `Canonical` bounds the three strings. |
| `Vdb/Chunk.lean` | node-buffer chunk framing: the `i64` size word, raw payloads (`-N` then `N` bytes, `-N` must equal the expected count, `0` for an empty payload) and compressed payloads (`+N` then `N` codec bytes). The codec is a parameter; the framing around it is proven. |
| `Vdb/Chunks.lean` | fixed-layout chunk chains (`concatChunks`, append/size lemmas, and field reads at chunk boundaries for u8/u16/u32/u64/i64/blobs), used by the header and available to the transform and grid body. |
| `Vdb/Meta.lean` | metadata entries: the ten type names, `MetaEntry` (name, type name, value), `WellFormed` (value agrees with the name; raw only for unknown names), wire chunks, total emit/parse (count is the caller's list length), and the typed/raw value decoder with the exact width checks. `WellFormed` splits into `TypeOK` (value agrees with the name; a raw value additionally requires the name to be neither a known type nor `string`, since the reader tests `string` first) and `SizesOK` (name, type name and payload lengths fit `u32`/`i32`). The reader dispatches on `MetaKind.ofName?` (a single `match`, like the transform), so the per-kind proofs do not have to reason about type-name if-chains; `getI32LE_chunk` and the other chunk reads are in place for the entry round trips. |
| `Vdb/Transform.lean` | grid transforms: double-bit-pattern `Vec3d` with a proven 24-byte round trip, the six map kinds and their names, emitted field chunks (derived inverse fields recomputed from the scale), total emit/parse, and `WellFormed` for the fields the reader does not store. |
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
| `putU8_size` … `putI64LE_size` | emitted sizes of every scalar writer, so read offsets are known to `simp`/`omega` |
| `getBytes?_append`, `getBytes?_prefix`, `getBytes?_putBytes`, `getString?_putString`, `getString?_putString_append`, `putString_size` | string/blob wire round trips and emitted sizes, including reads with trailing bytes |
| `concatChunks_append`, `concatChunks_size`, `concatChunks_append_map`, `concatChunks_triple`, `concatChunks_snoc_size`, `concatChunks_append_size`, `concatChunks_cons_size`, `concatChunks_nil_size`, `acc_append_concatChunks`, `getU8?_chunk` … `getBytes?_chunk`, `getString?_chunk` | chunk-chain algebra and boundary reads, including VDB strings |
| `Header.parseFromChunks` | **header round trip with trailing bytes**: the header composes with the file metadata/list and later data |
| `Header.parseFrom_emitFrom` | **header round trip**: every canonical header parses back unchanged from its emitted bytes, with the legacy compression byte present only for versions 220–221 |
| `Vec3d.ofBytes_toBytes`, `Vec3d.toBytes_size`, `Vec3d.parseAt_toBytes`, `parseVecChain_emit` | 24-byte double-vector round trips and the vector-chain parser inverse |
| `TransformKind.ofName?`, `ofName_uniformScale` … `ofName_affine` | map-name lookup and its six `native_decide` characterisations |
| `Transform.parseFrom_emitFrom_uniformScale/scale/uniformScaleTranslate/scaleTranslate/translation/affine` | per-kind transform round trips (name string + the kind's vector chain or 128-byte affine block) |
| `parseValue_bool/int32/int64/f32/f64/vec3i/vec3f/vec3d`, `parseRaw` | the typed value decoders: size chunk, negative-count rejection, exact-width check, then the value chunks |
| `MetaEntry.parseFrom_emitFrom_bool/int32/int64/f32/f64/vec3i/vec3f/vec3d/str/raw` | **per-kind metadata round trips**: name string, type name, value chunks; raw entries carry an `i32` byte count and opaque bytes |
| `MetaKind.ofName?_eq_none` | an unknown (non-`string`, non-known) type name has no `MetaKind`, which is what selects the raw decoder |
| `MetaEntry.parseFrom_emitFrom` | **metadata round trip**: every well-formed entry parses back unchanged from the bytes it emits (`TypeOK` selects the kind, `SizesOK` discharges the length hypotheses). The per-kind lemmas also return the exact end offset (`acc.size + sum of chunk sizes`), which the list framing needs. |
| `GridHeader.parseFromChunks`, `GridHeader.parseFromChunks_exact`, `GridHeader.parseFrom_emitFrom_exact` | the grid header parses with trailing bytes and returns its exact end offset, which the tree-base read needs |
| `GridBody.parseFrom_emitFrom` | **grid-body round trip**: header + tree-base count + opaque tree bytes in `[off, endOff)` parse back to the body with the exact end offset |
| `Transform.parseFrom_emitFrom_rest_exact`, `Transform.parseFrom_emitFrom_exact` | exact end offsets for the transform (per-kind and general), needed to chain the tree-base read |
| `GridHeader.parseFromChunks` | **grid-header round trip with trailing bytes**: flags + metadata list + transform compose with the tree data that follows |
| `FilePrefix.parseFromChunks` | **file prologue with trailing bytes**: header + file metadata + grid count parse with grid data following, at exact offsets |
| `GridBody.parseFromChunks` | **grid body with trailing bytes**: the body parses with following grids after its tree data, at the exact end offset |
| `FilePrefix.parseFrom_emitFrom` | **file prologue round trip**: header + file metadata + grid count parse back unchanged, composing `Header.parseFromChunks` with `MetaList.parseFromChunks` |
| `GridHeader.parseFrom_emitFrom` | **grid-header round trip**: flags + metadata list + transform parse back to the header (the metadata list is composed via `MetaList.parseFromChunks`; the transform contributes its own existential end offset) |
| `GridDescriptor.parseFrom_append` | a descriptor parse is unchanged by trailing bytes (the stability lemmas plus `split`/`simp_all`), so descriptors can be read from the middle of a file |
| `GridDescriptor.parseFrom_emitFrom` | **grid-descriptor round trip** for file version ≥ 221: name/type/instance-parent strings plus the three `u64` offsets parse back to the descriptor, with the exact end offset |
| `Chunk.parse_raw`, `Chunk.parse_compressed` | **chunk framing round trips**: a raw chunk returns its payload and a compressed chunk returns the codec's expansion, both with the exact end offset |
| `MetaList`, `parseEntries`, `MetaList.parseFrom` | metadata-list wire model: `i32` count (C bounds `0..4096`), then that many entries. |
| `MetaEntry.parseFromChunks_bool/…/raw`, `MetaEntry.parseFromChunks` | **entry round trip with trailing bytes**: an entry followed by the rest of the list still parses to itself and its end offset. This is what makes the list induction go through. |
| `parseEntries_emit`, `MetaList.parseFrom_emitFrom` | **metadata-list round trip**: a list of well-formed entries with length ≤ 4096 parses back unchanged (count chunk, then every entry), with the exact end offset. |
| `MetaList.parseFromChunks` | the same round trip with arbitrary chunk prefix _and trailing chunk list_, which is what lets the grid body compose the metadata list with the transform and tree data |
| `Transform.parseFrom_emitFrom_rest` | **transform round trip with trailing bytes** (per-kind `_rest` lemmas compose `parseVecChain_emit` with `post := rest`) |
| `Transform.parseFrom_emitFrom` | **transform round trip**: every well-formed transform parses back unchanged; the proof canonicalises the fields the reader does not store and applies the per-kind lemma |
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

## Differential harness: tree structure

`VdbCheck` (Lean model) and `vdbdump` (C reader) are compared on the 13 sample
files by `lean/scripts/diff_vdbdump.py`. Beyond the prologue, descriptors and
grid-body header, the harness now parses the **structured tree** with
`TreeData5.parseFullCount` and compares it against the C reader:

* `Root: N tiles, M children` — root tile and child counts;
* `Nodes: T total (I internal, L leaf)` — node counts (the C reader counts the
  root as total-only, so `I + L + 1 = T`);
* `Active voxels` — the sum of the leaf value-mask popcounts, compared through
  the C reader's `format_count` rendering;
* the tree pass must end exactly at the descriptor's `endOffset`
  (`tree end=… expected=… ok=true`).

The value payload is decoded by a codec stub: the structural pass only needs
the chunk framing (the `i64` size word), which is part of the model. Raw chunks
(`-N`) still have `N` checked against the derived `storedCount * elemSize`, so
a wrong value-count rule is caught.

Coverage: the non-half `5_4_3` grids (sphere, suzanne, sphere-div1,
bunny_bgcolor, bunny_cloud, the float grid of explosion) are checked node for
node. Half grids and `ptdataidx32` grids are reported as `tree unsupported`:
half grids hit finding **F6** (no chunk header when the active count is zero,
which the current `ValueRecord` framing does not yet branch on), and
point-index leaves append an index-count payload the tree model does not cover.
The model fix that this harness forced: internal-node children carry **no**
serialized origins (only the root's children do); the earlier model wrote and
read `i32 x3` origins at every level, which never matched a real file.

## Explicitly not yet done (next increments)

1. **Indexed lookup equivalence**: prove the spec `lookup` equals the C
   `tree_find`/accessor model (root hash map, per-level slot descent, rank
   compaction).
2. **Mask compression vs. the C writer**: the model now proves the
   round trip; the next step is a differential check that `classify` picks the
   same code/`val0`/`val1`/selection as `tvdb__write_mask_values` (needed for
   byte-identical output, not for correctness).
3. **Half float** bit model (`halfToFloat`, trunc vs round-to-nearest).
4. **Metadata round trip** (typed entries, strings and raw blobs), then the
   transform, chunk framing, grid body and the file round trip.
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
| F6 | **confirmed** by the tree differential harness: half grids whose node has `read_count == 0` carry no chunk header at all, while non-half grids carry the `i64` size word. The sample half files fail at the first zero-count internal node when parsed with the non-half framing, so the harness reports those grids as `tree unsupported`; this is the remaining record-framing gap. |
| F7 | bool-leaf writer emits `node->origin` (zeros for reader-produced trees) |
| F8 | instance grids are not resolved from the parent (stay empty) |
| F9 | `tvdb_grid_to_nanovdb` trusts `child_indices`/node types |
| F10 | classic MC table may not be crack-free on ambiguous faces |
| F11 | dense mesh→SDF sign uses the closest face normal (not pseudonormals) |
| F12 | dense CSG silences dimension/origin/voxel-size mismatches |
| F13 | `tvdb_gradient` boundary divides the clamped difference by `2h` |
