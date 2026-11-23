# plan-lean.md — Lean 4 formalization and verification of TinyVDB

Target repo: `tinyvdbio` (C11 core, Apache-2.0). Hand-off plan for an implementing
coding agent. Read `AGENTS.md` (repo root) first; its pre-push procedure applies
and **nothing is pushed without explicit authorization**.

Reference precedent: `~/work/tinyexr/lean/` (Lean v4.35.0 + mathlib v4.35.0 at creation; this project now pins v4.36.0,
`warningAsError`, executable oracles `exrcheck`/`exrgen`/`codecgen`, differential
harnesses, `VERIFICATION.md`, `AxiomAudit.lean`). Mirror its layout, gates and
conventions; do not copy EXR-specific code.

---

## 0. Goals, non-goals, ground truth

### Goals
1. **VDB file format (mandatory, deepest coverage).** A total, executable Lean
   model of the OpenVDB `.vdb` byte format as accepted/emitted by TinyVDB
   (`src/tinyvdb_io.h`), with an abstract sparse-grid semantics, decoder,
   encoder, and proven round-trip theorems; plus a differential oracle against
   the C reader/writer.
2. **Frequently used volume ops** — specs over ℝ, executable reference models,
   proofs of key properties, and differential tests against C:
   - level sets: SDF primitives, CSG, Godunov/fast-sweeping Eikonal solver,
     signed flood fill, trilinear sampling, measures/Euler characteristic;
   - volume → mesh: existing marching cubes (MC) **and** dual marching cubes
     (DMC) — see §0.3;
   - mesh → volume: exact unsigned distance (closest point on triangle, BVH
     pruning), sign (face normal vs. generalized winding number), narrow band.
3. Findings (spec vs. C disagreements) become C fixes with regression tests or
   documented, intentional deviations — never silently tolerated.

### Non-goals
- Proving the C code itself correct (no Frama-C/CN/VST). The Lean model is
  proven; C is checked against it differentially (same philosophy as tinyexr).
- Deflate/zlib, LZ4, zstd internals; Blosc codecs are treated as opaque
  byte-level black boxes (only the framing is modeled).
- GPU (Vulkan/CUDA) kernels — out of scope except as an optional later
  differential target reusing the same vectors.
- IEEE-754 rounding-error analysis of every float op. Proofs are over ℝ/ℚ;
  executable models use `Float`/`Float32`/`ℚ`; C agreement is via bit-exact
  checks where the algorithm is combinatorial and tolerance checks elsewhere.
  (Narrow, explicit exceptions: half-float conversion bit semantics, §2.4.)

### 0.1 Ground truth facts (from code survey; verify line numbers before use)
- Reader+writer: `src/tinyvdb_io.h` (single header impl, compiled by
  `src/tinyvdb_io.c`). `doc/fileformat.md` is a stale stub — do **not** spec from it.
- Tree index/lookup: `src/tinyvdb_tree.c` (`tree_find` ~357–439,
  `tvdb_tree_get` ~460, `validate_node` ~118, root key ~384, slot ~420/450).
- Dense ops: `src/tinyvdb_levelset.c`, `src/tinyvdb_ops.c`,
  `src/tinyvdb_sample.c`, `src/tinyvdb_mesh.c`,
  `src/tinyvdb_mesh_conversion.inl`, `src/tinyvdb_mc_tri_table.h`.
- Tree ops: `src/tinyvdb_sparse_tools.c` (tree MC `tool_mesh` ~1316,
  `tvdb_mesh_to_level_set` ~1891, rebuild ~1545), `src/tinyvdb_winding.c`,
  `src/tinyvdb_sdf_tree.c` (fast sweep ~976, `sdf_eikonal` ~897).
- **Two coordinate conventions**: dense grids are cell-centred
  (`o + (i+0.5)h`, x-fastest storage `(k*ny+j)*nx+i`); sparse trees are
  vertex-centred (`M·(i,j,k,1)`, leaf slot `(x<<2L)|(y<<L)|z`, z-fastest).
  Model both explicitly; never conflate.

### 0.2 Known suspected issues to confirm/deny with the model (seed findings)
Treat each as a hypothesis; record outcome in `lean/VERIFICATION.md`.
- F1 `tvdb__float_to_half` (scalar) truncates, flushes < 2⁻²⁴ to ±0, maps NaN→Inf;
  F16C path rounds-to-nearest → SIMD/scalar writer outputs differ.
- F2 `tvdb_header_t.half_precision` never set by reader.
- F3 No max file version check; `block_byte_offset` never validated; writer
  sets `block_byte_offset = grid_byte_offset` (OpenVDB differs).
- F4 Grid-type grammar is loose (`Tree_float_5_4_3x` yields extra zero levels).
- F5 log2dim ≤ 10 allows ~2^30·vsize allocations before byte-count checks;
  tree read not bounded by grid `end_byte_offset`.
- F6 Half grid with `read_count == 0` reads no chunk header; non-half reads 8 bytes.
- F7 Bool leaf writer emits `node->origin` (zeros for reader-produced trees).
- F8 Instance grids: tree not resolved from parent (stays empty).
- F9 `tvdb_grid_to_nanovdb` trusts `child_indices`/node types unchecked.
- F10 MC: no ambiguity resolution → the Bourke table may not be crack-free
  across ambiguous faces; decide this exhaustively (§4.2).
- F11 Dense mesh→SDF sign uses closest-face normal (not angle-weighted
  pseudonormal) → wrong sign possible near edges/vertices; `sign_method` ignored.
- F12 Dense CSG silently returns on dims mismatch; origin/voxel size unchecked.
- F13 `tvdb_gradient` boundary: clamped neighbour but divisor stays `2h`.

### 0.3 Dual marching cubes — scope decision
TinyVDB currently implements **only classic MC** (dense and tree). DMC is new.
Plan: (a) formalize DMC first as a Lean spec + executable reference with
proofs; (b) lane VS-3 (P6) adds a C implementation
`tvdb_grid_volume_to_mesh_dual` (+ dense variant) validated by the Lean oracle.
P6 is approved and scheduled in parallel with VS-1 (§4.1, §11.3).

---

## 1. Repository layout and tooling

```
lean/
  lean-toolchain            leanprover/lean4:v4.36.0   (upgraded from v4.35.0)
  lakefile.lean             package vdbSpec; mathlib @ v4.36.0; warningAsError
  lake-manifest.json        committed (pins)
  README.md                 modules table, build/validate, axiom profile
  VERIFICATION.md           theorem inventory, boundaries, findings, gate results
  VdbSpec.lean              root import
  AxiomAudit.lean           #print axioms over all exported theorems
  Vdb/Bytes.lean            LE readers/writers, Emit, append/extract lemmas
  Vdb/Half.lean             binary16 ↔ binary32 bit model
  Vdb/Value.lean            ValueType, sizes, Value encoding/decoding
  Vdb/Mask.lean             NodeMask (bitvec of 2^(3L)), popcount, rank, serialization
  Vdb/Coord.lean            Coord = ℤ×ℤ×ℤ (+ Int32 bounds), slots, spans, origins
  Vdb/Tree.lean             abstract tree (root map, internal, leaf), WellFormed
  Vdb/Semantics.lean        tree ↦ (Coord → Value × Bool), background, tiles
  Vdb/Layout.lean           grid-type grammar "Tree_<vt>_<L1>_..._<Ln>"
  Vdb/Meta.lean             metadata entries, typed + raw
  Vdb/Transform.lean        map kinds, matrix semantics, invertibility
  Vdb/MaskCompress.lean     7 per-node codes: classify / encode / decode
  Vdb/Chunk.lean            compression framing (i64 n; raw/negative; opaque codec)
  Vdb/Header.lean           magic, versions, UUID, legacy compression byte
  Vdb/Grid.lean             descriptor, grid body (flags, meta, xform, topo, buffers)
  Vdb/Parse.lean            total decoder File → Except Error VdbFile
  Vdb/Emit.lean             encoder VdbFile → ByteArray
  Vdb/Roundtrip.lean        decode∘encode theorems
  Vdb/Canon.lean            canonical dump (for differential compare)
  Ops/Real.lean             shared ℝ³ geometry, Lipschitz, dist lemmas
  Ops/Dense.lean            dense grid model (cell-centred, x-fastest)
  Ops/Sample.lean           trilinear / triquadratic, clamp semantics
  Ops/Sdf.lean              sphere/box/torus/capsule/platonic SDFs
  Ops/Csg.lean              min/max/difference semantics
  Ops/Eikonal.lean          Godunov local solver
  Ops/FastSweep.lean        sweep orderings, monotonicity, fixed point
  Ops/FloodFill.lean        signed flood fill (6-connectivity)
  Ops/Measure.lean          voxel volume, staircase area, χ of cube complex
  Mesh/Types.lean           TriMesh/QuadMesh, edges, orientation
  Mesh/McTable.lean         256×16 tri table + edge table as data (generated from C)
  Mesh/MarchingCubes.lean   MC cell classification, interpolation, welding
  Mesh/DualMC.lean          dual MC (surface-nets + Nielson DMC)
  Mesh/Closed.lean          mod-2 / oriented boundary, watertightness, Euler χ
  Mesh/Triangle.lean        closest point on triangle (Ericson regions)
  Mesh/Bvh.lean             AABB lower bound, pruning soundness
  Mesh/Winding.lean         solid angle (Van Oosterom–Strackee), winding sums
  Mesh/MeshToVolume.lean    unsigned distance, sign rules, narrow band
  VdbCheck.lean             exe: parse .vdb → canonical JSON verdict
  VdbGen.lean               exe: seeded well-formed .vdb generator
  OpsGen.lean               exe: op test vectors (SDF, sweep, MC, DMC, mesh→SDF)
tests/lean_diff/
  vdb_dump.c                C: tvdb_* reader → same canonical JSON
  ops_dump.c                C: run ops on vectors → canonical output
  run_vdb_diff.sh           lean vs C (and OpenVDB if available) on corpus+gen
  run_ops_diff.sh           ops vectors compare (bit-exact / tolerance per op)
```

- Add `lean/.lake/` and generated vectors dir to `.gitignore`. Generated
  `.vdb` files are already ignored (`*.vdb`); keep generated corpora under a
  build dir (`mktemp -d`), never tracked.
- CMake: new option `TINYVDB_BUILD_LEAN_DIFF` (default OFF) builds
  `vdb_dump`/`ops_dump` and registers CTest entries that call the shell scripts;
  scripts exit **77** if `lake`/built exes are missing (skip ≠ pass).
- `Mesh/McTable.lean` is generated by a small script
  (`scripts/gen_lean_mc_table.py`) from `src/tinyvdb_mc_tri_table.h` and
  `MC_EDGE_TABLE` in `src/tinyvdb_mesh.c`; a CTest checks the Lean copy is in
  sync (diff of regenerated output) so the proven table is the shipped table.
- Gates (shell-scripted, also documented in `lean/README.md`):
  - `lean-check`: `cd lean && lake exe cache get && lake build`
  - `lean-axioms`: `lake env lean AxiomAudit.lean` → only
    `propext, Classical.choice, Quot.sound` (+ explicitly listed
    `Lean.ofReduceBool` for `native_decide` self-checks; count them)
  - `lean-sorry`: grep first-party `sorry`/`admit` = 0
  - `vdb-diff`, `ops-diff`: 0 disagreements (or every disagreement mapped to a
    recorded finding with a decision)
- License header on every new file: Apache-2.0 SPDX (match repo), not BSD.

### Lean conventions
- Total functions; parsers return `Except VdbError α` with error kinds that map
  1:1 to `tvdb_status_t` (`INVALID_HEADER`, `UNSUPPORTED_VERSION`, …).
- Byte input = `ByteArray`; proofs on `List UInt8` views where easier, with
  bridging lemmas.
- No `sorry`. `native_decide` only in generator self-checks and exhaustive
  table checks where `decide` is infeasible; each usage listed in VERIFICATION.md.
  Prefer `decide` / `bv_decide` for 256-case table facts.
- Reals: `Real`/`EuclideanSpace ℝ (Fin 3)` for specs; executable twins use `ℚ`
  (proof-friendly, exact) or `Float` (differential only). Each executable
  function over `ℚ` gets a lemma `toReal (f_q x) = f_ℝ (toReal x)` where exact.

---

## 2. Phase P1 — VDB file format (mandatory core)

### 2.1 Abstract data model (`Vdb/Coord`, `Vdb/Mask`, `Vdb/Tree`, `Vdb/Semantics`)
- `Layout := { levels : List ℕ // 3 ≤ length ≤ 8, root level 0, each Lᵢ ∈ [0,10] }`;
  standard `[0,5,4,3]`. Derived `shift i = Σ_{j>i} L_j`, `span i = 2^(shift i + L_i)`.
- `NodeMask L := BitVec (2^(3L))` with `popcount`, `rank` (child compaction,
  matches `tvdb_tree_mask_rank`), serialization `bit i ↔ byte[i>>3] bit (i&7)`.
- Slot function `slot L shiftBelow (c - origin) = (x<<2L)|(y<<L)|z` with local
  index `(cᵢ - oᵢ) >> shiftBelow`. **Theorem** `slot_bij`: on the node's box it is
  a bijection onto `Fin (2^(3L))`; `childOrigin` inverse lemma.
- Root key `floor(c / span1) * span1` (Int floor division); lemma: `c` lies in
  the box of its root key; keys of distinct boxes distinct.
- `Tree V` inductive: `Root (background : V) (tiles : Finmap Key (V × Bool))
  (children : Finmap Key Internal)`; `Internal L` with child mask, value mask,
  `values : Fin (2^(3L)) → V`, children indexed by rank; `Leaf` with value mask
  and `Fin 512 → V` (generic `2^(3L)`).
- `WellFormed` = exactly the C `validate_node` + root checks:
  child∩value masks = ∅; no padding bits; #children = popcount childMask;
  root origins multiple of span1, in Int32, no duplicates, tiles/children keys
  disjoint; depth = layout length.
- Semantics `lookup : Tree V → Coord → V × Bool` (value, active) — spec version
  by structural descent; **theorem** `lookup_eq_treeFind`: the executable
  hashed/indexed lookup (model of `tree_find`, including the node cache of
  `tvdb_tree_accessor_get`) equals spec lookup.
- `activeSet t : Finset Coord` and `denote t : Coord → V × Bool`; equivalence
  `t ≈ u ↔ denote t = denote u` (extensional), used in round-trip statements
  where the encoder may canonicalize.

### 2.2 Value types and layouts (`Vdb/Value`, `Vdb/Layout`)
- `ValueType` = bool, int32, int64, float, double, half, vec3i, vec3f, vec3d,
  string; sizes per `tvdb_value_type_size`. Prefix map for grid type names:
  `float double int32 int64 bool mask(→bool) vec3s(→vec3f) vec3d vec3i
  ptidx32(→int32) ptdataidx32(→int32)`.
- `parseGridType : String → Except _ (ValueType × Layout × Flags)` — **strict
  spec grammar** plus a `parseGridTypeC` modelling the loose C behaviour (F4);
  theorem: they agree on all strings accepted by the strict grammar; generate
  counterexamples for the difference.
- `_HalfFloat` suffix handling; `\x1e` unique-name split.

### 2.3 Bytes, metadata, transform, header (`Vdb/Bytes`, `Meta`, `Transform`, `Header`)
- LE `getU8/U32/I32/I64/U64/F32bits/F64bits` + writers, round trips, append
  lemmas (port the pattern of `tinyexr/lean/Exr/Bytes.lean`).
- String = `u32 len ++ bytes`, reject embedded NUL; round trip.
- Header: magic `0x56444220` as i64; `file_version ≥ 220` (model **both** the C
  policy "no upper bound" and a spec policy "≤ 224/225"; F3); major/minor;
  `has_grid_offsets` (0 ⇒ UNIMPLEMENTED); legacy compression byte iff
  `220 ≤ v < 222` (nonzero ⇒ ZIP|ACTIVE_MASK); 36-byte UUID.
- Metadata: count ∈ [0,4096]; typed entries (`bool float double int32 int64
  vec3i vec3d vec3s string`) with exact-size checks; unknown → raw bytes.
- Transform: `UniformScaleMap|ScaleMap` (5×vec3d), `…ScaleTranslateMap`
  (6×vec3d, translation first), `TranslationMap`, `AffineMap` (16×f64,
  stored transposed). Spec matrix `indexToWorld : Map → Matrix (Fin 4) (Fin 4) ℝ`;
  theorems: affine last row; scale maps invertible iff all scales ≠ 0;
  writer recomputes inverse fields (lemma: recomputed fields are functions of
  scale/voxelSize; reading back gives same `indexToWorld`).

### 2.4 Half floats (`Vdb/Half`)
- Bit-level model: `halfToFloat : UInt16 → UInt32` (exact; subnormals, Inf, NaN)
  and two encoders: `floatToHalfTrunc` (scalar C) and `floatToHalfRNE` (F16C).
- Theorems: `halfToFloat` injective on non-NaN; `floatToHalfX (halfToFloat h) = h`
  for both encoders (exactly representable values round trip); characterize the
  set where Trunc ≠ RNE (→ F1 evidence); NaN handling lemma showing Trunc maps NaN to Inf
  (finding F1 decision: fix C to preserve NaN + pick one rounding mode, or document).
- Validate exhaustively over all 2^16 halves via `OpsGen`/`VdbGen` vectors vs C.

### 2.5 Mask compression (`Vdb/MaskCompress`) — central theorem target
- Codes 0–6 exactly as table in §0.1 survey (`NO_MASK_OR_INACTIVE_VALS` …
  `NO_MASK_AND_ALL_VALS`), with semantics of `val0/val1/selection mask`,
  `read_count = popcount(valueMask)` iff ACTIVE_MASK ∧ code ≠ 6 ∧ v ≥ 222.
- `classify (bg) (values) (valueMask) : Code × Option V × Option V × Option Mask`
  modelling `tvdb__write_mask_values` (bytewise equality, swap so `val1 = bg`,
  half rounding of inactive values).
- `decodeNode (encodeNode …)` theorem: for every value array and value mask,
  decoding the encoded node yields the original values on **all** slots
  (active and inactive), under the precondition that values are compared by
  bit pattern (so −0/+0 and NaN payloads preserved). For half grids: equality
  after `half∘float` rounding of active values, inactive exact.
- Legacy v<222 path: `num_values = 2^(3L) − popcount(childMask)` with scatter
  back; theorem scatter∘gather = id on non-child slots, child slots ↦ bg.
- Characterize F6 (half, read_count = 0) and decide spec intent.

### 2.6 Chunk framing (`Vdb/Chunk`)
- `i64 n`: `n ≤ 0` ⇒ `−n` raw bytes, must equal `elem*count`; `n > 0` ⇒ `n`
  compressed bytes ≤ remaining, decompressed size must equal expected.
- Codecs abstract: `structure Codec where decompress : ByteArray → ℕ → Option ByteArray`
  with axiom-free *hypothesis* `RoundTrip codec` used as a theorem premise (not
  a Lean `axiom`). Raw/uncompressed path proven unconditionally.
- Blosc header model (16-byte blosc1 / 32-byte blosc2): fields, `nbytes`
  equality, shuffle flag, bitshuffle rejected; byte-shuffle permutation and its
  inverse proven (`unshuffle ∘ shuffle = id`).
- Writer policy: zero-length ⇒ `0`; incompressible ⇒ `−N` raw. Lemma: emitted
  chunk size ≤ 8 + N.

### 2.7 Topology/buffers, grid, file (`Vdb/Grid`, `Parse`, `Emit`, `Roundtrip`)
- Root topology: background (full width even for half), tile/child counts with
  the C bound `tiles*(12+vsize+1) + children*12 ≤ remaining`; tiles; children
  recursive. Internal: child mask, value mask, compressed values, children by
  slot order. Leaf topology pass (mask) + buffer pass (mask again; v<222 origin +
  numBuffers; values). Bool/mask leaves; PointIndex leaf payload; PointData blob.
- Descriptor: unique name, grid type, instance parent (v ≥ 221), 3×u64 offsets;
  `grid ≤ end ≤ fileLen`; interleaved `[desc][grid]…`.
- `parseFile : ByteArray → Except VdbError VdbFile` — total, fuel-free
  (structural on remaining length; termination proven).
- **Bounds theorems**: every read is within `[0, len)`; recursion depth ≤
  layout length; all allocation sizes ≤ `c · remaining` *after* fixing F5
  (state the theorem for the spec policy; show counterexample for current C).
- `emitFile : VdbFile → ByteArray` modelling `tvdb_write_to_memory`.
- **Main theorems**:
  - `T-FILE-RT`: `WellFormed f → parseFile (emitFile f) = .ok (canon f)` where
    `canon` captures writer canonicalization (version ≥ 222 → 224 rule, UUID,
    `is_saved_as_half_float` metadata insertion, buffer count 1, transform
    inverse recomputation, `block_byte_offset`).
  - `T-SEM-RT`: `denote (parse (emit f)).grid i = denote f.grid i` for all
    non-half grids; half grids equal after `roundHalf` on active float values.
  - `T-EMIT-PARSE-WF`: parse output is always `WellFormed` (decoder never
    yields an invalid tree).
  - `T-PREFIX`: grid parse is independent of bytes outside `[grid, end)`
    (requires F5 fix; otherwise record as counterexample).
- Version coverage: 220, 221, 222, 223, 224 for read; 224 for write. Generator
  must emit all 7 mask codes, tiles at every level, active/inactive tiles,
  empty trees, all value types, half grids, multiple grids, instances,
  metadata of each type, every transform kind.

### 2.8 Executables + differential oracle
- `vdbcheck <file>`: JSON `{status, version, grids:[{name,type,half,xform,
  meta, background, active:[[i,j,k,valuebits]...] sorted, tiles:[…], hash}]}`.
  Sorted, bit-pattern values → bit-exact comparability.
- `vdbgen <out> <seed> <kind>`: well-formed files; `native_decide` self-checks
  that `parseFile (emitFile f) = ok (canon f)` for a fixed seed set.
- `tests/lean_diff/vdb_dump.c`: same JSON from `tvdb_file_open_memory` +
  `tvdb_read_all_grids` + tree lookup over active set.
- `run_vdb_diff.sh` corpora: (1) vdbgen seeds × kinds (≥ 2000 files);
  (2) `data/sphere-div1.vdb`, `data/sphere-div2.vdb`; (3)
  `data/reference/ref_*.vdb` if present (generated by
  `scripts/gen_openvdb_reference.cc`, skip if absent); (4) C-writer outputs
  (C write → Lean parse; Lean emit → C read; C write → C read → compare);
  (5) mutation fuzz: byte flips/truncations of (1) — both must reject, or both
  accept with identical dumps; status codes must match the mapped error kind.
- Optional OpenVDB oracle when `TINYVDB_BUILD_OPENVDB_TESTS=ON`.

### P1 exit criteria
All §2 theorems proven sorry-free; `vdb-diff` 0 unexplained disagreements;
F1–F9 each resolved as "C fixed + regression test" or "documented deviation"
(F1/F3/F7 are fixed in C per §11).

---

## 3. Phase P2 — Level-set ops

### 3.1 Geometry base (`Ops/Real`, `Ops/Dense`, `Ops/Sample`)
- `SignedDistance Ω φ :↔ ∀p, φ p = (if p ∈ closure Ω then −infDist p ∂Ω else infDist p ∂Ω)`
  (choose sign convention matching TinyVDB: negative inside).
- Dense grid model with x-fastest index bijection `idx_bij`; cell-centred
  positions; `tvdb_at` edge clamp.
- Trilinear sampling `v = (w−o)/h − 0.5`, clamp to `[−1, dim−1]`, corner clamp.
  Theorems: interpolates at voxel centres; result ∈ [min, max] of the 8 corners
  (convex combination); Lipschitz in `w` with constant `√3 · maxgrad / h`;
  partition of unity of weights; splat is the adjoint (`⟪sample g w, s⟫ =
  ⟪g, splat w s⟫`) — the adjoint identity is exactly what C autograd relies on.

### 3.2 SDF primitives (`Ops/Sdf`)
- Sphere `|p−c|−r`: theorem exact SDF of ball; 1-Lipschitz.
- Box `|max(q,0)| + min(max qᵢ,0)`: exact SDF of axis box (prove both inside
  and outside cases).
- Torus `√((√(dx²+dz²)−R)²+dy²)−r` (R > r > 0): exact SDF.
- Capsule: exact SDF (distance to segment minus r; clamp parameter lemma).
- Platonic `max_i nᵢ·(p−c) − r·ratio`: theorem: zero set = polytope boundary,
  sign correct, **1-Lipschitz lower bound** of |SDF| (not exact; formalizes the
  documented underestimate).
- Narrow-band clamp `clamp(φ, −bg, bg)` preserves sign and 1-Lipschitz.
- Grid sizing `n = ceil(span/vs)+1`, `origin = lo − 0.5 vs`: theorem the band
  `[lo−…, hi+…]` is covered; overflow guard ⇒ rejection (matches C contract
  "out untouched on failure").

### 3.3 CSG (`Ops/Csg`)
- union=min, intersection=max, difference=max(a,−b) over ℝ: interior sets
  compose as ∪, ∩, \; 1-Lipschitz preserved; result is a *lower bound* of the
  true SDF magnitude outside (classic min/max non-exactness) — state precisely.
- Pointwise ⇒ aliasing-safe theorem (output index i depends only on inputs at i).
- NaN asymmetry of `<`/`>` documented via Float executable model (F12 adjacent).

### 3.4 Eikonal / fast sweeping (`Ops/Eikonal`, `Ops/FastSweep`)
- Local Godunov solver `solve h a b c` with a ≤ b ≤ c (sorted):
  - `T-GOD-EQ`: returned x satisfies `Σᵢ (max(x − aᵢ, 0))² = h²` (discrete
    Eikonal) and is its unique solution with x ≥ a.
  - `T-GOD-DISC`: under each branch precondition the discriminant is ≥ 0 — the
    C `<0` fallbacks are unreachable (both `tvdb__godunov_solve` and the
    algebraically different `sdf_eikonal` form; prove the two formulas equal).
  - Monotone in each argument; `a + h/√3 ≤ x ≤ a + h`.
- Fast sweeping over a finite grid graph with frozen set F:
  - `T-FS-MONO`: values non-increasing per update; `T-FS-SIGN`: sign mask
    unchanged; frozen voxels unchanged.
  - `T-FS-FIX`: any fixed point of all 8 sweeps solves the discrete Eikonal
    system with boundary data F (and values ≥ true min over upwind paths).
  - `T-FS-TERM`: with exact arithmetic over ℚ the iteration reaches the fixed
    point in finitely many sweeps (bounded by #voxels·8 via monotone
    finite-descent argument on the "settled" set, à la Zhao 2005 causality) —
    if full proof is too costly, prove termination of the `max_change ≤ tol`
    loop for `tol > 0` (monotone bounded below) and record the stronger result
    as a stretch.
  - Unreached voxels keep input values (sentinel semantics).
- Tree variant: same theorems over the active-voxel graph with inactive = ∞.

### 3.5 Signed flood fill, measures, topology (`Ops/FloodFill`, `Ops/Measure`)
- Flood fill: result = +band on the 6-connected component(s) of {|v| ≥ band}
  touching the boundary, −band elsewhere among |v| ≥ band, band unchanged.
  Prove via reachability (`Relation.ReflTransGen`) and an executable BFS whose
  output equals the spec.
- Volume = #{v<0}·h³ exact count; staircase area = #{sign-change 6-edges}·h²
  (formalize as count; state it is **not** a consistent estimator — note only).
- Euler characteristic: `χ(cube complex of solid voxels) = V − E + F − C`
  (closed unit cubes); theorems: χ(single cube)=1; inclusion–exclusion
  additivity; χ of union of two disjoint (non-touching) solids adds;
  `tvdb_level_set_euler_characteristic = 2χ` equals χ of the boundary surface
  when the solid is a 3-manifold with boundary — prove the combinatorial
  identity `χ(∂S) = 2χ(S)` for **cubical solids whose boundary is a manifold**
  (stretch; at minimum exhaustive `decide` check on all 2×2×2 configurations
  of the local formula).

### P2 differential tests (`OpsGen` + `ops_dump.c`)
- Primitives: bit-patterned float grids from C vs ℚ/Float Lean evaluation,
  tolerance ≤ 1 ulp-ish (`1e-6` relative) — they are pointwise.
- Godunov: exhaustive random triples incl. degenerate (a=b=c, b=∞, c=∞) —
  compare C double vs Lean ℚ to 1e-12.
- Fast sweeping on small grids (≤ 16³): Lean ℚ fixed point vs C after
  convergence, tolerance 1e-5·h; sign identity exact.
- Flood fill / volume / χ: exact equality.

---

## 4. Voxel-surface workstream (mesh ↔ volume)

This section supersedes the former P3 (volume → mesh), P4 (mesh → volume), P5
(composition) and P6 (C dual MC) phase split. Those phases are consolidated
into one workstream because their theorems and harnesses share the same
lattice, topology and sign machinery. The format work (§2) and level-set ops
(§3) remain the baseline. Findings are still resolved as in §0.3: a model/C
disagreement becomes a C fix with a regression test, or a documented deviation.

### 4.0 Proof budgeting (mandatory for every lane)

- **Proof group** = one commit-sized theorem cluster, normally one
  `lean/Vdb/*.lean` module, so a timeout is attributable to one claim.
- **Cap**: 10 minutes wall-clock per group, measured as
  `cd lean && timeout 600 lake build Vdb.X` (`lake build -v` for per-job
  timing). Harness *runtime* is tracked separately, not under this cap.
- **Lane checkpoint**: after every 10 minutes of accumulated proof effort in
  a lane, re-assess: land, split, fall back, or wall. No lane absorbs
  unbounded time.
- **Fail fast**: start each group with a local `set_option maxHeartbeats
  800000 in` (tune down), so a runaway tactic exits in seconds. Keep
  `warningAsError` and 0 `sorry`.
- **Escalation ladder on timeout** — never land a weakened claim:
  1. Split at the abstraction seam: combinatorics vs. ℝ analysis; per-axis
     and per-case lemmas into separate modules; extract Prop-form witnesses
     before the assembly step (the `DmcOneStitch*` pattern).
  2. Restrict the model: prove the bounded `native_decide` instance first
     (`n=3` exhaustive, `n=4` seeded, all 256 cases) and land it as evidence
     with the general gap named.
  3. Hypothesize the hard step: state the missing lemma as an explicit premise
     (as `band_complete`, `hcover` and `Nodup` already do), prove everything
     downstream of it.
  4. Wall it: after two splits still time out, record statement, attempted
     approach, command and elapsed time in `lean/VERIFICATION.md`, then move
     on. Each group's outcome (pass / split / bounded / wall) gets one ledger
     line with its measured time.

### 4.1 Lane definitions

| Lane | Scope and deliverables | Depends on | Done when |
| --- | --- | --- | --- |
| **VS-0 — Plumbing + ledger** (first) | Wire the Lean harnesses into CTest under `TINYVDB_BUILD_LEAN_DIFF=ON` (exit 77 = skipped when `lake` is absent); fix the 110/104 module tally and F14 row order; refresh the stale publication paragraph after `git fetch` (no push); add the voxel-surface coverage matrix to `VERIFICATION.md` | — | `lake build`, 0 `sorry`, harnesses green, CTest skip list explicit, ledger counts match reality |
| **VS-1 — Mesh→volume differential completeness** (parallel with VS-3) | Sparse/tree mesh→volume harness (seeding, dilation, keep-rule, flood fill, prune; exercises `band_complete_tree` + `signedFill_eq_clamp`); BVH-vs-Lean differential (currently brute force on both sides); degenerate/huge-coordinate corpus for `mesh_triangle_double` (or a loud documented limit); wider winding mesh set (non-convex, genus > 0) | VS-0 | new harnesses pass with negative controls; every untested path either covered or explicitly scoped |
| **VS-2 — DMC closedness / χ** | Global DMC-1 Nodup criterion (consume `badFaceConfig` / `same_pair_badFace`), upgrade Euler to unconditional-given-criterion with F19 as negative witness; `T-DMC1-DUAL` beyond connectivity; DMC-0 genus/χ content | VS-1 vectors for cross-check | theorems proven sorry-free, or a documented boundary after the 10-min/timebox ladder — never a weakened claim |
| **VS-3 — P6 C DMC** (parallel with VS-1) | Implement `tvdb_grid_volume_to_mesh_dual` + dense variant with the existing `_ex` contract (status, output preserved on failure, arena rollback, alias rejection, deterministic across workers); CTest registration; docs + CHANGELOG; C↔Lean MC/DMC mesh harness (topology as index lists, positions tolerance). No GPU port | current Lean vectors: `n=3` exhaustive, `n=4` seeded, cube-local patch table | topology bit-exact vs Lean DMC-1 vectors; C matrix subset green; docs updated. χ claims stay in the conditional (no-repeat) form until VS-2 lands |
| **VS-4a — General angle-weighted sign proof** (promoted from stretch) | General convex-polyhedra soundness of the angle-weighted (Bærentzen–Aanæs) pseudo-normal at closest points, building on `ConeClosed` (`p − q = Σ λᵢ nᵢ`), `NormalCone`, and the F16 instance in `AnglePseudoNormal.lean`. Model result: **no C change implied** (C keeps the max-dot F16 rule) | `ConeClosed`, `AnglePseudoNormal` | theorem proven, or a precise 2D/vertex-figure case plus a documented convex gap |

Ordering: `VS-0 → (VS-1 ∥ VS-3) → (VS-2 ∥ VS-4a)`. Parked walls are unchanged.

### 4.2 Group decomposition (each group ≤ 10 min)

| Lane | Groups (one module each where possible) | Fallback tier |
| --- | --- | --- |
| VS-0 | plumbing/docs only — no proofs | n/a |
| VS-1 | sparse/tree generator twin; keep-rule/feature twin; reuse `signedFill_eq_clamp` + prune lemmas (no new proof); BVH twin; degenerate/huge-coordinate corpus | bounded grids + documented untested fallback |
| VS-3 | **landed**: dense + sparse/tree DMC-0 `_ex` APIs, 256-case patch decomposition parity, and a dense DMC-1 API (QEF vertices + Nielson quads) validated on sphere/torus/box/ripple with watertightness/winding/determinism, a QEF-optimum regression and a shell-pinned padded variant that closes boundary-touching surfaces, and a sparse/tree DMC-1 variant (index-space QEF + unconditional shell pinning), and a C↔Lean topology differential matching six invariants on all 256 shell-pinned fields; remaining: exact index-vector parity (C ordering/placement differs; not claimed) | C validated against current `n=3`/`n=4` vectors once the comparator lands |
| VS-2 | **2a** per-face bad-config classification; face-pair uniqueness; global Nodup criterion; **2b** Euler under criterion (compose the existing theorem — small); **2c** patch↔vertex bijection, quad↔MC-vertex, incidence preservation, χ equality; **2d** DMC-0 genus content | **2a+2b+2c landed in full**: `Vdb/DmcOneNodupCriterion.lean` proves `mesh_nodup_iff_noBadFace`, `euler_general_dmc1_of_noBadFace` and F19's negative witness; `Vdb/DmcOneDual.lean` proves `mcVertexQuadEquiv`, `patchVertexEquivN`, `mcIncident_iff_dmcIncident` and `chi_dual_eq` for every `n` (cube-local facts machine-checked over 256 cases, global lifting kernel-proof, ~34 s per group). Remaining: 2d genus (needs homology) |
| VS-4a | corner-angle positivity; cone-expansion pairing via `ConeClosed`; **hard seam** — quadratic-form strict positivity for angle-weighted normals (2D vertex figure first); assemble convex theorem | **landed**: general convex theorem conditional on `hface`, unconditional for non-obtuse and two-face planar figures (`AnglePseudoNormal`, ~7 s) and for isosceles three-face vertices (`AngleVertexFigure`, ~24 s); four 10-min groups generalised the algebra (~34 s), proved `sphericalProj_general` off the diagonal hyperplanes (~33 s), and closed those slices by continuity (~29 s); the three-face seam (S) is fully unconditional (`sphericalProj_unconditional`, `three_face_face_pos_unconditional`); arbitrary `n > 3` face figures are conditional on `sphericalBarycenter`, which is proved equivalent to (S) itself (singleton certificate); unconditional simplicial/non-obtuse instances and a non-vacuous `n = 4` fan theorem landed; (S) for general `n` remains walled |

### 4.3 C dual-MC contract (VS-3)

- API follows the existing `_ex` convention: status return + `tvdb_error_t`,
  output preserved on failure, arena rollback, alias rejection, deterministic
  across worker partitions, matching C/CTest conventions in §9.
- Validate topology bit-exactly against the Lean DMC-1 index-quad vectors and
  positions with the existing tolerance; add a CTest entry and gate it with
  `TINYVDB_BUILD_LEAN_DIFF` so a missing Lean toolchain skips (77).
- Update public docs, CHANGELOG and `VERIFICATION.md` coverage matrix.
- GPU port is explicitly out of scope.

### 4.4 Parked walls (not in scope without explicit go-ahead)

Zhao 2005 convergence and the super-solution half of T-FS-FIX; general
Poincaré–Lefschetz / homology; staircase-estimator consistency for general
sets; aggregate Barnes–Hut tree claim; Float IEEE-rounding theorems. The
general convex angle-weighted sign proof (VS-4a) is the one wall promoted
into scope by user decision; its first slice landed a conditional general
theorem plus unconditional non-obtuse and two-face planar cases, leaving only
the obtuse geometric seam (S) walled.

---

## 5. Physics-processing workstream (PH)

This workstream extends the verified model to the geometry needed by a physics
pipeline: **signed distance → part decomposition → collision proxy (simplified
mesh) → contact/manifold queries**. Tet-mesh generation for simulation is a
parked, optional lane. The C code is checked differentially; nothing here is a
proof about the C implementation. User decisions 9–12 in §11 fix the scope.

### 5.0 Scope and C-surface inventory

| Physics stage | C entry points | Lean coverage before PH |
| --- | --- | --- |
| signed distance | `tvdb_level_set_*`, `tvdb_mesh_to_sdf*`, `tvdb_cpt`, `tvdb_level_set_rebuild` | extensive (P1/P2/VS), `cpt` not modelled |
| part decomposition (SDF) | `tvdb_sdf_segmentation`, `tvdb_sdf_extract_enclosed_regions`, `tvdb_level_set_genus` | foundations only (`FloodFill`, `Euler`) |
| collision proxy | *no C API exists* | none (`PhysMesh` foundation added in PH-0) |
| convex decomposition | *no C API exists* | none |
| contact / manifold queries | *no C API exists*; ray helpers `tvdb_voxels_along_ray_dense`, `tvdb_segments_along_ray` | `Bvh`, `MeshDistance`, `WindingNumber` |
| simulation tets (optional) | `tvdb_sdf_to_tet_mesh`, `tvdb_level_set_to_tet_mesh`, graded/refine | none |

### 5.1 Lane definitions

| Lane | Scope and deliverables | Depends on | Done when |
| --- | --- | --- | --- |
| **PH-0 — mesh foundation + ledger** | shared `Vdb/PhysMesh.lean` index-mesh type (positions abstract, oriented triangles), `Watertight`/`Loopless`/`Nodup`, half-edge count and `2·χ = 2V − F`, quad→triangle watertightness bridge; physics coverage matrix in `VERIFICATION.md` | VS lanes | landed (2026-11-23) |
| **PH-1 — SDF gaps + part decomposition (SDF)** | `SdfMask` (fog/interior mask), `Segmentation` (6/26 components, per-part field, cavities), `GenusMeasure` (χ/genus arithmetic under `HasInteriorDuality`), `Cpt` (closest-point projection); differential harness for segmentation/cavities | PH-0 | Lean modules landed; C↔Lean part/cavity harness green with negative controls |
| **PH-2 — collision proxy by simplification (C + Lean)** | new C QEM/edge-collapse `_ex` API (status, output preserved on failure, alias rejection, arena rollback, worker-independent determinism); `Qem`, `EdgeCollapse`, `CollisionProxy` modules and a C↔Lean topology/error differential | PH-0, PH-1 | landed 2026-11-23: contract test + 9-case (V,F) differential; index-vector parity explicitly not claimed |
| **PH-3 — convex decomposition (C + Lean)** | `Convex`, `Sat`, `ConvexDecomp` modules; convex-hull/part proxy API; coverage of the original surface, determinism; SAT/convexity differential | PH-2 | landed 2026-11-23: AABB parts (boxes are convex and proved so), face-partition coverage, 2 cases / 3 parts exact parity; general SAT/hull decomposition remains a planned extension |
| **PH-4 — contact / manifold queries (C + Lean)** | `RayDda`, `RaySdf`, `Contact`, `NarrowPhase`, `Manifold`, `PersistentManifold`; contact = (point, normal, penetration) with orientation/equivariance theorems, broadphase necessity, manifold capacity/covering/determinism; contact differential corpus | PH-2, PH-3 | landed 2026-11-23: contact + manifold core with 3-case differential; ray DDA/SDF-segment twins, broadphase/narrowphase and temporal persistence remain follow-ups |
| **PH-5 — tet meshes for simulation (optional)** | isosurface stuffing: BCC warp, sign-case tables, minimum-key diagonals, watertight outward boundary, positive orientation, determinism; differential against `test_tetmesh` | explicit go-ahead | bounded Lean case-table evidence landed; C warp/float path and full watertightness remain outside the model |

Ordering: `PH-0 → PH-1 → (PH-2 ∥ PH-3) → PH-4`; PH-5 only on explicit
go-ahead. Each proof group obeys §4.0's 10-minute cap and split/bounded/
hypothesize/wall ladder; no weakened or `sorry`-carrying claims are landed.

### 5.2 Interactions with known walls

- The general-n angle-weighted sign seam (S) and topological degree for closed
  meshes (§4.4) are inherited by any mesh→SDF path used to *feed* the part or
  contact pipeline; PH modules state them as explicit premises where needed.
- No Euler–Poincaré/homology in mathlib 4.36: genus/χ duality stays conditional
  on `PoincareLefschetz.HasInteriorDuality` (PH-1).
- Float/Float32 behaviour is differential evidence only; no universal native
  Float theorems are claimed for contact tolerances.
- GPU kernels stay out of scope (§0); CPU paths only.

### 5.3 Validation additions

- New opt-in gates under `TINYVDB_BUILD_LEAN_DIFF`: `check_sdf_parts.sh`
  `check_proxy.sh`, `check_convex_parts.sh`, `check_contact.sh` (landed);
  ray-DDA and SDF-segment gates landed; exit 77 when the Lean toolchain or a C API is absent (skip ≠ pass).
- Any new C API needs a failing regression test first, then the AGENTS.md CPU
  matrix (scalar sanitizer, SIMD+OpenMP at OMP 1/8, clang); GPU only if GPU code
  changes. Docs, CHANGELOG and this ledger are updated with every landing.

## 8. Sequencing, sizing, risks

| Order | Phase | Est. effort | Risk |
|---|---|---|---|
| 1 | Tooling skeleton, Bytes, Mask, Coord, LE/strings | S | low |
| 2 | P1 tree model + semantics + lookup equivalence | M | medium (rank/indices proofs) |
| 3 | P1 MaskCompress + Half + Chunk | M | medium |
| 4 | P1 parse/emit + file round trip + vdbcheck/vdbgen + C diff | L | **high** (writer canonicalization, legacy versions) |
| 5 | MC table theorems + F10 decision | S–M | done |
| 6 | P2 SDF/CSG/sampling/Godunov + harnesses | M | done |
| 7 | P2 fast sweeping + flood fill + χ + harnesses | M–L | done |
| 8 | VS-0 plumbing + ledger | S | landed (this update) |
| 9 | VS-1 mesh→volume differential ∥ VS-3 C DMC | L / M–L | medium–high |
| 10 | VS-2 DMC Nodup/duality/χ ∥ VS-4a angle-weighted signs | L | high (topology/geometry proofs) |

- Each lane: land theorem + executable + differential vectors together;
  checkpoint commits locally; **no push** without authorization.
- Proof timeouts follow the mandatory protocol in §4.0: 10-minute cap per
  proof group, split / bounded instance / explicit hypothesis / documented
  wall. Never land a weakened claim to satisfy a budget.
- Mathlib geometry (`EuclideanSpace`, `Metric.infDist`, `convexHull`) is the
  basis for P2/P4; avoid building custom real analysis.
- Floating point: never claim a Float theorem; label float-level evidence as
  "differential".

## 9. Validation & reporting per phase
1. `lean-check`, `lean-axioms`, `lean-sorry` green.
2. `vdb-diff` / `ops-diff` green (or every diff ↔ finding).
3. For any C fix: regression test first (fails before), then AGENTS.md matrix
   relevant subset: scalar+ASan/UBSan, SIMD+OpenMP (OMP 1 and 8); GPU/fallback
   builds only if GPU-adjacent code changes. Report CTest 77 skips explicitly.
4. Update `lean/VERIFICATION.md` (theorem inventory with statement + file,
   boundaries, findings table F1…Fn with decision) and `lean/README.md`;
   add a short `lean/` section to `AGENTS.md` (build/validate, no-sorry rule,
   oracle philosophy) and a pointer in `README.md`.
5. `git diff --check`; no build products / generated `.vdb` / `.lake` tracked.

## 10. Definition of done — status 2026-11-21

Toolchain: Lean/mathlib **v4.36.0** (upgraded from v4.35.0; `lean/AxiomAudit.lean`
audits 4,729 `Vdb.*` declarations with `collectAxioms`, profile
`propext`/`Classical.choice`/`Quot.sound` + `native_decide`/`bv_decide`
certificates only). 135 Lean modules (128 under `Vdb/`), 0 `sorry`. Final
verified run: `lake build` 18,578 jobs; CTest **89/89** (25 Lean differential
gates + `lean_axioms` + 63 C tests). Out-of-tree runs need
`TINYVDB_BUILD_EXAMPLES=ON` (for `vdbdump`) and
`VDBDUMP=<build>/vdbdump` for `lean_diff`/`lean_diff_vdbgen`. Scalar ASan/UBSan, SIMD+OpenMP (OMP 1/8)
and clang matrices **59/59** each; GPU fallback passes with skips; the
generated-shader GPU leg is unavailable here (no glslangValidator).

- **P1/P2 format + level-set core** — done: T-FILE-RT, T-SEM-RT,
  T-EMIT-PARSE-WF, mask-compression round trip, slot bijection, lookup
  equivalence; exact SDFs, CSG set semantics, Godunov/Eikonal/fast-sweep/flood
  fill, grid sizing. Harnesses (samples, mask, half, Godunov, fill, Euler,
  fast sweep, CSG, MC face) all green.
- **VS-0 plumbing** — done: ~21 opt-in CTest entries with 77 skips, axiom
  gate, coverage matrix, toolchain pin, F1–F19 ledger.
- **VS-1 mesh→volume** — done as verified tiers: tree-path + BVH + BVH-ties
  (148 exact ties explained, 11 disagreements resolved) + double-fallback
  (48/48 exact RNE) + dense/sparse MC topology twin; seed spacing proved
  (`SeedCoverage`), seed stage mirrored bit-exactly. Remaining stages printed
  in an unmirrored banner.
- **VS-2 DMC theory** — done: general-`n` `EdgeClosed`, Nodup criterion, Euler
  under criterion, and full `T-DMC1-DUAL` (both bijections, incidence, χ);
  genus/PL duality remains the documented homology wall.
- **VS-3 C dual MC** — done at DMC-0 dense+tree and staged DMC-1 (QEF +
  shell padding) with contract/topology tests and C↔Lean differential; exact
  index-vector parity intentionally not claimed.
- **VS-4a angle-weighted signs** — three-face (S) unconditional; arbitrary-`n`
  reduced to named `FanCertificate` / spherical flux; non-obtuse and simplicial
  instances unconditional. Full geometric existence is the documented wall.
- **Section A (advanced) walls** — precisely named, not weakened: n-face fan
  existence / spherical Stokes, winding far-point (circular without degree
  theory), genus / Poincaré–Lefschetz (no Euler–Poincaré or cubical bridge even
  in 4.36), Zhao 2005 convergence, universal native-Float32 agreement.
- **Findings F1–F19** resolved; differential gates have 0 unexplained
  disagreements; each budget timeout/wall recorded in `VERIFICATION.md`.
- **PH-0/PH-1 (physics track)** — PH-0 landed: `Vdb/PhysMesh.lean` supplies the
  shared index-mesh type, half-edge/Euler counting and the quad→triangle
  watertightness bridge. PH-1 Lean modules landed: `Vdb/SdfMask.lean`,
  `Vdb/Segmentation.lean`, `Vdb/GenusMeasure.lean`, `Vdb/Cpt.lean`; the C↔Lean
  part/cavity gate is landed (`Vdb/SdfPartsCheck.lean`,
  `lean/scripts/sdf_parts_c.c`, `check_sdf_parts.sh`, CTest
  `lean_diff_sdf_parts`): 24 seeded cases, 24 parts, 4 nonempty cavities, exact
  dump parity. **PH-2 landed** (`Vdb/Qem`, `Vdb/EdgeCollapse`,
  `Vdb/CollisionProxy`, `Vdb/CollisionProxyCheck`, `src/tinyvdb_mesh_simplify.{h,c}`,
  `tests/test_mesh_simplify.c`, `lean_diff_proxy`): contract + 9-case (V,F)
  differential; exact index-vector parity intentionally not claimed, general
  manifold preservation is the bounded `collapse_watertight_fin4` result plus
  the C output closure check. **PH-3 landed** (`Vdb/Convex`, `Vdb/ConvexDecomp`,
  `Vdb/ConvexDecompCheck`, `src/tinyvdb_convex_decomp.{h,c}`,
  `tests/test_convex_decomp.c`, `lean_diff_convex_parts`): shared-vertex union-find
  components with an AABB per part, 2 cases / 3 parts with exact box+label parity.
  **PH-4 landed** (`Vdb/Contact`, `Vdb/Manifold`, `Vdb/ContactCheck`,
  `src/tinyvdb_contact.{h,c}`, `tests/test_contact.c`, `lean_diff_contact`):
  sphere/mesh contacts with a 3-case / 11-contact exact face+count differential.
  Ray-DDA twin and gate landed (4 cases, 30 voxels exact); SDF-segment
  differential landed (3 cases, pairs within 1e-6). **PH-5 landed** (bounded Lean evidence):
  `Vdb/TetStuffing` machine-checks the BCC stuffing case contracts over all 16
  sign patterns; the C warping/float path remains outside the model.
- **Bounded wall groups (§4.0)**: `Vdb/AngleNFaceRatBounded` (uniform-weight seam over 64 axis subsets, 7.31 s), `Vdb/FastSweep1D` (two-sweep 1-D Eikonal solution, 9.08 s), `Vdb/EulerDisjointBounded` (χ(∂K)=2χ(K) for separated cube subsets, 5.01 s). All machine-checked with exact rationals; none weakens the general walls. A n=6 geometric-seam group was attempted and walled in 14.68 s (boundary-map equality does not transport fan geometry/transfer data); the blocker is recorded in `lean/VERIFICATION.md`.
- **Publication** is the only remaining process item and requires explicit
  authorization plus the AGENTS.md pre-push audit; nothing has been pushed.

## 11. User decisions (resolved)
1. **Fix in C** the on-disk-behaviour findings (F1 half rounding/NaN, F3
   version cap and `block_byte_offset`, F7 bool-leaf origin). Each fix:
   regression test first, Lean spec defines the intended behaviour, update
   CHANGELOG and docs. F1: one rounding mode (round-to-nearest-even, matching
   F16C/OpenVDB) for scalar and SIMD, NaN preserved as half NaN. F3: reject
   versions above the highest supported, validate `block_byte_offset`, and
   write OpenVDB-compatible offsets. F7: write the leaf's real origin, derived
   from the tree when it isn't stored.
2. **MC cracks (if F10 is confirmed): use a consistent face rule**, not an
   asymptotic decider. Ambiguous faces are resolved by a fixed rule depending only
   on the face's sign pattern, e.g. "separate the inside corners", the same for
   both neighbouring cubes. Patch the affected `MC_TRI_TABLE` entries, regenerate
   `Mesh/McTable.lean`, and prove `T-MC-FACE-CONSISTENT` and watertightness on the
   new table. DMC-1 uses the same rule.
3. **P6 approved**: implement C DMC (`tvdb_grid_volume_to_mesh_dual` + dense
   `tvdb_sdf_to_mesh_dual_ex`) as lane VS-3, in parallel with VS-1 (user
   decision 2026-11-18); validate against the already landed `n=3`/`n=4` Lean
   DMC-1 vectors. The general Lean Nodup criterion (VS-2) may land afterwards.
4. **CI: local checks only for now.** Do not add a Lean CI job. Lean gates run
   locally through scripts and the CTest option `TINYVDB_BUILD_LEAN_DIFF`
   (default OFF).
5. **Lane priority (2026-11-18):** VS-0 first, then VS-1 and VS-3 in parallel,
   then VS-2 and VS-4a. The planning artifact is this file plus the refreshed
   `lean/VERIFICATION.md` and `lean/README.md` (no separate out-of-repo plan).
6. **Proof budget:** 10-minute wall-clock cap per proof group, with the
   split / bounded / hypothesize / wall ladder of §4.0. A stalled proof is
   never weakened to a false or `sorry`-carrying claim.
7. **Wall promotion:** the general angle-weighted (Bærentzen–Aanæs) sign proof
   (VS-4a) is in scope; Zhao 2005, general Poincaré–Lefschetz, staircase
   consistency and the aggregate Barnes–Hut claim stay parked.
8. **Instrumentation fix (2026-11-18):** all `lean/scripts/check_*.sh` export
   `ELAN_TOOLCHAIN` from `lean/lean-toolchain`, because CTest invokes them from
   the build directory and elan would otherwise select the ambient (4.36)
   toolchain instead of the pinned 4.36 and corrupt the mathlib cache.
9. **Physics scope (2026-11-23):** part decomposition covers *both* SDF
   connected-component segmentation (existing C APIs) and convex decomposition
   (new C + Lean, PH-3); contact/manifold queries are in scope (PH-4);
   isosurface-stuffing tet meshing is parked as optional (PH-5).
10. **Collision proxy implementation (2026-11-23):** mesh simplification has no
    C API in this repo; PH-2 adds a C QEM/edge-collapse `_ex` API together with
    its Lean model, proofs and differential harness.
11. **Physics ordering (2026-11-23):** `PH-0 → PH-1 → (PH-2 ∥ PH-3) → PH-4`;
    PH-5 only on explicit go-ahead. Publishing still requires separate explicit
    authorization.
