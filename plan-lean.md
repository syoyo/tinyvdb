# plan-lean.md — Lean 4 formalization and verification of TinyVDB

Target repo: `tinyvdbio` (C11 core, Apache-2.0). Hand-off plan for an implementing
coding agent. Read `AGENTS.md` (repo root) first; its pre-push procedure applies
and **nothing is pushed without explicit authorization**.

Reference precedent: `~/work/tinyexr/lean/` (Lean v4.35.0 + mathlib v4.35.0,
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
proofs; (b) optional phase P6 adds a C implementation
`tvdb_grid_volume_to_mesh_dual` (+ dense variant) validated by the Lean oracle.
P6 is approved (§11.3).

---

## 1. Repository layout and tooling

```
lean/
  lean-toolchain            leanprover/lean4:v4.35.0   (match tinyexr; elan has it)
  lakefile.lean             package vdbSpec; mathlib @ v4.35.0; warningAsError
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

## 4. Phase P3 — Volume → mesh

### 4.1 Mesh model (`Mesh/Types`, `Mesh/Closed`)
- `TriMesh`/`QuadMesh` with `Fin n` vertex indices; undirected edges; oriented
  half-edges. `boundary₂ : Mesh → (Edge →₀ ZMod 2)`; oriented boundary over ℤ.
- `Watertight m :↔ boundary₂ m = 0`; `Oriented m :↔ orientedBoundary m = 0`;
  `EdgeManifold m :↔ every edge has exactly 0 or 2 incident faces`;
  `VertexManifold` (single fan). Euler `χ = V − E + F`.

### 4.2 Marching cubes (existing C) (`Mesh/McTable`, `Mesh/MarchingCubes`)
- Encode corner order `{000,100,110,010,001,101,111,011}`, edges
  `{0-1,1-2,2-3,3-0,4-5,5-6,6-7,7-4,0-4,1-5,2-6,3-7}`, classification
  `bit c ⇔ value < iso` (equal ⇒ outside).
- Table theorems by `decide` over 256 cases:
  - `T-MC-EDGE`: every edge used by `TRI_TABLE[k]` is set in `EDGE_TABLE[k]`
    and is a sign-change edge of case k; and conversely every sign-change edge
    is used (no dangling crossing).
  - `T-MC-COUNT`: ≤ 5 triangles; −1 terminator well-formed.
  - `T-MC-CELL-BOUNDARY`: the mod-2 boundary of case k's triangles, restricted
    to the cube, lies on the cube faces, and on each face equals the face's
    segment set determined by the **face sign pattern + the table's choice**.
  - `T-MC-FACE-CONSISTENT` (F10): for each of the 6 ambiguous face patterns,
    both neighbouring cube cases choose the **same** segment pairing ⇒ the MC
    mesh is watertight on any grid without iso-equal samples. **Expectation:
    the classic table can fail this** — if `decide` finds counterexamples,
    record them (case pairs), add a C regression test reproducing a crack on a
    2×1×1-cell grid, and apply the consistent face rule fix (§11.2).
  - Orientation: `TABLE` winding faces the negative phase; `OUTWARD` is the
    `(v0,v2,v1)` permutation; prove oriented boundary cancellation per face
    given consistency.
- Geometry: edge parameter `t = (iso−v0)/(v1−v0) ∈ [0,1]` on crossing edges
  (no division by zero since signs differ); vertex lies on the segment;
  interpolation is exact for linear fields (vertex is the true zero).
- Welding: vertex key = (lower corner, axis); `T-MC-WELD`: #vertices =
  #sign-change grid edges exactly; key → vertex injective; output independent
  of traversal/worker partition (`T-MC-DET`: emission in raster order is a
  function of the grid only).
- Tree MC (`tool_mesh`): ownership rule (lowest corner via ctz) partitions
  crossing cells exactly once (`T-OWN-PART`); affine map with `det(M) > 0`
  triangle flip keeps outward orientation (prove orientation of
  `M`-image flips iff det < 0).
- Adaptivity (vertex clustering): only prove "every output vertex within tol of
  every merged input vertex" + degenerate-face removal; explicitly not
  topology-preserving.

### 4.3 Dual marching cubes (`Mesh/DualMC`) — new
Two levels:
- **DMC-0 (surface nets / cuberille dual)**: one vertex per crossing cell
  (any vertex position rule), one quad per sign-change **grid edge**, joining
  the 4 cells sharing that edge (boundary edges with < 4 cells handled as open).
  - `T-DMC0-CYCLE`: on a grid with no boundary crossings (or padded with the
    outside sign), the quad mesh is watertight: it is the boundary of the
    union of dual cubes of inside samples, and ∂∂ = 0 over ZMod 2.
  - `T-DMC0-ORIENT`: quad orientation from edge direction + sign is a ℤ-cycle
    (outward normals).
  - `T-DMC0-χ`: χ(mesh) = 2·χ(solid) when edge-manifold.
  - Non-manifold edges occur exactly at the 2 ambiguous diagonal face/edge
    configurations — characterize them (`decide` on 2×2×2 neighbourhoods).
  - Vertex placement: (a) mean of edge crossings → lies in the cell (convexity);
    (b) QEF/dual contouring is out of scope except "clamped to cell" lemma.
- **DMC-1 (Nielson dual marching cubes)**: per cell, one vertex **per MC
  patch** (component of case k's surface), from the same 256-case table;
  quads join the patch-vertices owning the edge.
  - `T-DMC1-MANIFOLD`: with face-consistent ambiguity resolution (proven table
    property from §4.2 or the fixed table), the mesh is edge- and
    vertex-manifold and watertight on padded grids.
  - `T-DMC1-DUAL`: DMC-1 is combinatorially dual to the MC mesh: bijection
    MC triangle-patches ↔ DMC vertices, MC vertices ↔ DMC quads; χ equal.
- Executable reference over ℚ in `OpsGen` producing quads + vertices for
  vector sets (spheres, tori, checkerboards, random signs, all 256 single-cell
  cases padded).

### P3 differential tests
- MC: Lean ℚ vs C dense + tree MC — faces equal as index lists (bit-exact
  topology), positions ≤ 2e-6; all 256 cases + random grids ≤ 12³.
- DMC: only Lean until P6; validate Lean topological invariants on the vectors
  (watertight, χ) as executable checks and cross-check χ with
  `tvdb_level_set_euler_characteristic` on the same grid.

---

## 5. Phase P4 — Mesh → volume

### 5.1 Closest point on triangle (`Mesh/Triangle`)
- Spec: `dist(p, T) = inf_{q∈T} |p−q|` with T = convex hull of 3 points.
- Executable Ericson region test (7 Voronoi regions) over ℚ/ℝ.
  `T-CP-CORRECT`: for non-degenerate T the returned q ∈ T and
  `|p−q| = dist(p,T)` (via first-order optimality on each region).
  Degenerate (collinear/coincident) faces: reduce to segment/point, theorem
  matching the C double fallback semantics.
- Mesh distance: `dist(p, M) = min_f dist(p, T_f)`; tie-break lowest face
  index (`T-TIE`: argmin is unique under the order).

### 5.2 BVH (`Mesh/Bvh`)
- AABB lower bound `aabbDist(p, box) ≤ dist(p, T)` for T ⊆ box.
- `T-BVH-SOUND`: pruned traversal with strict `>` + seed best face returns the
  same (distance, face) as brute force — the C claim "bit-for-bit equal to
  brute force" becomes a theorem over ℚ; tested bit-exactly over Float.
- Build properties (median split, ≤ 4 per leaf, depth ≤ 64) only as
  well-formedness invariants (partition of face set).

### 5.3 Sign (`Mesh/Winding`, `Mesh/MeshToVolume`)
- Face-normal sign rule (dense C path): formalize; **counterexample** theorem
  showing wrong sign near a convex edge/vertex (F11), and positive theorem: if
  the closest point lies in a face's interior the rule is correct for a closed
  oriented manifold mesh locally (half-space argument). Propose angle-weighted
  pseudonormals (Bærentzen–Aanæs) as the fix and prove their sign rule at
  edge/vertex closest points for **convex** meshes (full non-convex proof is a
  stretch).
- Generalized winding number: `w(p) = Σ_f Ω_f(p)/(4π)` with Van
  Oosterom–Strackee `Ω = 2·atan2(a·(b×c), |a||b||c|+(a·b)|c|+(b·c)|a|+(c·a)|b|)`.
  Theorems: orientation flip negates; additivity; translation/rotation
  invariance; `|Ω_f| < 2π`. Integer-valuedness on closed meshes is a stretch
  (needs degree theory; mark explicitly if not done) — instead verify
  executably on vectors (|w−round(w)| < 1e−9 for closed test meshes).
- Barnes–Hut far-field (dipole) approximation: prove the dipole term is the
  first-order Taylor term of Σ Ω_f; give an explicit error bound only as stretch.

### 5.4 Narrow band and lattice
- Dense: `origin = bbox_min − band`, `n = max(1, ceil((extent+2band)/h))`
  (cap 2048): covers bbox ⊕ band (`T-LATTICE-COVER`); value
  `clamp(±dist, −band, band)`.
- Tree: seeding by barycentric samples with step ≤ h/2 + dilation by
  `ceil(√3·max(ext,int)/h)+2` layers: `T-BAND-COMPLETE`: every voxel with
  `dist < width` is in the candidate set (the key correctness lemma for
  sparse mesh→volume; prove from sample spacing + dilation radius).
- Keep rule `d < (inside ? interior : exterior)`; stored `−d` never −0.
- Composition: final tree after flood fill + prune `denote`s to
  `clamp(signedDist, −in, ext)` on the band and ±width outside (given correct
  sign oracle).

### P4 differential tests
- Distances: ℚ exact vs C (`2e-5` / bit-exact face index); random triangles
  incl. degenerate and huge coordinates (overflow fallback).
- BVH vs brute force: face index bit-exact.
- Winding: exact mode vs Lean Float within 1e-9; fast mode 1e-2 outside.
- Sign counterexample meshes (F11) reproduced in C as a regression test.

---

## 6. Phase P5 — Composition / end-to-end
- `level_set_rebuild`: MC (→ mesh) then mesh→SDF then re-sign; theorem for
  linear (planar) fields: rebuild reproduces the plane SDF within band (exact
  over ℚ); general case: tested only.
- Volume ↔ file: `vdbcheck` on files written by `tvdb_mesh_to_level_set` →
  write → read; theorem-level reuse of `T-SEM-RT`.
- NanoVDB conversion (optional): spec only for `0/5/4/3` layout node packing
  of float trees + lookup equivalence; F9 checked against `WellFormed`.

## 7. Phase P6 (approved) — C DMC implementation
- New API `tvdb_grid_volume_to_mesh_dual` (+ dense `tvdb_sdf_to_mesh_dual_ex`)
  following existing `_ex` contracts (status + `tvdb_error_t`, output preserved
  on failure, arena rollback, alias rejection, deterministic across workers).
- Validated against Lean DMC-1 vectors (topology bit-exact, positions tol);
  CTest + docs + CHANGELOG; GPU port not included.

---

## 8. Sequencing, sizing, risks

| Order | Phase | Est. effort | Risk |
|---|---|---|---|
| 1 | Tooling skeleton, Bytes, Mask, Coord, LE/strings | S | low |
| 2 | P1 tree model + semantics + lookup equivalence | M | medium (rank/indices proofs) |
| 3 | P1 MaskCompress + Half + Chunk | M | medium |
| 4 | P1 parse/emit + file round trip + vdbcheck/vdbgen + C diff | L | **high** (writer canonicalization, legacy versions) |
| 5 | P3 MC table theorems (decide) | S–M | medium (F10 outcome) |
| 6 | P2 SDF/CSG/sampling/Godunov | M | low–medium |
| 7 | P2 fast sweeping + flood fill + χ | M–L | medium |
| 8 | P3 DMC-0 then DMC-1 | L | medium–high |
| 9 | P4 triangle/BVH/sign/winding/band | L | high (geometry proofs) |
| 10 | P5 composition, P6 C DMC | M–L | medium |

- Each phase: land theorem + executable + differential vectors together;
  checkpoint commits locally; **no push** without authorization.
- If a proof stalls > ~1 day of effort: weaken to an executable `decide`/
  exhaustive check on bounded sizes, record the gap in VERIFICATION.md
  ("Theorem boundary"), continue.
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

## 10. Definition of done
- `lean/` builds sorry-free with documented axiom profile.
- P1 theorems T-FILE-RT, T-SEM-RT, T-EMIT-PARSE-WF, mask-compression round
  trip, slot bijection, lookup equivalence: proven.
- P2: exact-SDF theorems (sphere, box, torus, capsule), CSG set semantics,
  T-GOD-EQ/T-GOD-DISC, T-FS-MONO/SIGN/FIX, flood-fill spec: proven.
- P3: MC table theorems proven; F10 decided; DMC-0 watertight + oriented
  proven; DMC-1 manifold theorem proven or boundary documented.
- P4: T-CP-CORRECT, T-BVH-SOUND, T-BAND-COMPLETE proven; F11 decided.
- Differential gates wired into CTest (skip 77 without Lean) with 0
  unexplained disagreements; findings F1–F13 each resolved (F1/F3/F7 fixed in
  C; F10 fixed via consistent face rule if confirmed).
- P6 C DMC shipped with tests matching Lean DMC-1 vectors.
- Stretch items explicitly listed as done / not done in VERIFICATION.md.

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
   `tvdb_sdf_to_mesh_dual_ex`) after DMC-1 in Lean is done.
4. **CI: local checks only for now.** Do not add a Lean CI job. Lean gates run
   locally through scripts and the CTest option `TINYVDB_BUILD_LEAN_DIFF`
   (default OFF).
