# CPU baseline

Captured with `tests/bench_tinyvdb.c` (build with `-DTINYVDB_BUILD_BENCH=ON`).

Machine: AMD Ryzen Threadripper 1950X, 32 threads, AVX2 (no AVX-512), 122 GB RAM.
Build: Release, `TINYVDB_OPENMP=ON`, `TINYVDB_SIMD=ON`, `TINYVDB_USE_SYSTEM_BLOSC=ON`.
Command: `bench_tinyvdb --dim 128 --reps 2 --threads 1,2,4,8,16,32`

Record a new row after each optimization phase; do not edit numbers in place.

## Parallel scaling (dim=128, ms, lower is better)

| case | 1 | 2 | 4 | 8 | 16 | 32 | 1 -> 16 | note |
|---|---|---|---|---|---|---|---|---|
| laplacian | 13.34 | 7.61 | 5.86 | 3.75 | 3.54 | 6.35 | 3.8x | scales, then regresses at 32 |
| poisson | 385.80 | 205.31 | 139.07 | 76.67 | 60.96 | 462.14 | 6.3x | 32 threads is 7.6x *slower* than 1 |
| dilate | 25.26 | 15.31 | 15.31 | 15.26 | 15.53 | 16.00 | 1.6x | no pragma; flattens after 2 |
| gaussian | 61.48 | 50.46 | 51.61 | 51.77 | 51.37 | 51.19 | 1.2x | separable_pass, unannotated |
| load | 20.37 | - | - | - | - | 13.08 | 1.6x | I/O target has no OpenMP |
| mc | 53.40 | - | - | - | - | 39.44 | 1.4x | serial; shared edge cache |
| tree_build | 116.58 | - | - | - | - | 94.75 | 1.2x | fully serial |
| tree_dilate | 324.28 | - | - | - | - | 292.03 | 1.1x | fully serial |
| sweeping | 20.43 | - | - | - | - | 16.98 | 1.2x | serial by construction |
| flood | 11.61 | - | - | - | - | 7.09 | 1.6x | serial DFS |
| dense_to_sparse | 35.33 | - | - | - | - | 20.30 | 1.7x | |

## Reading these numbers

- **poisson at 32 threads is a 7.6x regression against 1 thread.** Each CG
  iteration opens ~8 separate `omp parallel` regions (tinyvdb_ops.c:892-941), so
  at 32 threads the barrier and work-distribution cost exceeds the work. This is
  the clearest single defect in the threading story. Fix: one `omp parallel`
  region wrapping the iteration loop with `#pragma omp for` inside.
- **dilate and gaussian barely move past 2 threads.** Both kernels have no
  pragma at all (tinyvdb_ops.c:52 `tvdb_morph_step`, :129
  `tvdb_separable_pass`), despite their fp64 twins in the same file being
  annotated. The small 1->2 gain is noise, not scaling.
- **laplacian gains 3.8x and then regresses at 32**, consistent with
  `collapse(2)` over (iz,iy) plus cache contention.
- **SIMD and OpenMP are mutually exclusive today.** `tvdb_dot`
  (tinyvdb_ops.c:828) compiles the AVX2 path out when
  `TINYVDB_OPENMP_ENABLED` is defined, so this table was measured *without*
  vectorized dot products even though `TINYVDB_SIMD=ON`.

## Memory

Peak RSS is a process high-water mark, so it only grows across cases; read the
delta per case, not the absolute column.

| case | peak RSS at dim=128 |
|---|---|
| after load | 11.0 MB |
| after tree_build (364k voxels) | 46.8 MB |
| after tree_dilate | 122.5 MB |
| after dense_to_sparse | 122.5 MB |

## mesh_to_sdf: BVH (Phase 3)

`tvdb_mesh_to_sdf` used to test every voxel against every triangle -- no spatial
acceleration of any kind. It now builds a BVH over the triangles and fills the
grid in parallel. This was the single worst-performing path in the library.

Brute force (pristine `git archive HEAD`) vs now, dim is the level-set
resolution, grid is the padded output:

| dim | brute force | BVH, 16 threads | speedup |
|---|---|---|---|
| 32 | 2864 ms | 16.0 ms | 179x |
| 48 | 17242 ms | 59.7 ms | 289x |
| 64 | 63225 ms | 138.8 ms | **455x** |

The speedup grows with resolution because the brute force is quadratic while
the BVH query is near-logarithmic. The benchmark case no longer needs the size
cap that previously kept it measurable.

### Design

- Flat array BVH over triangle AABBs, median split on the widest centroid axis,
  leaves of <= 4 triangles, explicit 128-entry traversal stack.
- Node bounds are used **only** to prune. Pruning is a strict `>` comparison,
  never `>=`: the brute-force loop keeps the lowest face index among exact
  ties, so a triangle at exactly the current best distance can still change the
  result. Pruning on equality silently drops those.
- The fill is `#pragma omp parallel for collapse(2)` over (z,y); the BVH is
  read-only once built.

### Two bugs found by fuzzing, both caught before release

A differential fuzzer compares the accelerated result against a verbatim
re-implementation of the original inner loop, on adversarial meshes: single
triangles, more faces than vertices (zero-area), duplicated faces (guaranteed
exact ties), and coincident vertices (all centroids collide). It found two real
defects:

1. **Pruning on equality dropped the winning face.** Using `nd >= best_dsq` cut
   off subtrees that could contain an equidistant but lower-indexed triangle.
   75 of 120 trials mismatched; switching to strict `>` cut that to 15.
2. **The "no face accepted" case inverted the sign.** When every candidate
   distance is NaN (a mesh of zero-area triangles makes `tri_closest_point_c`
   return NaN, so no face is ever accepted), the original leaves
   `best_cp = {0,0,0}`. Recomputing the closest point from face 0 produced NaN,
   and `NaN >= 0.0f` is false, so the sign flipped at those voxels. The BVH now
   returns the closest point and normal directly, preserving the original's
   initialization exactly.

Both produced a *different triangle* being selected, which the sign then
amplified into a fully wrong voxel. After the fixes, 400 fuzz trials plus the
sphere meshes at 1/2/4/8/16/32 threads are all bit-identical to the brute-force
result, and TSan is clean.

### A rejected alternative

A binned surface-area-heuristic split (16 bins, the standard SAH cost) was
implemented and measured **worse**: 78 and 142 triangle tests per query versus
105 for the plain median split. The heuristic scores candidate planes against
triangle AABB centroids, and for a level-set shell every centroid sits on the
same surface, so the bins carry almost no information. Reverted to the median
split, with the reasoning recorded in the source so it is not re-attempted
blindly.

## Phase 1 results (I/O + deserialization)

All four changes are in `tinyvdb_io.h` / `tinyvdb_nanovdb.h`. Every one was
verified bit-identical: a hash over every node's masks, values and child index
arrays matches the pre-change build exactly on all six corpus grids.

### Load time (best of 5, `tvdb_read_all_grids`)

| grid | before | after | speedup |
|---|---|---|---|
| icosahedron.vdb | 8.7 ms | 6.7 ms | 1.30x |
| smoke.vdb | 8.9 ms | 8.8 ms | 1.01x |
| bunny.vdb | 118.8 ms | 91.7 ms | 1.30x |
| fire.vdb | 93.4 ms | 69.8 ms | 1.34x |
| explosion.vdb | 165.5 ms | 144.8 ms | 1.14x |

smoke.vdb barely moves because it is version 222 with compression flag 0x1
(ZIP only) and has a small active set, so it exercises far less of the
mask-scatter path.

### What changed

1. **Shared staging buffer** (`tvdb__read_mask_values`). Each node used to
   malloc, zero and free its own decompression scratch. One buffer now serves
   the whole tree load and is released in `tvdb__read_grid` on every path.
   Allocations per node: **5.07 -> 4.07** (bunny: 147,943 -> 118,782).
2. **Float fast path for the mask-compressed value scatter.** The generic loop
   did a bounds-checked `nodemask_is_on` plus a variable-size `memcpy` per
   element. The common `float`/full-width case now uses direct 32-bit loads
   from the mask words and a fixed 4-byte store.
3. **Popcount `bitset_count_on`.** Replaced the `while (v) { v &= v-1; }`
   branch-per-bit loop. This ran once per compressed node and was ~12% of load
   time. Verified against the original over all 256 byte values and 200,000
   random masks of varying width.
4. **Table-driven CRC32** (`tvdb_nanovdb_crc32`). 108 -> 443 MB/s (4.1x),
   bit-identical over 78 size/offset/seed combinations.

### Rejected after measurement

Two ideas from the original review did not survive measurement and were
dropped rather than shipped:

- **Sizing internal-node `values` by active count** instead of `bitsize`. The
  "92.6% of payload" figure is real, but only for grids with very few leaves:
  on bunny.vdb the array is 2.2 MB of 61 MB (3.6%), because leaf data
  dominates. Shrinking it also breaks the layout contract -- the writer emits
  `bitsize` values, `vdbrender.cc:192` indexes `values[slot]`, and
  `tvdbview/main.cc:1797` asserts `values_size/vsize == bitsize`. Not worth it.
- **A bump arena for node masks/payloads.** After the scratch-buffer change,
  malloc is only ~4.5% of load time (`_int_malloc` 1.75%, `malloc` 0.83%,
  `malloc_consolidate` 1.94%). glibc's per-chunk header tax is 8 bytes, not
  the 16 originally assumed. The remaining 4 allocs/node are 2-3 real payload
  arrays, so an arena would buy little for real risk.

## Phase 2 results (threading + kernels)

All changes are in `src/tinyvdb_ops.c`. Every parallelized kernel was checked
for thread-count independence: identical results at 1, 2, 4, 8, 16 and 32
threads.

### Correction to the Phase 1 reading of Poisson

The baseline table above records Poisson as "7.6x slower at 32 threads than
at 1", and the first Phase 2 measurement seemed to confirm it (2571 ms at 16
threads). **That number was a measurement artifact** -- it was taken while the
machine was busy, and the machine varies a lot run to run.

Re-measured with the two binaries interleaved and best-of-N against a pristine
`git archive HEAD` build, the fork/join cost turned out to be worth only
~1.1x, not 78x. A control experiment settles why: fusing 100 trivial
`omp parallel for` regions into one region with 100 inner loops changed
nothing measurable on this box, and 32 threads is slower than 8 for a plain
memory-bound loop. The 32-thread cliff is this machine (Threadripper 1950X
running at ~2.1 GHz base with SMT contention across 16 physical cores), not the
code. Pinning with `OMP_PROC_BIND` recovers most of it.

So the fusion was kept because it is correct, thread-count independent, and
marginally faster -- not because it fixed a 7.6x regression.

### Poisson CG (fused: 6 regions/iteration -> 2, fp32 and fp64)

Interleaved best-of-7, dim=128, 20 iterations:

| threads | before | after | speedup |
|---|---|---|---|
| 1 | 187.9 ms | 159.8 ms | 1.18x |
| 4 | 56.3 ms | 51.8 ms | 1.09x |
| 8 | 37.7 ms | 32.6 ms | 1.16x |
| 16 | 31.4 ms | 31.0 ms | 1.01x |
| 32 | 216.7 ms | 118.4 ms | 1.83x |

Iteration count and residual are identical to the original at every thread
count (63 iterations, relative residual 1.0e-4), so this is a pure
restructuring.

Two bugs were introduced and caught during this work, both worth recording:
- Combining partials with `omp critical` and then reading them in `single` is
  **wrong**: `critical` serializes but does not synchronize, so `single` can run
  before every thread has contributed, and the solver divided by a partial
  pAp. Reproduced in a 10-line standalone case. The correct pattern is a
  `reduction` on the `omp for` itself, which combines at that construct's own
  closing barrier.
- The first attempt also used a `critical` section, which serialized all 32
  threads and made small grids 4-8x *slower* than the original. Replaced with
  the lock-free `omp for` reduction.

### Kernels that had no pragma (dim=256, reps=3)

`tvdb_morph_step`, `tvdb_separable_pass`, `tvdb_laplacian_filter`, the three
fp32 `tvdb_csg_*`, `tvdb_surface_area` and `tvdb_volume` were entirely serial,
even though the fp64 twins of the CSG and measurement kernels in the same file
already carried pragmas. All read/write disjoint ping-pong buffers or are
elementwise, so they parallelize directly.

| case | threads | before (serial) | after | speedup |
|---|---|---|---|---|
| dilate | 4 | 294.9 ms | 174.4 ms | 1.69x |
| dilate | 8 | 295.4 ms | 160.2 ms | 1.84x |
| dilate | 16 | 284.1 ms | 150.8 ms | 1.88x |
| gaussian | 4 | 823.8 ms | 382.1 ms | 2.16x |
| gaussian | 8 | 838.0 ms | 242.5 ms | 3.46x |
| gaussian | 16 | 797.7 ms | 211.3 ms | 3.78x |

Single-threaded time is unchanged (as expected), so these are pure parallel
gains with no added per-element cost. The reductions in `surface_area` and
`volume` accumulate an exact integer count in a double, which is bit-stable
regardless of how the work is split.

### Median filter: qsort-per-voxel -> quickselect

`tvdb_median_filter` ran a full `qsort` on a `(2r+1)^3` window for every voxel
(343 elements at r=3). Replaced with an in-place median-of-three quickselect,
which is O(n) expected and selects the identical element.

Measured on N=64, r=3, 2 iterations:

| threads | before | after | speedup |
|---|---|---|---|
| 1 | 3.01 s | 0.60 s | 5.0x |
| 8 | 2.92 s | 0.09 s | 32x |
| 16 | 3.03 s | 0.08 s | 38x |

Verified identical to the original: an FNV hash over every output voxel matches
for N in {32, 48, 64} and r in {1, 2, 3}, and the selection routine was
checked against `qsort` on 200,000 random cases spanning sorted, reversed,
duplicate-heavy, binary and uniform data. The first version of the quickselect
had an unbounded scan loop and hung; the shipped version bounds both scans and
guarantees progress.

### SIMD / OpenMP

`tvdb_dot` compiled the AVX2 path out whenever `TINYVDB_OPENMP_ENABLED` was
defined. The stated reason -- unstable summation order from nested SIMD -- does
not apply now that both call sites are outside the iteration loop, so the AVX2
reduction is used unconditionally when available. This is worth little for
speed (two calls per solve) but removes a confusing build-dependent behaviour.

## Marching cubes: measured, and NOT the bottleneck

The original plan assumed `tvdb_sdf_to_mesh` was a major cost, on the theory
that its shared edge cache rehashes inside the innermost loop. That turned out
to be wrong. Measured directly (marching-cubes sphere, and a noisy SDF with
99.9% active voxels which is the worst case for a surface extractor):

| N | faces | time | us/cube |
|---|---|---|---|
| 128 | 98780 | 20.4 ms | 0.010 |
| 192 | 222296 | 55.0 ms | 0.010 |
| 384 | 407256 | 446.4 ms | 0.008 |

It scales linearly and costs 0.01 us/cube. The edge cache is an open-addressing
map that doubles geometrically, so the rehash cost amortizes away; it is not the
problem. The 3-phase parallel restructure remains a valid future idea but
would buy a path that is already ~1000x cheaper than `mesh_to_sdf` was.

Lesson: this and the Poisson case in the previous section both point the same
way -- the initial review ranked paths by reading code rather than measuring
them, and was wrong twice. Measure before reprioritizing.

## mesh_to_sdf: two build strategies tried and rejected

The BVH still issues ~105 triangle tests per query, and per-voxel cost grows
with mesh size (1.8 us at 128^3, 2.9 us at 256^3). Diagnosis: on a level-set
mesh every triangle centroid lies on a thin shell (measured: all 98,780
centroids fall in two radial bins at r*20 = 7 and 8), so a centroid median
split cannot separate them well.

Two alternatives were implemented and measured, and both were **worse**:

- **Binned surface-area heuristic** (16 bins, standard SAH cost): 78 and 142
  tests/query versus 105 for the median split. The heuristic scores planes
  against triangle AABB centroids, and on a shell those carry no information.
- **Morton-code (LBVH) ordering plus balanced midpoint split**: 1.99 and 4.08
  us/voxel versus 1.77 and 2.87. Morton groups space well, but a *balanced*
  midpoint split over that order cuts across the shell, producing long thin
  boxes. The original median split wins because its node boxes stay compact
  even though the ordering ignores the shell structure.

Both were reverted and the dead code removed; the reasoning is recorded in the
source so neither is re-attempted blindly. The remaining headroom is a
sphere-tracing traversal, or exploiting that ~90% of voxels fall outside the
band and get clamped anyway.

## Sparse tree: leaf traversal + leaf-stamp dilate

Two defects in `tinyvdb_sparse_tree.c`, both confirmed by measurement.

### 1. Bit-at-a-time child-mask scan (151x overhead)

The internal-node walk tested every bit of the child mask one at a time, from
0 to `1 << 3*log2dim` (32768 for a level-2 node), even though a typical node has
a few hundred children. On a real icosahedron build that is **294,912 bit tests
to visit 1,951 children -- 151x overhead**, on a path that runs on every tree
traversal.

Replaced with a word-at-a-time scan: assemble each 64-bit mask word
little-endian (matching the bit order `nm_set` uses), then take
count-trailing-zeros of the remaining bits and clear the low one. This visits
exactly the set bits in the same ascending order, so nothing downstream moves.
Portable ctz helpers are provided for pre-C23 compilers (the tree still
supports GCC 4.8 / MSVC).

`tvdb_grid_active_voxel_count` on icosahedron: **0.321 ms -> 0.092 ms (3.5x)**.

The unused `nth_set_bit_pos` helper, which had the same O(bitsize) scan, was
removed rather than left as a trap.

### 2. Leaf-stamp dilate was fully serial

`dilate_step` grew a shared output with a capacity check per voxel. Restructured
into three phases: per-leaf active-voxel counts (parallel), an exclusive prefix
sum (serial, trivial), then a parallel scatter where each leaf writes only into
its own contiguous block. Because the original emitted leaves in order and, in a
leaf, (i,j,k) order, the block layout reproduces the output byte for byte --
verified by hashing the full ordered output of dilate/erode (topology and
leaf-stamp) against the original build: identical, and identical at 1/2/4/8/16/32
threads.

`tvdb_grid_dilate_active` on icosahedron: **6.8 ms -> 1.8 ms at 16 threads (3.6x)**.

Note this is a *different* code path from `tvdb_grid_dilate_topology`, which
routes through `tvdb_dilate_sparse` in `tinyvdb_sparse.c` (a hash-insert
scatter, ~161 ms) and is untouched. Parallelizing that while preserving its
emission order is a substantially harder problem and was not attempted.

## Next

Remaining, in measured priority order:

1. **`mesh_to_sdf` traversal** -- still 1.8 s at 128^3. Sphere tracing, or a
   cheap "is this voxel outside the band" early-out, which applies to ~90% of
   voxels but needs its own equivalence proof.
2. **`tvdb_dilate_sparse`** -- the hash-scatter topology dilate (~161 ms), now
   the slowest sparse-tree path. Needs a parallel build-then-sort to keep
   emission order.
3. **`to_nanovdb` O(children) scans** at `to_nanovdb.c:456/532/645`; convert
   time is currently comparable to load time.
4. **Sparse tree build** still does a per-parent insertion sort, but the
   measured cost is small (max 255 children, ~236k comparisons on a real
   build) -- the "32768 children" figure in the original review was wrong.
5. **Splat uses `omp atomic` per tap** -- 8 and 27 `lock xadd` per point.
6. **Fast sweeping** could become plane-red-black wavefronts.
7. **Marching cubes parallel restructure** -- real but low value (see above).
8. **GPU: device-local SSBOs.** Still open -- see below.

## GPU backend (Phase 3, first slice)

Baseline first: with `TINYVDB_BUILD_GPU=ON` the 44 CPU-parity tests pass on
both backends (Vulkan via precompiled SPIR-V, CUDA via NVRTC). The headline
number from that baseline is that **the identical SDF kernel took 63.5 ms on
Vulkan and 2.4 ms on CUDA** for the same grid -- a 26x gap that is not compute,
it is memory placement.

### Shipped: compute-pipeline cache

`tvdb_vk_dispatch` created and destroyed 28 Vulkan objects per call, including a
shader module, a pipeline layout, a descriptor-set layout and the pipeline
itself. Measured fixed cost: a trivial 8^3 primitive took ~2.2 ms wall.

Those four objects depend only on (SPIR-V blob, descriptor shape), so they are
now cached in the context and released with it. Descriptor *sets* are still
written per dispatch, since the bound buffers differ, but `UpdateDescriptorSets`
is cheap.

| op (Vulkan) | before | after | speedup |
|---|---|---|---|
| sdf sphere 57^3 | 63.5 ms | 45.0 ms | 1.41x |
| sdf box 33x51x25 | 27.9 ms | 11.7 ms | 2.39x |
| sdf torus 58x19x58 | 31.4 ms | 16.6 ms | 1.90x |
| sample ssbo (already persistent path) | 19.2 ms | 19.2 ms | 1.00x |

Verified: 44/44 parity on both backends, zero failures over 3 consecutive runs,
20 context create/destroy cycles leak-free, and the CPU-only build is unaffected.

### Shipped: shared descriptor pool and command pool

Measured the fixed per-dispatch cost directly (instrumenting the phases of
`tvdb_vk_dispatch` over 23 calls of a trivial 8^3 primitive):

| phase | cost over 23 calls | share |
|---|---|---|
| descriptor pool create + set allocate + write | 41.8 ms | 43% |
| wait for fence | 37.5 ms | 38% |
| command pool + command buffer allocate | 13.0 ms | 13% |
| record + end command buffer | 5.3 ms | 5% |
| submit | 0.6 ms | <1% |

Creating a fresh descriptor pool and command pool on every call was the single
largest item. Both are now created once per context and reused, with
`vkFreeDescriptorSets` returning each set to the shared pool. Overhead over the
same 23 calls: **98.2 ms -> 70.0 ms**. Small grids gained ~10% (8^3: 2.20 ->
1.99 ms); realistic grid sizes did not move, because at 57^3 the fixed cost is
only ~4% of the total. Kept because it is free and correct, not because it is a
large win.

### The 26x gap was a hand-typed constant, not a mirror

The `reverted device-local mirroring` attempt below was the right diagnosis
(wrong memory placement) reached by a wrong route, and its failure was
self-inflicted. It is worth recording what actually caused the 26x, because it
was a single line and no amount of barrier debugging would have found it.

`src/tinyvdb_gpu.c` declares the Vulkan ABI by hand so the library builds with
no GPU SDK installed. Every struct and constant is re-typed, and there are no
headers to check against. The memory-property bits were **a permutation of the
real values**:

| constant | declared | actual |
|---|---|---|
| `VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT` | 0x1 | 0x2 |
| `VK_MEMORY_PROPERTY_HOST_COHERENT_BIT` | 0x2 | 0x4 |
| `VK_MEMORY_PROPERTY_DEVICE_LOCAL_BIT` | 0x4 | 0x1 |

So the SSBO path asked for `HOST_VISIBLE | HOST_COHERENT` and received bit 0x3,
which the driver reads as `DEVICE_LOCAL | HOST_VISIBLE` -- and on a discrete
NVIDIA part the only such type is the write-combining BAR. Every buffer lived
there. Worse, the four "device local" allocations (the sparse-image path) asked
for bit 0x4, which is `HOST_COHERENT`: **nothing device-local was ever
allocated**. The code ran and produced correct results, which is why this
survived; write-combining host memory is merely very slow, not wrong.

Four more wrong constants, all of which the NVIDIA driver tolerates but other
drivers do not:

| symbol | declared | actual | consequence |
|---|---|---|---|
| `VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO` | 100 | 29 | wrong on any strict driver |
| `VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER` | 44 | 45 | wrong; this is the constant the crashed mirror reused for a *buffer* barrier, which is the most likely cause of the `libnvidia-glcore` segfault |
| `VkQueueFamilyProperties` | 40 bytes, `minImageTransferGranularity` at 16 | 24 bytes, at 12 | array-stride mismatch, so every queue family after the first was read as garbage |

Correcting all six, with no other change:

| op (Vulkan) | before | after | speedup |
|---|---|---|---|
| sdf sphere 57^3 | 45.0 ms | **10.0 ms** | 4.5x |
| sdf box 33x51x25 | 11.7 ms | **3.56 ms** | 3.3x |
| sdf torus 58x19x58 | 16.6 ms | **4.47 ms** | 3.7x |
| batchReadback | 1.09 ms | **0.168 ms** | 6.5x |

Vulkan vs CUDA for the same kernel: **26x -> 4.6x** (10.0 ms vs 2.17 ms).

To stop this recurring, `tests/test_vk_abi.c` now parses the hand-declared block
out of `src/tinyvdb_gpu.c`, compiles a probe against those declarations and a
second probe against the real `<vulkan/vulkan.h>`, and diffs every struct size,
member offset and constant value -- 459 checks. It is wired into ctest as
`test_vk_abi` and skips cleanly when the SDK headers are absent, since not
requiring them is the reason the ABI is declared by hand. It was confirmed to
fail when a single constant is reverted, so it is a real gate rather than a
formality.

Lesson recorded because it cost real time: a hand-declared ABI needs a
mechanical conformance test from the day it is written, and a tolerated
misdeclaration is worse than a rejected one, because it hides until the
measurement moves.

### Correcting an earlier claim: the "5.7x persistent-dispatch win"

The 5.7x figure quoted above and in the previous summary compared
`persistentSparse` against `denseSSBO`, which are **not the same operation**:
one samples a sparse image3D with hardware trilinear filtering, the other reads
a dense SSBO. It is a comparison of two algorithms, not of persistence, and it
should not be quoted as evidence that per-dispatch cost is 5.7x. The direct
measurement above is the trustworthy number: fixed per-dispatch cost is ~2 ms
and falls to ~1.99 ms with the shared pools, which is only ~4% of a 57^3 op.
Generalizing "persistence" therefore has a ceiling near 4% on realistic sizes,
not 5.7x. The remaining gap is memory placement, not dispatch overhead.

### Device-local SSBO mirroring: implemented, measured, removed

Worth writing down because the *reverted* attempt's crash had a real cause, and
because the correct answer turned out to be "this is not the bottleneck".

The `VkBufferMemoryBarrier` segfault from the first attempt is explained by the
`VK_STRUCTURE_TYPE_IMAGE_MEMORY_BARRIER 44` typo: 44 is
`BUFFER_MEMORY_BARRIER`, so the barriers were tagged as buffer barriers while
carrying image-barrier structs, and the driver read a garbage `VkBuffer` out of
the wrong field. With the constants corrected (`test_vk_abi` now pins all of
them) the barrier version runs cleanly, so the mechanism does work.

It was also not worth having. Implemented as: host-visible buffer stays the
CPU-facing side (all ~170 `memcpy(x.data, buf.mapped, n)` call sites untouched),
`DEVICE_LOCAL` mirror created on first use, stage in, dispatch, stage out, with
explicit buffer barriers both sides.

Applied blanket, it is a large regression:

| op (Vulkan) | host-visible | + blanket mirror |
|---|---|---|
| sdf sphere 57^3 | 9.7 ms | 11.9 ms |
| sdf box | 3.46 ms | 4.42 ms |
| denseSSBO 192^3 | 29.3 ms | 59.5 ms |

These kernels are **output**-bound: the result crosses PCIe once no matter where
the kernel runs, so a device-local binding only adds a stage-in copy of data the
kernel never reads. Made opt-in per dispatch it was worth 4.4% on the one
read-heavy op available to measure, which turned out to be host-bound on
marshalling 65536 query points serially. Worse, a device-local buffer allocated
per dispatch for a buffer as small as 64 KB doubled the host RSS growth rate.

**So it was removed.** The 4.5x that the constant fix delivered was never about
memory placement. The residual ~4.3x Vulkan/CUDA gap is per-dispatch cost
(~2 ms) plus host-side marshalling -- both of which the CUDA path avoids by not
round-tripping through a mapped host pointer at all. Closing it needs a resident
device-side buffer set with batched upload and readback, which is a different
project, not a faster single dispatch.

### Shipped: hash map for ijk_to_index

`ijk_to_index` (and `coords_in_grid` on top of it) scanned the whole active set
per query: O(nq*na). Replaced with an open-addressing map from ijk to
first-seen index: O(na) build + O(nq) probe.

The map is built **on the host**, not the GPU. That is deliberate: a parallel
insert cannot guarantee that the lowest index wins a slot without extra
atomics, and the write-keys-then-compare-keys ordering leaves a duplicate-key
race that would break first-seen semantics. Host-side insertion is in index
order, so "first insert into a slot wins" *is* first-seen, with no atomics and
no race. The construction is the same order as the data upload that already
happens.

Measured, nq=65536 queries (linear -> hash):

| na | linear scan | hash map | speedup |
|---|---|---|---|
| 64 | 5.84 ms | 5.75 ms | 1.02x |
| 512 | 6.58 ms | 6.69 ms | 0.98x |
| 4096 | 13.62 ms | 7.09 ms | 1.92x |
| 32768 | 33.91 ms | 10.62 ms | 3.19x |
| 262144 | 175.32 ms | 45.68 ms | 3.84x |

The linear path scales linearly in na and the hash path is nearly flat, which is
the asymptotics showing through. At small na the map loses, because the build
and the extra keys/values buffers cost more than a short scan saves, so both
paths are kept and selected at `TVDB_VK_INDEX_MAP_MIN_ACTIVE = 2048`. Verified
bit-exact against the CPU reference at na = 512 (linear), 4096, 32768 and
262144 (hash), with query sets containing exact hits, misses and duplicate keys.

**Attribution note:** measured na=512 before gating, the hash map looked like a
2.86x win. It was not -- that was the memory-property constant fix showing
through, because the comparison baseline was `HEAD`. Isolating the three states
separately (18.20 ms at HEAD, 5.99 ms with the constant fix alone, 6.40 ms with
the constant fix plus the map) showed the map is a *loss* at na=512. Always
isolate against a baseline that differs only by the change under test.

### Shipped: same treatment for neighbor_counts and points_in_grid

`neighbor_counts` was the worst of the three: up to 26 full scans of the active
set per active voxel, i.e. O(na^2 * connectivity). `points_in_grid` was O(np*na).
Both now probe the same host-built map above the same threshold, with a map-backed
shader each, and keep their linear-scan path below it.

`neighbor_counts`, against a baseline differing only in this change (constant fix
+ threshold + shared pools, brute force otherwise):

| na | connectivity 6 | connectivity 26 |
|---|---|---|
| 512 | 1.0x | 1.3x |
| 4096 | 1.8x | 2.8x |
| 32768 | 5.6x | 24.6x |
| 110592 | 17.2x | 66.4x |
| 262144 | 27.0x | **device lost** |

The `device lost` cell is the striking one: with the memory-property fix alone,
the brute-force kernel at na=262144 / connectivity 26 issues ~1.8 trillion
comparisons and **hangs the GPU** (`vkWaitForFences failed: -4`), where `HEAD`
completed in 3074 ms. The hash map runs that case in 67.6 ms. So the constant fix
made this kernel *worse* at scale, and the algorithmic fix is what makes it
viable -- the two changes are not independent, and measuring only the end state
would have hidden that.

Verified bit-exact against the CPU reference at na = 512 (linear path), 4096,
32768 and 262144 (map path) for both connectivities, on dense lattices where
interior voxels must report full connectivity. `points_in_grid` gives 1.2-2.2x
with 0 mismatches at every size; it gains less because the op is bounded by the
host-side marshalling of the query points, not by the lookup.

### Shipped: sparse_conv, the last brute-force lookup kernel

`sparse_conv`'s fallback path did a full O(count) scan of the active set for
every kernel tap, i.e. O(count^2 * kx*ky*kz). It now probes the same map above
the same threshold. The map stores the first-seen *index*, and the shader reads
the value at that index, which reproduces the brute-force kernel's "first match
wins" behaviour for duplicate coordinates exactly.

`count` on a wide-stride lattice (so the brute-force path is actually taken;
coordinates are spread enough that the dense fast path's 400e6 cap declines),
k=3, against `HEAD`:

| count | HEAD (brute force) | now (map) | speedup |
|---|---|---|---|
| 512 | 4.96 ms | 4.39 ms | 1.1x |
| 2197 | 11.14 ms | 4.31 ms | 2.6x |
| 4096 | 14.85 ms | 4.80 ms | 3.1x |
| 13824 | 51.07 ms | 10.65 ms | 4.8x |
| 32768 | 108.62 ms | 24.56 ms | 4.4x |

Bit-exact against a CPU reference at every size (max relative error 1.16e-07).

### Three bugs found while doing the above

**1. `descriptor_types[6]` in the pipeline cache entry overflowed.** The first
sparse_conv map dispatch needed 7 bindings. `tvdb_vk_pipeline_entry` had a fixed
`descriptor_types[6]`, so writing binding 6's type overwrote the adjacent
`VkShaderModule` handle. The symptom was a **segfault inside
`libnvidia-glcore` during `tvdb_vk_dispatch`**, not a clean Vulkan error, and it
reproduced at any `count` and even at k=1 -- which is what made it look like a
driver bug rather than a host overflow. Every fixed-size array in the dispatch
path is now sized from `TVDB_VK_MAX_DESCRIPTORS` (8), and `tvdb_vk_dispatch`
rejects an over-large count instead of corrupting memory.

**2. std140 alignment on the new uniform.** The shader declares
`ivec4 kdim`, which std140 requires to start at offset 16, but the matching C
struct put `int32_t kdim[4]` at offset 12. The shader therefore read a garbage
kernel size. The first symptom was the GPU hanging and `vkWaitForFences`
returning `VK_ERROR_DEVICE_LOST`. Fixed with an explicit `align_pad` field.

Neither of these is in the category `test_vk_abi` can catch: one is a host-side
array bound, the other a host/shader struct layout agreement. Both are the kind
of thing that has to be read off the spec, not compiled.

**3. (covered above) the shared command-pool leak.**

Worth noting for the record: the descriptor-count bug was masked for a long
time by the fact that a *7-binding* variant and a *6-binding* variant look
identical from the host. Consolidating the map's key and index arrays into one
interleaved `(ix, iy, iz, v)` buffer fixed the crash, which was initially
misread as "7 descriptors is beyond some driver limit" rather than "we corrupted
a struct". The interleaved layout is the better design anyway -- a probe touches
one cache line instead of two.

### mesh_to_sdf: uniform binning built, measured, reverted

`mesh_to_sdf` is O(nvoxels * nfaces) with a full closest-point test per pair,
which makes it the worst kernel in the backend. On the CPU the equivalent got
455x from a BVH. Built the GPU analogue: exact uniform-grid binning of faces by
world AABB over `domain = voxel grid (+) band`, per-bin AABB, and a ring walk
from each voxel with a conservative `dist2Box >= best` skip. Exactness rests on
three facts, each checked:

  * A face within `band` of a query point is necessarily binned, because the
    ball `B(p, band)` lies inside the expanded domain.
  * `dist(p, bin AABB)` lower-bounds the distance to every face in that bin, so
    a farther bin cannot change the minimum.
  * Faces overlapping no bin go in an overflow list every voxel scans, so
    nothing is ever invisible -- and the sign of the result, which comes from
    the closest face's normal, therefore stays defined.

Three findings, each of which changed the design:

1. **std140 bit us twice.** `vec3 domain_lo` must start at offset 64, but C
   placed it at 52, and the struct was 68 bytes in a 64-byte buffer. Now 80
   bytes with explicit padding, verified with `offsetof` before dispatching.
2. **Bin sizing cannot be in voxels.** Sized at ~4 voxels/bin the grid was 45^3
   bins holding 6342 face references -- 0.19 faces per bin. A voxel's
   neighbourhood is then *empty*, the walk finds nothing and falls back to the
   seed face, which is wrong as well as slow. Bins have to be sized in world
   units (~8 voxels) so a neighbourhood actually holds faces.
3. **The ring walk is not the binding constraint; the watchdog is.** Even
   correctly terminated, the whole grid in one dispatch exceeds the driver's
   TDR limit and comes back as `VK_ERROR_DEVICE_LOST`. A torus at dim=16 is
   199^3 = 4.0M voxels, which the *brute-force* path cannot do either.

Reverted, because none of it could be shown to be a win and the existing parity
test cannot exercise it: `test_mesh_to_sdf` uses a 4-face tetrahedron, so it
never crosses the threshold a binned path would need, and it explicitly
tolerates sign flips ("the closest-triangle-normal sign is ... FP-fragile at
voxels (near-)equidistant to multiple triangles"), so it would not have caught
a wrong sign either.

To do this properly, in order:
  - chunk the grid into TDR-safe slabs (this is the actual blocker, and it
    applies to the brute-force path too);
  - then either a GPU BVH, or exploit the sign tolerance with a parity/winding
    test so only voxels within `band` of the surface need a real closest-point
    query -- the band clamp makes the magnitude cheap and the sign is the only
    thing forcing a global search;
  - and extend the parity test with a mesh large enough to cross the threshold.

### Shipped: PDE stencils (the backend had zero PDE coverage)

Auditing GPU op names against the CPU API found no `laplacian`, `divergence`,
`curl`, `gradient`, `central_diff_*`, `mean_curvature_flow`, `fast_sweeping` or
`solve_poisson` on the GPU at all, and no fp64 or vec3 grid support. Added the
five stencils, which is the bulk of the central-difference family:

| op | CPU reference | shapes |
|---|---|---|
| laplacian | `tvdb_laplacian` | scalar -> scalar |
| central difference x/y/z | `tvdb_central_diff_x/y/z` | scalar -> scalar |
| gradient | `tvdb_gradient` | scalar -> vec3 |
| divergence | `tvdb_divergence` | vec3 -> scalar |
| curl | `tvdb_curl` | vec3 -> vec3 |

Four GLSL shaders plus four NVRTC kernels, all matching the CPU reference
including its edge handling (reads clamp at the boundary, `tvdb_at`). The host
precomputes the scale (`1/h^2` for laplacian, `1/(2h)` for the central
differences) so the shader only multiplies, which keeps the two backends and the
CPU from each re-deriving it.

Verified against the CPU reference in `tests/test_gpu_pde.c`, on both backends,
on a deliberately awkward 17x11x5 grid with a non-round voxel size (0.37) so
that x, y and z are not interchangeable and the clamping is actually exercised.
Worst absolute error, Vulkan / CUDA: laplacian 3.8e-06, central diffs 2.4e-07 to
6.0e-08, gradient 2.4e-07, divergence and curl 4.8e-07 -- float epsilon against
field magnitudes of 0.6 to 15.6.

Two things worth recording:

* **Absolute, not relative, tolerance.** The laplacian first looked wrong at
  1.08e-05 *relative*. It is one voxel where the 7-point result cancels to near
  zero; the absolute error is 3.8e-06 on a scale of 15.6. The shader contracts
  multiply-add into FMA, so a relative tolerance is the wrong instrument for a
  stencil. This matches the convention the rest of the GPU suite already uses.
* **3D dispatch was missing.** `tvdb_vk_dispatch` only ever called
  `vkCmdDispatch(cmd, group_x, 1, 1)`, so no shader with a 2D or 3D workgroup
  could be launched through it. `group_y` / `group_z` were added (0 or 1 meaning
  1, so every existing call site is unchanged). This is also the blocker the doc
  previously noted for migrating the 17 shaders whose `local_size` does not match
  the 128 the engine hardcodes -- those can now be migrated, because the group
  counts are no longer forced into a 1D launch.

The CUDA path runs real kernels, not a CPU fallback. Getting there caught three
bugs worth naming, all of which the fallback would have silently hidden:

1. The three vec kernels' index macro parenthesised only part of the product,
   so it computed `3*(z*ny + y)*nx + x + c` instead of `3*((z*ny + y)*nx + x) + c`.
2. The shared launcher passes `(op, scale)`, but only the scalar->scalar kernel
   took `op`; the other three read the `int*` for `op` as the `float` scale.
   Fixed by making all four signatures uniform rather than special-casing.
3. A string-literal merge dropped the final `"}n"` line, so the whole CUDA
   program failed to compile -- and because the fallback is silent, every op
   still "passed" via the CPU path. That is the argument for making a fallback
   visible in a test run.

### Shipped: fp64, with a capability gate rather than a silent downcast

fp64 was entirely absent from the backend. It is optional in core Vulkan
(`shaderFloat64`) and runs at a small fraction of fp32 rate on consumer parts --
on the RTX 5060 Ti fp64 is 1/64 -- so the question is not just "add a double
shader" but "what should happen on a device that cannot".

The answer chosen: query the feature at context creation and return
`TVDB_ERROR_UNIMPLEMENTED` when it is absent. Computing in fp32 instead would
hand back different values than the caller asked for with no indication, which
for an op whose entire purpose is extra precision is worse than refusing.
`tvdb_gpu_supports_fp64()` exposes the answer so callers can choose a path.

Added `tvdb_gpu_stencil_scalar_d` (laplacian and the three central differences in
double), one GLSL shader and one NVRTC kernel, gated identically on both
backends. Verified by `tests/test_gpu_fp64.c` against a double-precision CPU
reference, both backends, on a 13x9x4 grid at voxel size 0.31:

| op | worst relative error |
|---|---|
| laplacian_d | 8.1e-14 |
| central_diff_x_d / y / z | 2.2e-16 |

The tolerance here is 1e-12, deliberately much tighter than the fp32 stencils'
2e-5: a tolerance loose enough to accept fp32 results would not be testing the
thing the op exists for. That the results come out at 1e-16 is the evidence that
the gate is not quietly downcasting.

The two std140 traps bit again and were caught the same way as before, by
checking the layout numerically before dispatching: `ivec4 dim` at offset 0
forces `double scale` to offset 16, and the struct is 32 bytes.

### Shipped: vec3 grid ops, and a static assert so std140 cannot regress again

The vec3 grid coverage in the backend was just `gradient`. Added the three
elementwise ops that have CPU references -- `magnitude` (vec3 -> scalar),
`normalize_vec` (vec3 -> vec3) and `cpt`, the closest-point transform
(scalar -> vec3, `p - d * grad`) -- as **op selectors on the stencil shaders
that already existed**, so this needed no new shader and no new kernel. `cpt`
reuses the gradient the scalar->vec shader was already computing; `magnitude` and
`normalize_vec` sit in the vec3->scalar and vec3->vec kernels respectively.

Verified in `tests/test_gpu_pde.c` against the CPU reference on both backends,
max absolute error 1.2e-07 to 9.5e-07 against a 2e-5 tolerance. The
`normalize` zero case is tested explicitly (seeded with an all-zero vector, and
asserted all-zero out) because the CPU reference writes zero rather than NaN
there, and a generic random field would never reach that branch.

**The durable fix: std140 layout is now asserted at compile time.** Adding
`grid_o` to the uniform block got it wrong a third time -- std140 aligns a
`vec4` to 16 bytes, so the C struct placed it at offset 20 where the shader read
offset 32. That produced `cpt` errors of 4.7, and only on Vulkan; the CUDA
kernel took the origin as a plain function argument and was unaffected, which is
exactly the kind of split that makes a bug look like a driver problem.

Three times is enough, so the uniform is now a named type with

```c
_Static_assert(sizeof(tvdb_stencil_uniform) == 48, ...);
_Static_assert(offsetof(tvdb_stencil_uniform, scale)  == 16, ...);
_Static_assert(offsetof(tvdb_stencil_uniform, grid_o) == 32, ...);
```

confirmed to fail the build when the padding is removed. Note `typeof` is a GNU
extension and is not available under the `-std=c11` this project uses, so the
struct is named.

The fp64 stencil uniform has the same shape of hazard (`ivec4 dim` forces
`double scale` to offset 16) and is written out and checked the same way, but is
not yet asserted -- worth doing.

### Shipped: mean curvature flow

`tvdb_mean_curvature_flow` had no GPU path. It turned out to be the tractable
member of the iterative PDE family: the CPU is **Jacobi** (each step copies the
grid to a snapshot, reads only the snapshot, writes only the interior), so the
steps are mutually independent and the GPU version is `iterations` dispatches
ping-ponging two device buffers. No in-place dependency, no workgroup algorithm.

Matched exactly, including the parts that are easy to get wrong:
- the `g2 < 1e-12` guard leaves the voxel untouched rather than dividing;
- boundary voxels are copied through, which the CPU does by never writing them
  (so the GPU shader has to write them explicitly or the ping-pong would drop
  the frame);
- the grid is a no-op when any axis is below 3.

Verified against the CPU reference over 4 iterations on a 13x11x9 grid, both
backends, max absolute error 4.8e-07 (Vulkan) and 4.2e-07 (CUDA) at a 1e-4
tolerance. Four iterations rather than one, because a stencil-order or
boundary mistake is invisible after a single step and compounds.

### The iterative PDE family, and why persistent dispatch still matters

`fast_sweeping` and `solve_poisson` are the remaining two, and both are
*Gauss-Seidel*: the CPU `fast_sweeping` reads `absphi` for the already-updated
neighbour along the sweep direction, so a step is sequential in x, y and z. A
bit-exact GPU port therefore needs a diagonal-wavefront decomposition, one
dispatch per plane, in order.

That is arithmetically hostile as things stand. An N^3 grid needs 8 directions x
3(N-1) planes per iteration: 1512 dispatches at N=64, 4584 at N=192. Measured
end-to-end cost of the cheapest op in the backend today is ~2 ms (buffer create,
upload, one dispatch, readback, destroy), so a N=64 iteration would be about 3
seconds and a usable solve is hopeless.

This is the one place the persistent-dispatch work is *not* capped at the ~4%
measured on bandwidth-bound ops. Those ops spend their time in the kernel, so
removing per-dispatch overhead barely moves them. A wavefront sweep is made of
thousands of *tiny* dispatches, where the fixed cost is essentially all of the
time -- so a persistent pipeline, descriptor set, command buffer and fence turns
a 3 s iteration into something competitive. That is the concrete argument for
the remaining priority-1 work, and it is a workload to design against rather than
a generic "50 ops to migrate" list.

### Shipped: deferred submit, and where the per-dispatch time actually went

This is the persistent-dispatch work (priority 1), done against a workload that
needs it rather than spread over 50 ops for a ~4% average.

`mean_curvature_flow` runs `iterations` dispatches. Measured per-iteration cost
on a 32^3 grid, before any change: **2777 us**. That is absurd for a kernel that
touches 32768 voxels, so it was worth finding out what it was.

| change | us/iteration | 256-iteration total |
|---|---|---|
| baseline (wait for a fence every dispatch) | 2777 | 708 ms |
| + deferred submit (one wait for the whole batch) | 592 | 150 ms |
| + pre-built descriptor sets for the ping-pong | 574 | 150 ms |

**The fence wait was 82% of it.** `tvdb_vk_dispatch` created a fence, submitted,
then blocked on `vkWaitForFences` before returning. A batch of N dispatches
therefore paid N blocking waits. The queue is single and in-order, so a batch
only needs *one* wait, at the end.

The mechanism is general, not an mcf special case: a dispatch with `defer_wait`
set returns as soon as the work is queued and parks its fence and command buffer
on the context; any non-deferred dispatch, or `tvdb_vk_flush`, drains first. So
correctness does not depend on the caller remembering to flush -- a deferred
batch is always completed before anything that could reuse its resources, and
context teardown drains it too.

**CUDA was worse, and the same fix applies.** `tvdb_mcf_cuda` was calling
`cuCtxSynchronize` after every launch, so it paid a blocking sync per iteration
even though launches go to the NULL stream and are executed in order. Batching
all launches and synchronising once:

| backend | us/iteration before | after | 256-iteration total |
|---|---|---|---|
| Vulkan | 2777 | 577 | 708 ms -> 150 ms |
| CUDA | 2306 | 2.9 | 621 ms -> 3.0 ms |

The CUDA number is the striking one: **~2.3 ms of pure synchronisation cost per
launch**, which was completely invisible before because every op in the backend
synchronises once anyway. It is why both backends showed almost the same
per-iteration cost for a kernel whose actual work is microseconds, and it is a
much larger absolute number than the Vulkan gap this whole phase started from.
Any other CUDA path that issues several launches in a row should get the same
treatment.

The second lever was smaller than expected and is worth recording as a negative
result: pre-building the two descriptor sets the ping-pong alternates between
(cutting `vkAllocateDescriptorSets` and `UpdateDescriptorSets` per iteration)
bought 592 -> 574 us, i.e. almost nothing. So the remaining cost is not
descriptor churn, and building out a full persistent descriptor cache would have
been wasted effort on this workload.

**What the remaining 574 us is.** Scaling the grid with the iteration count held
fixed:

| grid | voxels | us/iteration |
|---|---|---|
| 16^3 | 4096 | 588 |
| 32^3 | 32768 | 565 |
| 64^3 | 262144 | 1620 |

Flat from 16^3 to 32^3 and then rising 3x at 64^3. The flat part is the GPU
round-trip for a kernel too small to fill the machine, with the queue stalling
because only a submission or two can be in flight. The rise at 64^3 is memory:
each iteration re-reads the whole grid, and at 262144 voxels that is ~21 MB,
giving 1620 us, i.e. about 13 GB/s -- which is host-visible memory over PCIe, not
device-local.

That last point refines the device-local conclusion rather than contradicting it.
Device-local measured as a clear *regression* on output-bound kernels (sphere
9.7 -> 11.9 ms), where the result crosses PCIe once regardless. An iterative
read-iterative kernel is the opposite case: it re-reads its whole input every
iteration, so binding the grid device-local is the remaining lever here. Worth
doing deliberately, for read-iterative ops only, rather than as a blanket default
-- which is what the earlier blanket attempt got wrong.

Also fixed while doing this: the shared descriptor pool was created lazily inside
the dispatch, so a caller building a descriptor set *before* its first dispatch
passed a NULL pool and crashed inside the driver. Pool creation is now
`tvdb_vk_ensure_pools`, called from both paths, and the pool is larger
(1024 sets) since long-lived sets are no longer returned immediately.

### Shipped: device-local staging where it actually pays (2.0x at 64^3)

The blanket device-local mirroring was reverted earlier because it measured as a
regression. That verdict was right for the ops it was applied to, and the reason
generalises: a per-dispatch mirror copies in and out on *every* call, so for an
output-bound kernel the stage-in is pure waste -- the result crosses PCIe once
regardless.

An iterative kernel is the opposite case, because the transfer can be hoisted
out of the loop. `mean_curvature_flow` re-reads its whole grid every iteration,
so staging it into device memory once and staging the result back once removes
almost all of the PCIe traffic:

    stage in (1 copy) -> iterate `iterations` times in device memory -> stage out (1 copy)

Interleaved A/B, 256 iterations, Vulkan, alternating runs to cancel machine load:

| grid | host-visible | device-local staging | |
|---|---|---|---|
| 16^3 (4096 vox) | 226-234 ms | 231-241 ms | 2-4% worse |
| 32^3 (32768 vox) | 234-239 ms | 237-257 ms | neutral |
| 64^3 (262144 vox) | 504-557 ms | 252-256 ms | **2.0x better** |

So the two extra full-buffer copies are only worth paying once per-iteration re-read
traffic dominates. It is gated on `n >= 131072` voxels, between 32^3 and 64^3, and
falls back to host-visible buffers (still correct, just slower per iteration) when
the device-local allocation is unavailable.

This is the shape the earlier attempt should have had. The mechanism -- host
buffer stays the CPU side, `vkCmdCopyBuffer` for the transfers, explicit
`VkBufferMemoryBarrier` either side -- is the same; what changed is that the
transfers are amortised over a whole iteration count instead of paid per dispatch.
`VK_PIPELINE_STAGE_HOST_BIT` was added to the hand-declared ABI while writing this
and `test_vk_abi` immediately caught it declared as 0x2000 when the real value is
0x4000.

**Two bugs the lifetime gate caught, both in the new code:**

1. The deferred-submit context field was a *single* pending fence slot, so a batch
   that deferred several dispatches before draining orphaned all but the last
   fence and command buffer -- ~0.4 MB per batch. Now a bounded ring of 64, with
   the oldest drained when it fills. This only appeared once the gate was extended
   to `mean_curvature_flow`, which is the first op to defer more than one dispatch
   in a batch; the earlier 4-path test could not have found it.
2. Draining N fences one at a time cost 153 ms -> 222 ms for the same work, because
   a blocking wait costs ~2.4 ms whenever it actually has to block. Fixed by
   passing all pending fences to a single `vkWaitForFences`, which is also what the
   in-order queue allows: the last completing implies the earlier ones did.

Worth being explicit about a negative result from the same investigation: there
are 40 sites where a `cuCtxSynchronize` is immediately followed by a synchronous
`cuMemcpyDtoH`, which is arguably redundant. Measured on one of them, removing it
saved nothing, so the bulk edit was **not** made. The expensive waits are the ones
with outstanding work behind them; a single trailing wait is cheap. Only the
per-iteration waits were real, and those are fixed by batching.

### Build bug found while adding a shader

The SPIR-V `foreach` maps each shader name to a C array name. `sparse_conv_batched`
and the new `index_probe` had no `elseif` branch, and the `else()` fallback
silently reused the *previous* shader's array name, so a missing mapping emits an
`.inc` that redefines another shader's symbol. The `else()` is now a
`message(FATAL_ERROR)` naming the shader, so this fails at configure time instead
of surfacing later as a redefinition or a missing symbol.

### Two resource-lifetime bugs from sharing the pools

Both were found by measurement rather than by reading the code, and both are
worth recording because the obvious test suite passed through both.

**1. Shared descriptor pool exhaustion.** Caching one descriptor pool per
context removed 43% of the fixed per-dispatch cost, but the set was only
returned to the pool behind an `own_pool` flag that was 0 once the pool became
shared -- so sets were never returned. The pool has a fixed `maxSets`, and it
exhausted with `VK_ERROR_OUT_OF_POOL_MEMORY` after 85 calls of a rotating
three-op workload. The 44 parity tests never hit this because they do each op a
handful of times. Found by looping the ops inside one context.

**2. Command-buffer leak, the same shape, worse.** Sharing the command pool had
the mirror-image problem: Vulkan only reclaims a command buffer on pool reset or
`vkFreeCommandBuffers`, and a per-dispatch `vkAllocateCommandBuffers` against a
shared pool therefore accumulated them forever. Measured as **linear, unbounded
host RSS growth of ~0.34 MB per dispatch** (139 MB at 100 iterations, 2300 MB at
6400). Fixed by creating the pool with `VK_COMMAND_POOL_CREATE_FREE_COMMAND_BUFFER_BIT`
and freeing the buffer after the fence wait; RSS now plateaus at 187 MB and holds
from 1600 to 4000 iterations, matching `HEAD`.

Both are the same lesson: Vulkan resource lifetimes are the driver's business, and
sharing a pool silently changes who owns the resources drawn from it. The 44-test
parity suite is a correctness gate, not a resource-lifetime gate -- it needed a
repeat-loop harness to catch either of these.

### The index map, and porting it to CUDA

The four brute-force index kernels were replaced with a host-built
open-addressing ijk map. That work originally landed on Vulkan only, and CUDA was
left scanning the active set -- so the same algorithm was O(nq*na) on one backend
and O(1) per probe on the other, which is not a state worth leaving in. The map
is backend-independent by construction: the host inserts in increasing
active-index order, so the first insert into a slot wins and the +1 sentinel
gives first-seen semantics with no device-side atomic anywhere, and the hash is
three multiply-xor constants identical on both sides. So the same
`tvdb_index_map_build` output feeds a Vulkan `*_probe` shader or a CUDA
`*_probe` kernel unchanged.

That closes a coverage hole as much as a performance one. The 44-case suite's
active set is 64 voxels, well under `TVDB_INDEX_MAP_MIN_ACTIVE` (2048), so on
both backends it always took the linear scan and the map was never compared
against the CPU by anything. `test_gpu_index_map` now covers it on both backends,
with duplicates in the active set (so first-seen ordering is observable rather
than assumed), misses, negative coordinates, both connectivities, and sizes just
over and well over the gate. It also asserts its own active set clears the gate,
because otherwise raising the gate would silently turn it back into a
linear-scan test. Mutation checked: changing one hash constant in the CUDA probe
fails all eight of its sub-checks while Vulkan stays green.

CUDA, interleaved A/B of the same source with the map forced on and off, best of
5, 2^18 queries with a 50% hit rate, milliseconds:

| na | ijk_to_index | neighbor_counts(26) | points_in_grid |
| --- | --- | --- | --- |
| 4,608 | 18.9 -> 6.8 (2.8x) | 20.3 -> 4.6 (4.4x) | 16.6 -> 9.0 (1.8x) |
| 87,424 | 269.3 -> 17.1 (15.7x) | 1977.0 -> 11.7 (169x) | 263.8 -> 22.4 (11.8x) |
| 699,136 | 1957.5 -> 88.6 (22.1x) | 112593.5 -> 103.0 (1093x) | 1967.7 -> 97.0 (20.3x) |

`neighbor_counts` is the extreme case because the linear version does up to 26
full scans of the active set per active voxel, i.e. O(na^2 * connectivity) --
at na=699k that is 115 seconds against 0.1. A second round reproduced the same
ratios to within the noise.

The one measurement lesson here is worth recording: the first A/B appeared to
show no difference at all, because the "forced linear" build was built with
`-DTVDB_INDEX_MAP_MIN_ACTIVE=...` and a bare `#define` in the source silently won.
Both arms were running the map. Guarding the constant with `#ifndef` is what made
the comparison real, and the same guard is now on the deferred-submit switch.

The gate itself is shared by both backends. The crossovers differ (CUDA's linear
scan is cheap enough that the map starts winning near na=1000-1400; Vulkan's is
nearer 4000), so a shared 2048 leaves a little on the table for CUDA in a narrow
band. Lowering it for CUDA would need a per-backend gate, and the numbers say the
band is narrow enough that it is not worth the extra knob.

#### Two more things the map turned up

`test_gpu_index_map` includes a sparse-convolution case, and it needed one to be
meaningful: `tvdb_sparse_bbox` refuses a dense index grid above 4e8 voxels, so a
sparse grid scattered through a 1100^3 volume is the *only* way to reach the
map-probed conv path. On CUDA it is the only way to reach it at all -- the dense
path handles everything else -- so without that case the CUDA map conv would have
been unreachable code. (Dense for the dense case, map for the wide-sparse case,
brute force only for small inputs: that is now the same three-tier structure on
both backends.)

Writing that case surfaced a real pre-existing CPU bug. `tvdb_hash_build` in
`tinyvdb_sparse.c` probes with

```c
while (tbl[h].idx_plus_one) {
  if (tbl[h].key == key) break;   /* already indexed: keep the first one */
  h = (h + 1) & mask;
}
tbl[h].key = key;
tbl[h].idx_plus_one = (uint32_t)(i + 1);   /* ...and overwrite it anyway */
```

The `break` is reaching for first-seen, but the assignment after the loop runs
regardless, so a repeated coordinate ended up **last-wins**. Every GPU lookup
disagreed: the brute-force scan returns the first match in index order, and the
host-built map only ever fills an empty slot. This never showed up because no
test fed a sparse grid with duplicate coordinates. Fixed to first-seen, which is
what the code intended, and the conv case is now bit-exact (`worst rel 0.0`) on
both backends.

The same insertion loop is the reference for how first-seen is obtained without a
device-side atomic: the host inserts in increasing index order, so whoever gets
there first stays. That is the property the map's +1 sentinel and the `0 = empty`
convention exist to express.

### A build without glslangValidator was silently broken

Adding shaders without touching `tinyvdb_gpu_spv_fallback.inc` would have shipped
a build that does not compile: that file is the only SPIR-V source when
`glslangValidator` is absent, and it was missing `kTvdbGpuCsgDSpv` and
`kTvdbGpuSampleDSpv`. It is a hand-maintained symbol list (every array there is a
zero-length `{0}` placeholder, so ops correctly report UNIMPLEMENTED), which means
there is no compiler error to catch a missing entry until someone builds without
the validator. `test_spv_fallback_consistent` now compares the mapped array names in
`CMakeLists.txt` against the symbols in the fallback and runs in *both*
configurations, so the file cannot drift; all 65 agree. It checks both directions
-- a mapping with no symbol, and a symbol with no mapping -- because the second is
dead weight that would not be regenerated if the file were ever rebuilt from the
shader list.

That check is only worth having because it took a deliberate mutation to discover
it was broken. CMake's `MATCHALL` returns whole matches, and the first version
walked them with a consume-and-restart pattern that stopped after one iteration, so
it compared exactly one name out of 65 and reported "consistent". Dropping a symbol
changed nothing. A green result from a check that has silently narrowed its own
input is worse than no check at all, so it now refuses to report success unless it
parsed a plausible number of names, and dropping or adding a symbol each make it
fail.

The more interesting half is what happened once it compiled. Every GPU test
*failed* in a fallback build rather than skipping, because a context creates fine
and then every op returns `UNIMPLEMENTED` -- so all four faces ran and none was
distinguishable from a genuine regression. Three of those failures were
pre-existing (`test_gpu_pde`, `test_gpu_fp64`, `test_gpu_lifetime`), and two more
would have been mine.

Two things were needed. First, a way to tell "not built for this" from "broken",
which is now `tvdb_gpu_spirv_available()`; the tests skip on that and *only* on
that, so a real `UNIMPLEMENTED` in a proper build still fails. Skipping on
`UNIMPLEMENTED` alone would have been simpler and much worse -- it would hide a
capability check that started misfiring, which is exactly the kind of regression
`test_gpu_fp64` exists to catch. Second, `test_multi_gpu` was reaching a
Vulkan-only op from a CUDA context, because CUDA still creates a context in a
fallback build (its kernels are compiled at runtime) while `sparse_conv3d_batched`
has no CUDA path and no SPIR-V to fall back on.

Both configurations are now green: 33/33 with the validator, 33/33 without it, the
GPU tests running in the first and skipping in the second.

### mesh_to_sdf: slab chunking, and a test that can fail

`mesh_to_sdf` was the last brute-force kernel left, on either backend. It is still
O(voxels * faces) per voxel -- no BVH, no binning, same as before -- so the work
here was to make it *usable* and to make it *checkable*, and to be honest that the
algorithm itself is unchanged.

**Slab chunking.** One dispatch over the whole grid meant one kernel with millions
of threads each scanning every triangle, which is what came back as
`VK_ERROR_DEVICE_LOST` before. z is now split into slabs of at most
`TVDB_MESH_SDF_MAX_VOXELS_PER_DISPATCH` (1M) voxels and each slab is its own
dispatch, writing to its true global voxel index, so the assembled field is
identical to a single dispatch over the full grid. The per-slab uniform is
written up front into its own 256-byte slice with a pre-built descriptor set bound
to it, rather than rewritten between dispatches -- otherwise the host would have
to touch a buffer a queued dispatch still reads, forcing a wait per slab and
throwing away the point. Same pre-built-set pattern as the fast-sweeping planes.

Chasing that found another latent NULL-pool crash: the slab sets are allocated
before any dispatch in the call, so the shared descriptor pool may not exist yet.
`mesh_to_sdf` is normally preceded by other work that creates it lazily, so this
only fired when it was the *first* GPU call in a process -- which is exactly what
a standalone test does. `tvdb_vk_ensure_pools` is now called first.

**What it bought, measured** (spheres, CPU reference vs GPU, same build):

| mesh | grid | CPU | GPU | ratio |
| --- | --- | --- | --- | --- |
| 256 faces | 117^3 = 1.60M | 1056 ms | 201 ms | 5.3x |
| 256 faces | 175^3 = 5.36M | 3376 ms | 529 ms | 6.4x |
| 4096 faces | 108^3 = 1.26M | 3668 ms | 313 ms | 11.7x |

So the GPU path is genuinely 5-12x the CPU now, and 5.36M voxels completes where
the earlier note recorded a device loss at 4M. Chunking is also faster than one
big dispatch at that size (529 vs 785 ms, interleaved against a
`TVDB_MESH_SDF_MAX_VOXELS_PER_DISPATCH=1<<40` build of the same source), because
several smaller dispatches pipeline better than one very long kernel. To be
accurate: I could *not* reproduce the device loss on this machine even with the
one-slab build at 5.36M voxels, so the ceiling is raised rather than demonstrably
removed -- the watchdog threshold is driver- and workload-dependent.

**A test that can fail.** The suite's own `mesh_to_sdf` check is a 4-face
tetrahedron with up to 10% sign disagreement allowed, which cannot distinguish a
working kernel from a broken one: four faces and four thousand behave the same if
the voxel loop is right and the same if it is wrong, and 10% of 22k voxels is
2200 flips of latitude. `test_gpu_mesh_to_sdf` replaces that with 256 to 4096
faces, a non-cubic grid, a tight-band case that leans on the clamp, and a case
past the slab threshold, and it compares the two properties separately: the
unsigned distance field to 2e-5 (measured 1e-7, so ~200x margin) and sign
disagreement at 0.1% of voxels (measured 0.0003% to 0.082%).

Comparing signed values would have been the wrong test, and that was the first
version's bug: a sign flip on a band-saturated voxel *is* a 2x-band difference in
the signed value, so it reads as a distance error of 0.4 and the distance check
becomes unfalsifiable. Split, the same run reports `worst|df| 1.0e-07` alongside
18 flips, and the two constraints can fail independently.

Mutation checked: rewriting the shader to index as if there were one slab fails
only the chunked case (38% flips, `worst|df| 2.0e-01`) and leaves the five
single-slab cases green, which is the correct discrimination.

**Still not done: the algorithm.** O(voxels * faces) with 4096 faces is 4096
closest-point tests per voxel. A BVH would be the real fix, but it has to
reproduce the CPU's exact tie-break -- the CPU accepts a triangle only on a
strictly smaller squared distance, with the lower face index winning ties, and it
gets identical results to brute force by using that same rule plus an explicit
lower-index tie-break. A GPU bin that visits candidates out of face order would
pick a different triangle at exact ties and change both the distance and the sign,
so the bin needs an ordering-aware tie-break to be safe. The parity-based sign
alternative (use the band clamp to skip distant triangles, then get the sign from
ray parity for the rest) avoids the tie-break problem entirely and is the cheaper
path to a big win, but it is a different algorithm and wants its own parity test.

### mesh_to_sdf acceleration: a uniform bin grid, tried, measured, reverted

`mesh_to_sdf` is the last brute-force kernel left. It stays O(voxels * faces)
per voxel. A uniform bin grid over the triangles is the obvious thing to try, and
it was implemented and measured -- exactly, to 1e-7 against the CPU, on both
backends, at 256 to 4096 faces and up to 1.6M voxels. **It is slower than the
brute-force scan at every size measured, and gets worse as the mesh gets finer,
so it was reverted.** The numbers, because the failure is structural and worth
not rediscovering:

| mesh | faces | voxels | brute | binned | ratio |
| --- | --- | --- | --- | --- | --- |
| seg16x8 | 256 | 21,952 | 5.7 ms | 6.6 ms | 1.2x slower |
| seg32x16 | 1,024 | 1,601,613 | 130 ms | 175 ms | 1.3x slower |
| seg64x32 | 4,096 | 1,601,613 | 265 ms | 352 ms | 1.3x slower |
| seg64x32 | 4,096 | 2,744,000 | 436 ms | 556 ms | 1.3x slower |
| seg96x48 | 9,216 | 2,744,000 | 638 ms | 1,296 ms | 2.0x slower |
| seg128x64 | 16,384 | 2,744,000 | 904 ms | 3,105 ms | 3.4x slower |
| seg160x80 | 25,600 | 2,744,000 | 1,244 ms | 6,355 ms | 5.1x slower |

(The CPU reference for the same cases is 7.0 s to 17.5 s, so the shipped brute
GPU path is 5-12x the CPU. The binned path would have given that up.)

Why it degrades, which is the part worth recording: a bin grid prunes well when
the nearest triangle is *near*. Bin size is `extent / (4*faces)^(1/3)`, so for
16k faces on a unit sphere the bin is ~0.035 across. A voxel deep inside the mesh
has its nearest triangle ~0.5 away, so the ring expansion has to reach radius
`d/h` ~ 14, visiting `(2r+1)^3` ~ 24,000 bins at ~4 faces each -- about 10^5
candidates, versus scanning 16,384 faces directly. A uniform grid therefore
degenerates to O(faces) per interior query and gets *worse* as faces grow, which
is exactly the regime a bounding volume hierarchy exists to fix. Pruning by the
band clamp would bound the ring count at `band/h`, but then the sign for the
saturated voxels needs a second mechanism (ray parity), and that is a different
algorithm with its own failure modes on degenerate rays.

So the remaining work is a BVH, and this repository already has one: `tvdb_bvh_t`
in `tinyvdb_mesh.c`, with the traversal already written to reproduce the brute-force
result exactly (strict `dsq <` plus an explicit lower-face-index tie-break, and
node bounds used only to prune). Porting it is the right move -- the nodes are 40
bytes and the traversal is a stack walk -- and unlike a bin grid it will not need
to be re-derived from scratch.

Worth recording from getting the bin version *correct* first, since both bugs are
ones a plausible-looking implementation would ship:

- The early-out was off by one ring. At the top of iteration `r`, rings `0..r-1`
  are searched, so the nearest unsearched bin is at Chebyshev distance `r`, which
  makes the distance to it `l + (r-1)*bs` and `r*bs - l`. Using `r` and `r+1`
  over-estimates the bound by a full bin, so the search stopped a ring early and
  missed the true nearest triangle. The visible symptom was the dangerous kind:
  correct magnitudes, wrong sign on ~11% of saturated voxels -- a smooth field
  that looks converged.
- A transcription error in Ericson's voronoi-region test: `d4 <= d3` became
  `d4 <= 0.0`. That is the test for a different formulation, and it returns
  vertex `b` for a band of configurations, producing a closest point that is not
  on the triangle and a distance that is too small. Caught only by diffing the two
  shaders' `tri_closest` line by line once the bin grid was exact against the CPU
  but disagreed with the exhaustive GPU scan -- which is impossible unless one of
  them is wrong.

Also of note: a uniform grid is what made the *sign* reproducible at all. The
CPU picks the triangle minimising `(dsq, face index)` lexicographically, and a
bin grid visits candidates in an order unrelated to face index, so it needs that
predicate spelled out explicitly (and the per-candidate box reject must be `>`,
not `>=`, or a candidate that merely ties can still win on the index). That part
worked, and is exactly what a BVH port would need too.

### A reusable, device-resident index map: the priority-2 gap

The map is what makes the index ops viable, but it is rebuilt and re-uploaded on
every call, and at 699k active voxels that is ~25 MB of transfer plus a host-side
insert loop -- which is what the remaining Vulkan-vs-CUDA ratio was made of. Both
backends pay it equally, so the *ratio* between them was not the symptom; the
symptom was that the absolute time was dominated by something that does not
depend on the query at all.

So: `tvdb_gpu_index_map_create` / `_destroy` / `_active_count`, plus
`tvdb_gpu_ijk_to_index_mapped`, `tvdb_gpu_neighbor_counts_mapped` and
`tvdb_gpu_points_in_grid_mapped`. Build once, query any number of times. It is
opt-in -- the per-call entry points are unchanged, because they cannot know
whether the caller's active set is still the same buffer with the same contents,
and guessing would be a correctness hazard rather than an optimisation.

Interleaved A/B, best of 5, 2^18 queries at a 50% hit rate, per-call vs reusable:

| na | Vulkan ijk | CUDA ijk | Vulkan nbr(26) | CUDA nbr(26) |
| --- | --- | --- | --- | --- |
| 10,944 | 41-44 -> 11-13 ms (3.5x) | 2.8 -> 1.9 ms (1.5x) | 5-6 -> 1.8 ms (3x) | 2.1 -> 2.2 ms (1.0x) |
| 87,424 | 53 -> 11-12 ms (4.6x) | 6.1-6.4 -> 1.2 ms (5x) | 70-72 -> 4.8-5.3 ms (14x) | 5.3-6.4 -> 2.3-2.5 ms (2.5x) |
| 294,912 | 71-72 -> 11-12 ms (6x) | 12.9-13.8 -> 1.9 ms (7x) | 239-241 -> 16.6-17 ms (14x) | 15-16.7 -> 2.5-3.0 ms (6x) |
| 699,136 | 97.5-98.5 -> 11.4 ms (8.6x) | 29.8-31.2 -> 1.1-1.3 ms (25x) | 602 -> 38-42 ms (15x) | 35.5-36.5 -> 3.4 ms (10x) |

The reusable time is flat in `na`, which is the point: the map cost is gone and
what remains is per-query.

**Device-local, and it mattered twice.** The map itself is DEVICE_LOCAL --
write-once/read-many, which is exactly what device-local is for. The first version
left the *query scratch* host-visible, and the reusable query was a flat ~34 ms
on Vulkan at every active-set size. A flat cost independent of the map is the
signature of the transfer path, so the scratch moved to device-local too, with
staging copies in and out issued in the *same* command buffer as the dispatch, so
a query still costs one submit. That took Vulkan's reusable `ijk_to_index` from
~34 ms to ~11 ms, and the Vulkan-vs-CUDA ratio for it from ~25x to ~9x. (CUDA needs
no equivalent: `cuMemcpyHtoD` already goes to device memory.)

Three pipelines, not two: `ijk_to_index` and `points_in_grid` have the same
descriptor *shape* but are different shaders, and points reads 4 floats per point
where ijk reads 3 ints, under a different uniform block. Sharing one pipeline
between them ran the index probe for points queries. Similarly the aggregate probe
writes to binding 3 while the io probes write to binding 2, so two descriptor
sets exist rather than one set whose binding 2 gets rewritten around each
neighbor-counts call.

**Four real bugs found while building it**, all of which the new test catches and
three of which no existing test could:

- `tvdb_vk_run_copies` inferred each copy's *source* access mask from its index
  ("copy 0 is a host write, the rest are compute"). Copying three host buffers
  into device memory got a `SHADER_WRITE`/`COMPUTE_SHADER` source scope on copies
  1 and 2, which does not cover the transfer at all. Now the source and
  destination sides are explicit fields, each copy is bracketed producer->transfer
  and transfer->consumer, and `dst_access` names the *consumer's* mask -- the old
  code passed `TRANSFER_READ` for a compute consumer, which is not what a shader
  read needs. The two pre-existing callers were each passing a single copy whose
  barrier happened to be redundant, so neither noticed.
- A 2-set `vkAllocateDescriptorSets` with a single layout in `pSetLayouts`
  violates VUID-VkDescriptorSetAllocateInfo-descriptorSetCount-00301. On this
  driver that is not a tidy error, it is a segfault inside `libnvidia-glcore`.
  One layout per set costs nothing.
- The `VkWriteDescriptorSet` array held pointers into a `VkDescriptorBufferInfo`
  array declared *inside* the per-set loop body, so it was a use-after-scope by the
  time `UpdateDescriptorSets` read it. Hoisted.
- The device-side of the map's buffers is not allocated until the first query, and
  a query that finds the scratch "big enough" then hands `cuMemcpyHtoD` a null
  pointer. The scratch is now allocated at build time and only ever grown.

A fifth is a repeat of an earlier one: allocating descriptor sets before any
dispatch segfaults when the shared pool does not exist yet, so a build whose
first GPU call is `tvdb_gpu_index_map_create` faults. `tvdb_vk_ensure_pools` is
called first -- the same trap `mesh_to_sdf` fell into.

`test_gpu_index_map` now covers the reusable path on both backends: it agrees with
the CPU, with the per-call path it replaces, and across 4 differently-sized query
batches x 2 rounds with the three query kinds interleaved. The repetition and the
interleaving are deliberate -- the map is device-resident state, so a stale or
aliased buffer shows up as the *second* query disagreeing, not the first, and two
sets sharing one scratch would only misbehave when the kinds alternate.
`test_gpu_lifetime` runs it too, since it is the heaviest device-object path here:
three pipelines, two sets, a layout, and six buffers per map, created and
destroyed every iteration. 0.01 MB/iter at 1600 iterations, i.e. a plateau.

### Generalising deferred submit: measured, and mostly not a win

`defer_wait` is now applied to every multi-kernel chain, not just mean curvature
flow: dense morphology (an N-dispatch ping-pong), sparse erode (mark -> erode),
sparse dilate (mark -> scatter -> finalize), the conv transpose (scatter ->
finalize), and the fast-sweeping planes. Generalising it required a real fix
first: a deferred dispatch was returning its descriptor set to the pool
immediately after the submit, but a descriptor set is read at *execution* time,
so the pool could hand that memory to the next allocation while the dispatch was
still in flight. Sets are now parked with their fence and released in
`tvdb_vk_drain_pending`. The two original deferred callers both pre-built their
sets, so this never fired for them; it appears the moment the path is used by an
op that does not.

Having done it, the honest result is that the generalisation is **performance
neutral**, and it is worth knowing why. Interleaved A/B of the same source built
with `TVDB_VK_DEFERRED_SUBMIT` 1 and 0, best of 12, four rounds:

| op | deferred | not deferred |
| --- | --- | --- |
| dense dilate x8, 128^3 | 143.2 / 148.8 ms | 148.4 / 149.3 ms |
| sparse dilate x2, 885k active | 1045.9 / 1080.9 ms | 1050.8 / 1103.0 ms |
| sparse erode x2, 885k active | 368.4 / 371.9 ms | 361.4 / 373.5 ms |

Every difference is inside run-to-run variance. These chains are two or three
dispatches of ~10^6 voxels each, so the chain is GPU-bound and the host's one
wait per chain is amortised over ~50 ms of real work -- there is nothing left
to overlap. The mean-curvature-flow 4.7x came from the opposite regime: a long
chain of *tiny* dispatches where per-wait overhead was the whole cost.

So the rule the measurements give is: defer when the chain is long and the
dispatches are small, and expect nothing when either is not true. It is left
switched on in all of these paths because it is now correct and uniform and
costs nothing, but it is not a source of speedup, and `TVDB_VK_DEFERRED_SUBMIT=0`
is the A/B switch for anyone who wants to re-check. Signed flood fill is the one
loop that deliberately does *not* defer: it reads a counter out of mapped memory
each iteration to decide whether to keep going, so the host has to see it.

### GPU: still to do

1. The residual gap on single-dispatch ops is still per-dispatch cost plus
   host-side marshalling, not memory placement. The deferred-submit work removed
   most of the per-dispatch cost for batched ops; single-dispatch ops cannot
   benefit from batching because they have nothing to batch. The reusable
   index map is the one case where hoisting a per-call build out of a loop closed
   a large part of it (Vulkan `ijk_to_index` 98 -> 11 ms at 699k active voxels);
   no other op has a comparable per-call setup cost to hoist, which is why the
   same trick does not generalise.
2. Migrate the ops that bypass `tvdb_gpu_dispatch`; the engine hardcodes
   `block = 128`, but 17 shaders use 64 or 256, so migrating them as-is would
   silently under- or over-launch. (Note that `tvdb_vk_dispatch` itself now emits
   a shader-write -> shader-read barrier on every bound buffer, which those
   bypassing call sites still lack; any of them that chains two dispatches over
   the same buffer has the same stale-read bug the barrier just fixed.)
3. ~~`mesh_to_sdf` brute force~~ **Done, with a measured two-sided gate** -- see
   "mesh_to_sdf: a BVH port, and the crossover that bounds it". The brute-force
   scan remains the fallback for meshes outside the measured win band, and CUDA
   still uses it.
4. ~~Remaining coverage~~ **Closed**, completely: all 49 compute ops in
   `tinyvdb_ops.h` have a GPU path on both backends. `solve_poisson`,
   `solve_poisson_d` and `solve_poisson_dd` (see
   "Poisson CG on the GPU: correct, parity-exact, and slower than the CPU");
   `surface_area` / `volume` and their fp64 twins, *bit-identical* to the CPU in
   fp32 (see "surface_area and volume: the first bit-exact GPU reductions"); and
   `fast_sweeping_d` (see "Fast sweeping in fp64"). Every op in
   `tinyvdb_ops.h` now has a GPU path or a documented reason it does not. There
   is no vec3 sample on the CPU at all, so `sample_trilinear_vec_dense` was
   never a parity gap.
5. Assert the fp64 stencil uniform layout with `_Static_assert` as the fp32 one
   now is.
6. fp64 is covered for the scalar stencils, CSG, trilinear sample, the
   area/volume reductions and Poisson, all gated on `shaderFloat64`. Note the
   gate is Vulkan-only: NVRTC compiles `double` regardless, and testing the
   Vulkan field on the CUDA path rejects a path that works. fp64 on this
   consumer part runs at 1/64 rate, so these are for accuracy, not speed.
5. `test_gpu_lifetime` is now in ctest and gates RSS growth. It covers seven
   paths: the four map-backed ones, mean curvature flow (device-local staging),
   fast sweeping (128 pre-built descriptor sets per call) and dense dilate (a
   fresh descriptor set per iteration, now parked with its fence). Extend it as
   further device-object paths land. Poisson is the next candidate: it builds
   seven device buffers per call and runs 1200+ iterations, so its host-visible
   traffic is the largest per-call setup in the backend.

### Fast sweeping on the GPU (done)

`fast_sweeping` is now a real wavefront implementation rather than a CPU
fallback. The CPU reference is Gauss-Seidel: within a sweep direction it walks
voxels in index order, so an update reads the already-updated value of the
neighbour it has already passed. Ordering voxels by
`L = dir.x*ix + dir.y*iy + dir.z*iz` makes every voxel on a plane read only
levels strictly below its own -- which is exactly the set the serial sweep has
already written -- so each of the 8 directions becomes a sequence of
independent planes, launched in order from a pre-built descriptor set per plane
(one set per plane, each bound to a 256-byte slice of one uniform buffer). The
result matches the serial reference voxel for voxel, not merely to the same fixed
point.

Three bugs, all found by comparing against the serial sweep rather than by
convergence, and all worth recording because the first two are silent:

1. **`uint frozen[]` against a byte-per-voxel upload.** The shader declares the
   frozen mask as a `uint` array, so std430 makes each element four bytes, but
   the host was uploading one byte per voxel. Each thread therefore read four
   voxels' bytes at `4*gid`, which both mis-gathered the flag -- any voxel whose
   4-byte window touched a frozen voxel was treated as frozen -- and ran past
   the end of the declared descriptor range. Effect: propagation stopped one
   step from the seed, and the result was a smooth, plausible, wrong field.
2. **Write-back overwrote frozen voxels.** The device buffer only ever holds
   `|phi|`, and the result was copied over the whole grid before the signs were
   reapplied, so every frozen voxel came back with a positive magnitude instead
   of its original signed value.
3. **No memory barrier between dispatches.** `tvdb_vk_dispatch` bound, dispatched
   and submitted but never emitted a barrier, and the only barriers in the file
   were the ones in the copy helpers. Queue submission order orders *execution*
   but supplies no dependency between one dispatch's shader writes and a later
   dispatch's reads, so every kernel chain that iterates -- mean curvature flow,
   the fast-sweeping planes -- was relying on undefined behaviour. Fixed once in
   `tvdb_vk_dispatch` for all buffers, covering every op rather than patching
   each chain; the barrier is free because dispatch N+1 depends on N anyway.

The remaining difference from the CPU is the `sqrt` in `godunov`: GLSL allows up
to 2 ULP against libm's `sqrtf`, and a single-seed field is a chain of ~range/h
updates, so the spread grows with the field's extent (~1e-6 relative on a 3x3
box, ~2e-5 on a 23-unit one). `test_gpu_fast_sweeping` derives its tolerance
from that bound and separately caps it at 1e-3 relative, so a wrong plane order
(which would be an O(range) disagreement) cannot pass. The test is mutation
checked: reinstating the byte-per-voxel mask fails 6 of its 9 cases.

Coverage: `tests/test_gpu_fast_sweeping.c` on both backends, plus
`test_gpu_lifetime` now runs it too, because it allocates 128 descriptor sets
per call against a shared pool with a fixed `maxSets`.

CUDA still routes `fast_sweeping` to the CPU. It has to, to stay bit-compatible:
matching the serial Gauss-Seidel sweep needs the same wavefront decomposition,
and a parallel Jacobi iteration would converge to the right answer but would not
reproduce the reference the parity suite is written against.
6. Host/shader struct layouts (std140 uniform blocks in particular) are agreed
   by hand and unenforced. `test_vk_abi` covers the Vulkan ABI but not these;
   a generated header from the `.comp` source would close the gap.
4. Fix the brute-force kernels (`ijk_to_index`, `points_in_grid`,
   `neighbor_counts`, `sparse_conv`, `mesh_to_sdf`). The first four are done on
   **both** backends via the shared host-built map -- see "The index map, and
   porting it to CUDA" above. `mesh_to_sdf` is slab-chunked and now 5-12x the CPU
   but is still a per-voxel scan of every triangle; see item 3 above.
5. Add the missing op coverage (PDE ops, fp64, vec3 grids, sparse tree).
2. **`to_nanovdb` O(children) scans** at `to_nanovdb.c:456/532/645`; convert
   time is currently comparable to load time.
3. **Sparse tree is still fully serial** (build, dilate, leaf iteration), and
   has two algorithmic defects: insertion sort over up to 32768 children per
   internal node, and a bit-at-a-time child-mask scan.
4. **Splat uses `omp atomic` per tap** -- 8 and 27 `lock xadd` per point.
5. **Fast sweeping** could become plane-red-black wavefronts.
6. **Marching cubes parallel restructure** -- real but low value (see above).
7. **GPU work** has not started.
2. **`to_nanovdb` O(children) scans** at `to_nanovdb.c:456/532/645`; convert
   time is currently comparable to load time.
3. **Sparse tree is still fully serial** (build, dilate, leaf iteration), and
   has two algorithmic defects: insertion sort over up to 32768 children per
   internal node, and a bit-at-a-time child-mask scan.
4. **Splat uses `omp atomic` per tap** -- 8 and 27 `lock xadd` per point.
5. **Fast sweeping** could become plane-red-black wavefronts.
6. **GPU work** has not started.

Note that all the CPU parallel gains above require `-DTINYVDB_OPENMP=ON`, which
is still OFF by default.

Note that `TINYVDB_OPENMP` is still OFF by default; the parallel gains above
require `-DTINYVDB_OPENMP=ON`.


### mesh_to_sdf: a BVH port, and the crossover that bounds it

The remaining brute-force kernel is now a GPU traversal of the *same*
`tvdb_mesh_bvh_t` the CPU query uses, so the tree and its lexicographic
`(squared distance, face index)` tie-break are shared rather than re-derived.
Results are bit-for-bit identical to the exhaustive scan on every case in
`test_gpu_mesh_to_sdf`, down to the sign-flip counts, on both backends.

Interleaved A/B, 2.7M-voxel grids, so the mesh is the only variable:

| mesh | faces | brute | BVH | verdict |
|---|---|---|---|---|
| 64x32 sphere | 4,096 | 427-435 ms | 288-357 ms | BVH **1.2-1.5x** |
| 96x48 sphere | 9,216 | 607-628 ms | 492-527 ms | BVH **1.2x** |
| 128x64 sphere | 16,384 | 879-913 ms | 1038-1101 ms | brute 1.2x |
| 160x80 sphere | 25,600 | 1232-1272 ms | 1962-1990 ms | brute 1.6x |
| 128x64 sphere | 16,384 | 4026-4111 ms | 3195-3340 ms | BVH **1.27x** (12.8M voxels) |

The hierarchy stops paying above ~10k faces, and the reason is the tree the
existing build produces: a median centroid split on a level-set shell, where
every centroid lies on the same thin surface, gives depth 22-31 for 2k-16k
faces -- roughly 2.5x log2(n) instead of log2(n). The walk is a serial
dependent-load chain, so its cost tracks that depth, and past ~10k faces it
exceeds what the scan saves.

So the gate is two-sided and both bounds are measured: `faces <= 10240` uses the
BVH, above that the exhaustive scan runs. Note the gate is genuinely
two-dimensional -- at 16,384 faces on a 12.8M-voxel grid the hierarchy wins
again (a bigger grid amortises the node buffer) -- and no single threshold in
`faces * voxels` fits those points, so that corner falls back to the scan. A
better build (SAH, or a BVH over triangle *edges* rather than centroids) would
move the upper bound out; the traversal is not the limitation where the tree is
shallow.

A depth mismatch cannot produce a wrong answer: the host compares the tree's
measured `max_depth + 1` against the shader's 48-entry stack and declines (falls
back to the scan) if it would not fit, so a disagreement costs speed only.

### Two driver-visible bugs from the BVH port

1. **`VK_ERROR_DEVICE_LOST` from an infinite walk.** The node buffer is typed
   `float nodes[]` so the 40-byte record can be read at a 4-byte stride, and the
   four `int32` child indices are recovered with `floatBitsToInt`. Writing
   `int(nodes[b + 6u])` instead converts the float *value*, not the bit pattern,
   so every child index collapsed to 0 and the traversal followed node 0 into
   itself forever. The driver reported this as a device loss, not a wrong
   answer. Reinterpreting is exact for every int32 including the -1 leaf marker
   (0xFFFFFFFF is a NaN, and `floatBitsToInt` of it is -1).
2. **std140 `ivec2 pad0` pushed the uniforms 8 bytes later than expected.** The
   first `_Static_assert` on the CG uniform had already caught the same class of
   bug in the fp32 stencil, so it was caught again immediately here: the node and
   prim counts land at 56 and 60, not 48 and 52, and the block is 64 bytes.

### surface_area and volume: the first bit-exact GPU reductions

`tvdb_surface_area` and `tvdb_volume` (and the `_d` twins) count a per-voxel
predicate and scale the count once at the end. That makes them the first GPU ops
in the backend whose result can be *exactly* equal to the CPU rather than close,
and `test_gpu_measure` asserts bit equality (float bit patterns, modulo +0/-0)
instead of a tolerance.

The reason it is exact rather than nearly exact is a width trap: the CPU
accumulates into a `double` and casts to float on return, so the GPU must too. A
fp32 accumulator stops being exact above 2^24 crossings, which ~50M faces of
crossing count reaches on a 256^3 grid. `test_gpu_measure` includes a 181^3
checkerboard with **17,692,740** crossings -- past 2^24 -- and the result is
still bit-identical, so a reduction that accumulated in the input's own width
would fail it and nowhere else.

The two API families are deliberately *not* unified: the fp32 CPU ops test
`<= 0` and the fp64 ones test `< 0`, so they disagree on exact zeros. The
`zeros-8x8x8` case is what pins that; a "harmonisation" would be a silent
behaviour change.

The reduction is two dispatches over one partials buffer, ordered by the
per-dispatch shader-write -> shader-read barrier. Two bugs here are worth
recording because both produced plausible-looking numbers rather than crashes:

- `partials[gid]` instead of `partials[gl_WorkGroupID.x]`: indexing by the
  global invocation id strides the array by 256, so every workgroup past the
  first wrote outside the range the reduce pass reads. The result was a
  correct-looking fraction of the true count (64 instead of 128, exactly half,
  for a 512-voxel grid).
- The reduce was originally two workgroups writing back to `partials[0]` and
  `partials[1]`. With `ngroups > 1` that is a race -- workgroup 0 is still
  reading `partials[1]` when workgroup 1 overwrites it, and two workgroups in
  one dispatch share no barrier. It is now a single workgroup with two 128-lane
  halves, which removes the question entirely.

### Poisson CG on the GPU: correct, parity-exact, and slower than the CPU

`solve_poisson` and `solve_poisson_d` are implemented on both backends: one
shader for the whole iteration, selected by a phase code, with the stencil fused
into the dot product that consumes it (the unfused form is six dispatches per
iteration, each re-reading the whole grid).

Parity is exact on all six `test_gpu_poisson` cases on both backends: identical
iteration counts, and relative residuals agreeing to 1-2 significant figures at
the requested tolerance (e.g. 1.0469e-05 vs 1.0453e-05 at 58 iterations).

**And it is much slower than the CPU**, which is worth stating plainly:

| grid | CPU | GPU | ratio |
|---|---|---|---|
| 32^3 | 19.9 ms | 689 ms | 0.03x |
| 64^3 | 413 ms | 1439 ms | 0.29x |
| 128^3 | 45468 ms | 71782 ms | 0.63x |

The cause is measured, not guessed: a minimal one-dispatch-and-sync round trip
on this machine costs **~4 ms** (2000 iterations of `tvdb_gpu_grid_checksum` on a
single-voxel grid: 7.9 s). CG needs two host round trips per iteration, because
`alpha` cannot be formed until `<p, Ap>` is reduced and `beta` until `<r, z>` is,
so the floor is ~8 ms per iteration regardless of grid size. The CPU does a
32^3 iteration in 0.16 ms. The crossover would need a sweep to exceed the
latency, i.e. roughly 5e8 voxels, which is beyond what five fp32 arrays fit in
memory.

So this op is coverage, not acceleration. The port was still worth making: the
iteration is a read-only stencil plus two reductions, which is the shape the
whole backend is built for, and the host round trip is per *iteration* rather
than per *op* -- a caller solving a sequence of Poisson problems amortises
nothing, but the structure is now in place if the sync path ever gets faster.

One honest caveat: at 96^3 the CPU needed 1191 iterations and the GPU 415. The
smaller cases match exactly, but past roughly a thousand iterations in fp32 the
tree-ordered reduction and the CPU's OpenMP `schedule(static)` partials diverge
enough that the convergence test fires at different points. Both converge; they
just stop counting differently. A per-voxel comparison at equal iteration count
would be the check for a future grid where the sweep actually dominates.

Four bugs here were all in the same family -- fp32 in, fp64 workspace, and one
of the two ends got the width wrong:

1. The `_d` path memcpy'd `n * sizeof(double)` **into the caller's fp32
   `x->data`**, a 2x heap overflow. Fixed by narrowing element-wise on the way
   out.
2. The same path uploaded `n * sizeof(double)` **out of the caller's fp32 `rhs`
   and `x`**, a 2x over-read that filled every double's upper 4 bytes with
   garbage. That is where the fp64 NaNs came from. Fixed by widening into
   staging.
3. The CUDA launcher passed 13 arguments to a 17-parameter kernel -- `phase` and
   the three grid dims were missing -- so every scalar was shifted by one slot
   and the kernel read far out of bounds.
4. `lap_mode` was set once per solve on CUDA, so the `_d` *iterations* used zero
   Dirichlet; `tvdb_solve_poisson_d` clamps inside the loop and only its initial
   residual is zero-Dirichlet. It is per-dispatch on both backends now. The
   symptom was converging in 17 iterations where the CPU took 23.

#### The test almost "fixed" a correct CPU op

Worth recording as a process failure. The first version of the residual check
indexed the y-neighbours as `(z * cym)` instead of `(z * ny + cym)`, dropping
both the plane stride and `y`, so most voxels read a neighbour from the wrong
plane. That made the measured residual garbage, and it reported the CPU's
correctly-converged solution as having a residual **6.5x larger** than its own
initial one. A second probe independently made the identical index error.

Taken at face value, that says `tvdb_solve_poisson` diverges -- and the obvious
response would be to "fix" the GPU to match a phantom bug in a reference
implementation. It took a hand-computed double-precision PCG step to settle it:
the CPU's first step matches to 2.7e-14, and the operator is correct.

Two guards came out of that, and both are in the shipped test:

- an *absolute* progress check (the residual must fall as the budget grows, and
  must reach the requested tolerance) so a wrong measurement cannot masquerade
  as a diverging solver;
- the clamp-to-edge Laplacian is singular (constants are in its null space), so
  only a mean-zero rhs is consistent. Without the mean removal both solvers
  "converge" to garbage and any residual comparison between them is meaningless.

### Fast sweeping in fp64

`tvdb_fast_sweeping_d` is the same wavefront decomposition as the fp32 path at a
different element width, so the shader is a mechanical twin and the ~200-line host
driver is *shared* rather than duplicated -- every width-dependent quantity comes
from one `esz`/`is_d` pair. The plane enumeration, the pre-built per-plane
descriptor sets and the deferred submit are all unchanged.

The accuracy improves as it should, since the arithmetic is now genuinely fp64
rather than an fp32 sweep with a wider accumulator:

| case | fp32 max abs diff | fp64 max abs diff |
|---|---|---|
| 8x8x8, band 0.5 | 3.099e-06 | 1.192e-07 |
| 13x7x11, band 0.4 | 2.146e-06 | 1.192e-07 |
| 32x24x20 single seed, h=0.10 | 9.012e-05 | 2.374e-07 |
| 24x40x16 single seed, h=0.05 | 6.223e-05 | 1.190e-07 |

The single-seed cases are the interesting ones: the fp32 error grows with the
number of chained updates (`scale/h` steps), and the fp64 error does not.

**The one place fp64 is not simply "the same, wider".** The convergence
accumulator `max_change` has to be reduced on the device, and the fp32 shader
gets that for free from `atomicMax` over a 32-bit float pattern. The fp64 shader
cannot: GLSL has no `uint64_t` (that is `ARB_gpu_shader_int64`, which would also
need `GL_EXT_shader_atomic_int64` and therefore a device-creation change) and
`union` is a *reserved word*, so the 64-bit pattern cannot be reinterpreted at
all. Asking for both extensions was rejected: it adds a new device-creation
dependency for one op, and a device without them would then fail the whole
backend rather than this one function.

Instead the shader tracks the **high 32 bits** of the pattern, computed
arithmetically with `frexp` (d = m*2^e with m in [0.5,1), so the biased exponent
is e+1022 and the top 20 mantissa bits are (m-1)*2^20 -- which is exactly the top
half of the pattern). The host rebuilds a value with `ldexp`, good to 2^-20
relative. That is an **under**estimate, so the direction of the error is safe:
`max_change <= tol` can fire up to 1e-6 relative late and never early. The parity
test therefore allows the iteration counts to differ by one while still requiring
the field to match to the same bound as fp32. In practice the counts matched
exactly on all five fp64 cases.

### solve_poisson_dd, and comp_max/min/sum/mult

`solve_poisson_dd` is **not** the fp32-in/fp64-internals twin of
`solve_poisson_d`; it is a different algorithm, and porting the `_d` one and
calling it a match would have been wrong in three ways:

| | `tvdb_solve_poisson_d` | `tvdb_solve_poisson_dd` |
|---|---|---|
| tolerance | `tolerance^2 * r0^2`, relative to the initial residual norm | `tolerance^2`, **absolute** |
| convergence test | `rr < tol2` | `rr <= tol2` |
| final iteration | updates `p = z + beta p`, then breaks | breaks **before** forming `beta` or updating `p` |
| initial residual | zero Dirichlet | clamp-to-edge |

The first two are why a first attempt returned 43 iterations where the CPU took
47: the GPU applied the relative criterion, which is looser here, and so stopped
earlier. Once `abs_tol` and `init_zero_dirichlet` are separate per-call flags the
two agree exactly -- 47/47 iterations and a worst elementwise difference of
**3.3e-16**, i.e. fp64 round-off.

The break placement matters for a second reason that is easy to get backwards:
breaking *before* the `p` update means `rz` and `p` must still be refreshed on
every *non*-converged iteration. An early version that only did the beta/p update
inside the relative branch never advanced `rz` in the absolute branch, so
`alpha` stayed at its initial value and the solve ran to the full 400-iteration
budget without converging.

`comp_max/min/sum/mult` are one shader with an op selector. The interesting part
is not the arithmetic but the two contracts that a plausible kernel would get
wrong, both of which `test_gpu_comp` pins:

- **The shape mismatch is a no-op, not a clamp.** All four CPU ops start with
  `if (!same_shape(a,b) || !same_shape(a,result)) return;` and leave `result`
  untouched. Clamping b's extent -- the convention most of the other kernels
  here use, because their stencils read neighbours -- would produce a whole
  field where the CPU produces none. The host rejects the mismatch and returns
  `TVDB_OK` with `result` untouched.
- **NaN goes through the CPU's ternaries.** `va > vb ? va : vb` keeps `va` when
  the comparison is false, so it returns `va` for a NaN in `a`. `fmax(NaN, y)`
  returns `y`. The difference is a whole voxel of a field, and it is exactly the
  kind that a max/min op sees in practice on a grid with an undefined region.

All four are bit-identical to the CPU on both backends.

Two more bugs in this batch, both from writing the CUDA path against the GLSL by
hand rather than sharing the mechanism:

- The CUDA `comp` kernel took a fifth parameter, `n`, that the dispatch spec has
  no binding for, so it read whatever followed in the argument list. Deriving `n`
  from the bound uniform removes the possibility entirely.
- `solve_poisson_dd`'s CUDA path needed no widening buffer, but the source
  pointers still pointed at one: `cuMemcpyHtoD` got a null `src` and
  `(double*)NULL + n` for the rhs.

And one that is worth singling out because it produced a wrong answer with no
diagnostic anywhere: generalising the CG write-back from "narrow if fp64" to
"narrow unless the caller wants fp64 out" made the **fp32** path read its float
device buffer through a `const double*`. The condition has to key off the
*device* element width (`is_d`), not what the caller asked for.

### Advection: the last PDE-shaped op

`tvdb_advect` is the one remaining op in the stated coverage scope (a PDE
operator on a **vec3** grid), and it ports directly: every scheme is a pure
per-voxel gather, so the whole family is embarrassingly parallel.

One shader, four ops, sequenced by the host exactly as the CPU sequences them:

| op | what it does | passes |
|---|---|---|
| 0 | `out = sample(field, rk_backtrace(vel, ix, iy, iz))` | RK1-4 in one; the two round-trip passes for MacCormack/BFECC |
| 1 | `out = clamp_to_stencil(phat + 0.5 * (field - pstar))` | MacCormack |
| 2 | `out = field + 0.5 * (field - pstar)` | BFECC's error correction |
| 3 | clamp `out` in place to the 8 corners at the backtrace point | BFECC + clamp |

The two contracts worth naming:

- **Both samplers clamp.** `tvdb_at` and `tvdb_vec_at` clamp the *index*, so a
  backtrace that leaves the domain -- which it does whenever `|dt| * |v| / h`
  exceeds one voxel -- repeats the edge value. A zero-fill would put a hard wall
  where the CPU has a constant extension. The test therefore includes cases at
  `|dt|*|v|/h` of 0.5, 1, 2.5 and 80; a zero-fill agrees on the first and fails
  the rest.
- **A shape mismatch is a no-op.** The CPU returns without writing, so `result`
  is left untouched. Verified, along with `TVDB_ERROR_INVALID_ARGUMENT` for an
  unknown scheme -- which is a deliberate divergence, since the CPU has no scheme
  validation at all and silently treats anything past RK4 as BFECC.

Two bugs, both from writing the CUDA path by hand against the GLSL:

- The MacCormack/BFECC round trip was re-advecting **field** on the backward
  pass instead of **phat**, so the "error" term was meaningless. The four RK
  schemes matched to 2e-07 while the error-compensated ones were off by ~5e-2 on
  a field of scale 1.2 -- the kind of gap that reads as numerical noise and is
  actually a wrong algorithm.
- The CUDA kernel read `inv_h` and `dt` from `u[6]` and `u[7]`, which are
  `cfg[2]`/`cfg[3]` and therefore zero. The backtrace became a no-op and the
  kernel returned the un-advected field, again ~5e-2 off. The uniform is
  `{int dim[4]; int cfg[4]; float inv_h; float dt; uint nvox;}`, so they are
  `u[8]` and `u[9]`. Reading a uniform by int index is exactly the mistake the
  `_Static_assert`s elsewhere in this file guard against for *offsets*; here the
  offset was right and the *index* was not.

All six schemes now agree with the CPU to 2.4e-07 absolute on a field of scale
1.19, on both backends.

### Filters, and the last op with no GPU path

`mean_filter`, `gaussian_filter`, `laplacian_filter` and
`advect_semi_lagrangian` are the remaining `tinyvdb_ops.h` compute ops without a
GPU path. All four are one shader with three ops, and all three are exact
transcriptions of the CPU's *orderings*, which is where the real content is:

- The separable filters run **one axis at a time through ping/pong buffers**
  (`grid -> ping -> pong -> grid`), not as a fused 3-D pass. A fused pass is a
  different filter, not a faster version of this one. The first version of this
  fed every axis the same input, which keeps only the z pass and silently drops
  the other two -- and it *agreed with the CPU for one iteration*, because the z
  pass happens to be the last one written. Two and three iterations diverged by
  0.19 and 0.31 on a field of scale 3.5.
- The Laplacian filter is **Jacobi**: each voxel reads the previous generation
  from a scratch buffer and the buffers are swapped between iterations. In place
  would be Gauss-Seidel, which is order dependent.
- `advect_semi_lagrangian` reads the velocity at the voxel itself; the RK family
  in `tvdb_gpu_advect` interpolates it. That is the entire difference between it
  and op 0 of the advect shader, and getting it wrong is a plausible-looking
  small error rather than an obvious one.

Edge handling clamps the *index* (`tvdb_at`), so an overhanging tap is evaluated
at the boundary voxel instead of the kernel being renormalised over the in-range
taps. The two differ wherever the field is not locally constant, and the corners
are where they differ most -- the `nx == 1` and `20x20x4` shapes exist to put
that under the test.

The test that caught the axis-chaining bug also had a bug: it computed the
tolerance scale from a freshly `malloc`'d buffer before filling it, so the
tolerance was derived from uninitialised memory. That is worth noting because it
made the *correct* one-iteration cases fail and would have made a wrong
implementation pass on a large "scale".

Final agreement is 1.2e-07 to 1.8e-07 absolute on a field of scale ~1, on both
backends, across five shapes and four (width, iterations) combinations.

`median_filter` was left as the last known gap and is now done too, so every
compute op in `tinyvdb_ops.h` has a GPU path.

It is a **coverage port, not an accelerated one**, and the two properties are
separated deliberately:

- *Exact.* The CPU's `tvdb_select_kth` returns the element a full sort would place
  at `n/2`, which is order independent, so a completely different algorithm can
  match it bit for bit. This one counts ranks: for each candidate `j`, how many
  window elements are strictly below it and how many are at or below it, and the
  answer is any `j` with `below[j] <= k < below[j] + eq[j]`. The test asserts bit
  patterns, not a tolerance. NaN is the exception on both sides -- `tvdb_cmp_float`
  returns 0 when neither `a<b` nor `a>b` holds, which is not a total order, so a
  NaN-containing window is undefined for the CPU too and is not claimed to match.
- *Slow.* Rank counting is `O((2r+1)^6)` comparisons per voxel. A bitonic sort of
  the padded window would be `O(n log^2 n)` but needs 128-512 floats of private
  memory per thread, which does not fit. The practical port is the rank count.

`radius` is bounded at 2, which the shader's 125-float private window implies;
above that it reports `UNIMPLEMENTED` rather than silently using a smaller window,
since that would be a different filter. The CPU accepts any radius. Getting the
bound right also forced the filter shader's workgroup down to 32 threads -- at 64
the median op's window alone is 16 KB of private memory per workgroup -- so the
host now sizes `group_count_x` for 32 and lets the CUDA path's hardcoded 128
threads launch 4x the blocks it needs, which the kernel's bounds check discards.

The test filters a salt-and-pepper field rather than the smooth one used for the
other ops: a smooth field's median is nearly a no-op, so a wrong window gather or
a wrong index would be invisible. Bit-identity on that field is what makes the
claim worth anything.

### Deferral generalised to the dispatch engine, and why advect still does not use it

`tvdb_gpu_dispatch` -- the cross-backend abstraction the newer kernels (comp,
advect, filters) are written against -- now supports `spec->defer` plus
`tvdb_gpu_dispatch_flush`. Deferring hands the VkBuffers to a small queue that
owns them and destroys them at the flush, because a queued command buffer still
references them and Vulkan requires them to outlive it. Holding a pointer to the
dispatching frame's buffers instead would be a dangling reference; the queue
copies them by value.

**The new ops do not set `defer`, and that is a measured decision rather than an
omission.** Advection is the obvious candidate -- MacCormack is four
grid-wide passes and a host round trip costs ~4 ms on this machine -- but every
multi-pass op here is a *ping/pong* chain: each pass writes a host scratch buffer
that the next pass reads. A queued dispatch sees whatever the host has written by
the time it executes, so deferring the chain would feed pass N+1 pass N's
*inputs* instead of its output. The result is wrong with no diagnostic.

Making it defer requires the ping/pong buffers to be device-resident, which is
the reusable-index-map machinery rather than a flag. So the flag exists, is
tested by the existing multi-dispatch chains that do defer (fast sweeping, whose
368 planes per iteration are all device-resident and pre-bound), and is
deliberately left unset where a host round trip is the only correct option.

**One bug worth recording from this change, because it failed silently.** The
first version put `st = tvdb_vk_dispatch(...)` inside the `if (spec->defer)`
branch. Every non-deferred call then skipped the dispatch entirely while `st`
stayed `TVDB_OK` from the buffer-creation loop, so `comp_*`, the filters and
advect all "succeeded" while reading back buffers nothing had written. It showed
up as four test binaries failing with plausible small errors rather than as a
crash, because the readback was of uninitialised host memory. The immediate path
must dispatch unconditionally; only the buffer ownership and the readback
placement differ.

The queue is file-scope rather than per-context, which is fine for the workloads
that use it (a few grid passes inside one op) and is a real limit rather than an
accident: two contexts deferring concurrently would share it.

## Follow-up hardening audit (2026-10-01)

This pass preserves public signatures and file formats. It builds on the
uncommitted pre-push fixes: allocator-owned reader scratch, context-owned deferred
GPU buffers, correct output-binding readback, synchronized Poisson reductions,
median allocation failure handling, and CUDA-unavailable test skips.

The additional review found two reproducible UBSan failures: left-shifting
negative sparse-tree coordinates, and unaligned integer accesses in bundled
miniz. With `UBSAN_OPTIONS=halt_on_error=1`, these stopped four CPU tests. Both
are corrected. Origin alignment now uses arithmetic floor alignment, and miniz
uses `memcpy` for native unaligned loads/stores, including when callers explicitly
enable its fast path. A two-byte match-distance record now copies exactly two
bytes rather than four.

CPU sparse and coordinate queries compare complete coordinate triples after
hash matches. Previously, querying `(2097152, 0, 0)` incorrectly matched
`(0, 0, 0)`. Hash entries remain compact and duplicate lookups retain the first
index. Integer-boundary neighbors are missing rather than wrapping, and invalid
world coordinates never reach an undefined float-to-integer conversion.

Checked arithmetic protects dense constructors, median scratch, sparse capacity
and hash growth, and arena allocation. Sparse reserve allocates both replacements
before committing, preserving its state on either allocation failure. Vulkan
buffer helpers similarly clean up at every failed creation stage. Dispatch
binding kinds are validated before allocation, and linking the GPU CMake target
alone now carries its NanoVDB dependency.

### Retained median optimization

Each worker keeps its window across iterations, and one OpenMP team processes all
passes. Z/Y boundary clamps and row offsets are computed outside the innermost
window loop. Scratch-size and indexing arithmetic remain checked/wide; a failed
worker allocation prevents all writes. A sorted-window reference verifies three
passes on a non-cubic grid.

The table reports medians of three paired Release runs, reversing before/after
order in the middle pair. Both executables use the same benchmark source; the
baseline links the pre-pass libraries. Affinity is restricted to the first eight
available logical CPUs, with `OMP_PROC_BIND=true` and `OMP_PLACES=cores`.
Compiler: GCC 13.3, `-O3 -DNDEBUG`, SIMD enabled, OpenMP enabled. Host reports an
AMD Ryzen Threadripper 1950X. Times are totals for ten repetitions; `median_iter`
performs five passes per repetition. Measurements are local, not portable speed
claims.

| Dimension | Threads | Case | Before (ms) | After (ms) | Improvement |
|---|---:|---|---:|---:|---:|
| 32³ | 1 | median | 115.33 | 100.47 | 12.9% |
| 32³ | 1 | median_iter | 487.32 | 409.58 | 16.0% |
| 32³ | 8 | median | 27.17 | 23.18 | 14.7% |
| 32³ | 8 | median_iter | 110.32 | 96.58 | 12.5% |
| 64³ | 1 | median | 766.55 | 648.34 | 15.4% |
| 64³ | 1 | median_iter | 3759.32 | 3211.57 | 14.6% |
| 64³ | 8 | median | 161.11 | 150.91 | 6.3% |
| 64³ | 8 | median_iter | 802.13 | 699.47 | 12.8% |

Earlier full-harness measurements varied enough to obscure the scratch-reuse
benefit. Hoisting row work and using an isolated comparison produced the results
above. All eight retained cases meet the no-regression gate, and seven improve
by more than 10%.

Reproduce the workloads with `bench_tinyvdb --case median,median_iter --dim 32
--reps 10 --threads 1,8`, then repeat at dimension 64. Compare paired binaries
with equivalent compiler settings and CPU affinity.

### Rejected optimization and correctness costs

Fusing Poisson's residual update, preconditioning, and two reductions improved
single-thread measurements, but repeatedly regressed the 64³/eight-thread case.
A three-pair confirmation with twenty repetitions measured 92.38 ms before and
99.05 ms after (7.2% slower). The fusion was reverted. The reduction barrier and
wide stencil indices remain.

Full-coordinate equality checks add work to sparse queries. Three paired runs
of `sparse_query` at ten repetitions measured approximately 8–12% overhead across
32³/64³ and one/eight-thread harness settings. This is the cost of correcting
coordinate aliasing, not an acceleration claim. A bounded-coordinate shortcut
was tried and removed because it did not beat direct full-coordinate checks by
5%. Transactional sparse reserve also temporarily holds old and new arrays
during growth; failure leaves the old pointers, count, and capacity intact.

`zip_roundtrip` adds a repeatable API benchmark: a valid empty-root NanoVDB grid
with a 1 MiB patterned payload, ZIP encoding, memory decoding, and byte equality
verification. Ten repetitions measured roughly 30–34 ms before and after in
paired runs, with no consistent speedup claim. A separate single-core miniz
roundtrip check (100 × 1 MiB, three pairs) measured medians of 335.97 and 316.71 ms;
encoded sizes matched at 6567 bytes. The alignment fixes are retained for
correctness regardless of noisy throughput differences.

### Regression checks

New tests cover coordinate aliases and duplicates, invalid world frames,
integer-boundary morphology, checked allocation sizes, median reference results,
sparse allocation rollback, median allocation failure, and each Vulkan buffer
failure stage. Allocation tests count outstanding allocations independently of
LeakSanitizer. Deferred dispatch tests exercise multiple output bindings,
interleaved contexts, queue capacity, repeated flushes, and context teardown.
Negative coordinates on both sides of a leaf boundary round-trip explicitly.

CPU tests run with SIMD off under ASan/UBSan, and with SIMD/OpenMP enabled at one
and eight threads. Generated-shader GPU tests, the Vulkan ABI check, and the GPU
lifetime check pass; CUDA cases skip when unavailable. A fresh build with
`-DTINYVDB_GLSLANG_VALIDATOR:FILEPATH=` verifies the actual fallback without stale
generated shader includes. GPU operations skip there, while CPU tests and mocked
Vulkan failure tests run.

ASan uses `detect_leaks=0` in this ptrace-managed environment because
LeakSanitizer cannot run here. UBSan halts on the first error; the CPU suite is
clean. Leak detection on a non-ptrace host remains a separate verification step.

### Additional container review (2026-10-01)

Jagged tensors and grid batches now check offset-array sizes, cumulative
counts, channel widths, and payload sizes before allocation or copying.
Grid-batch construction rejects nonempty grids with missing coordinate or
value arrays. Jagged reductions and the batch-to-jagged bridge reject
nonmonotonic offsets. Concatenation rejects an output handle that is one of
its inputs before modifying that handle; this restriction is documented.
Regression cases were added to `test_jagged`.

Validation: all 22 CPU tests passed under ASan/UBSan (LeakSanitizer disabled
for the existing environment limitation) and in the OpenMP build with eight
threads. `git diff --check` passed. No performance claim is made for these
additional validation checks.

## Follow-up: op review, hardening and threading (2026-10-02)

A review of the volume ops against three axes -- correctness, threading, memory --
turned up more in the GPU backend than in the CPU kernels, and one CPU measurement
that turned out to be far worse than the tables above suggest.

Machine for the numbers below: AMD Threadripper 1950X, 32 threads, AVX2, 122 GB
RAM. Release build, `TINYVDB_OPENMP=ON`, `TINYVDB_SIMD=ON`. Pinned with
`taskset -c 0-7`, `OMP_PROC_BIND=true`, `OMP_PLACES=cores`, best of 5 paired runs,
`--reps 10` unless stated. Measurements are local, not portable speed claims.

### Two defects that were not hypothetical

`tvdb_gpu_fast_sweeping` allocated one descriptor set per wavefront plane from the
shared pool, and `total_planes = 8*(3N-2)`. The pool's `maxSets` is 1024, so every
grid above **43 voxels per axis** failed with `VK_ERROR_OUT_OF_POOL_MEMORY`:

| grid | planes | before | after |
|------|--------|--------|-------|
| 40^3 (the suite's largest case) | 944 | OK | OK |
| 44^3 | 1040 | `VK_ERROR_OUT_OF_POOL_MEMORY` | OK |
| 48^3 | 1136 | `VK_ERROR_OUT_OF_POOL_MEMORY` | OK |
| 64^3 | 1520 | `VK_ERROR_OUT_OF_POOL_MEMORY` | OK |
| 80^3 | 1904 | `VK_ERROR_OUT_OF_POOL_MEMORY` | OK |

The suite's largest case was 40^3 = 944 planes, 92% of the limit, which is why
this survived. The chain is now **one** descriptor set with a dynamic uniform
offset selecting the plane's 256-byte slice, so there is no ceiling and no
per-plane `vkAllocateDescriptorSets`/`UpdateDescriptorSets` pair. A new
`pool-ceiling-48` / `pool-ceiling-64` pair in `test_gpu_fast_sweeping` compares
against the serial CPU reference; reinstating a pool-sized cap fails them.

Two things had to be true for that to work, and both were found the hard way on
the device: the set must be allocated from *the same* `VkDescriptorSetLayout`
handle the pipeline layout was built from (an "identically defined" layout is legal
but faults on at least one driver, hence `tvdb_vk_get_pipeline`), and
`dynamicOffsetCount` must equal the number of dynamic bindings even when the offset
is 0, which is plane 0.

`tvdb_gpu_solve_poisson_d_ex` and `_dd_ex` never worked on CUDA. They requested a
kernel symbol `tvdb_cuda_stencil_d`, which is the name of a *host wrapper* in
`tinyvdb_gpu.c`, not a kernel; the real kernel is `tvdb_cuda_stencil_scalar_d`. Every
fp64 Poisson solve on CUDA returned `CUDA_ERROR_NOT_FOUND` at module load. The fp32
spelling was already correct, which is why only the `_d` and `_dd` paths were
broken and only `test_gpu_poisson_cuda` noticed.

### CPU fixes with tests

`test_hardening` gained `test_measure_and_guards`, `test_nonfinite_vectors` and
`test_sweeping_no_seed`. Each was checked to fail against the code it covers:
`tvdb_volume_d(NULL)` and `tvdb_surface_area_d(NULL)` segfaulted (the fp32 twins
return 0); `tvdb_prune_grid` with a negative extent was an ASan heap-buffer-overflow
in both directions; `tvdb_ijk_to_world` dereferenced all five of its pointer
arguments unconditionally.

`tvdb_surface_area` counted exact-zero voxels as inside (`<= 0`) while `tvdb_volume`
and both fp64 twins used `< 0`, so one grid got two different answers. All four and
both measure shaders now agree on `< 0`. `measure.comp` changed with it, so CPU/GPU
parity holds.

`tvdb_normalize_vec` turned a NaN component into a zero -- indistinguishable from a
genuine zero vector -- and `sqrtf(x*x+y*y+z*z)` overflowed to `+inf` above ~1.8e19,
silently zeroing a large but finite vector. Both are scaled now.

`tvdb_fast_sweeping` copied its 1e30 "unreached" sentinel into the caller's grid
when nothing was frozen (band=0, or a field with no voxel inside the band) and
reported success. The GPU path had the same bug; `test_gpu_fast_sweeping`'s
`band-zero-unsolved` case is what pinned it, and the CPU/GPU disagreement is why
that test started failing once the CPU side was fixed.

### Threading: three files had no pragmas at all

`tinyvdb_topology.c`, `tinyvdb_grid_index.c` and `tinyvdb_jagged.c` contained zero
`omp` directives while `tinyvdb_ops.c` had 20 and `tinyvdb_poisson.c` 17. Every
loop in them is independent -- each output element a pure function of its own input
window, against a hash that is read-only once built -- so they all take
`collapse(2) schedule(static)` now. `tvdb_merge_grids` is the deliberate exception:
its splat is a read-modify-write min from two grids onto the same output voxel, so
only the background fill is parallel. `tvdb_jagged_reduce` also had the channel loop
outside the element loop, so every step advanced `c` floats and touched a new cache
line; channel is now innermost, which leaves the per-channel summation order
untouched and so keeps the result bit-identical.

`tests/test_threads.c` is new and is the reason any of this is pinned. It runs
every parallel op at one thread and again at the widest team and requires
bit-identical results via `memcmp`. Nothing in the suite asserted this before: no
test called `omp_set_num_threads` and no ctest set `OMP_NUM_THREADS`, so each test
ran once at whatever the host defaulted to. It was validated by making
`tvdb_prune_grid` accumulate racy into a `static`, which it reports as
`prune_grid differs at element 175/12312`. Its leak checking also found two real
leaks, both since fixed: the marching-cubes edge cache was never released
(`edge_cache_free` added), and `tvdb_mesh_to_sdf` never freed its per-face normal
table.

### Measured: CPU

`tree_dilate` (icosahedron, 364k active voxels, 8 threads, medians of five):

| phase | ms | note |
|-------|----|------|
| baseline | 2075 | |
| leaf hash hoisted out of `dilate_step`, set-bit mask iteration | 2044 | the O(count x leaves) repack scan is gone |
| + first-occurrence bitmap from `tvdb_hash_build` | **1932** | removes a hash probe per input voxel |

The leaf hash was rebuilt identically on every iteration inside `dilate_step` and
then discarded, and the per-output-voxel repack used a linear scan over leaves to
find a leaf that hash already indexed. Both now go through one table built once.

`mesh_to_sdf` is the slowest op in the library by more than an order of magnitude,
and the tables above do not show it because the harness times the whole
sphere -> mesh -> sphere round trip. Measured directly (98,684 faces from a 128^3
sphere, output 109^3):

| threads | before | after | |
|---------|--------|-------|---|
| 1 | 19.50 s | **16.72 s** | -14% |
| 8 | 4.42 s | **3.39 s** | -23% |

Three changes, all bit-exact against the original (verified by dumping the rebuilt
grid and diffing): a per-triangle AABB reject before the closest-point case
analysis; the two per-face bound arrays interleaved into one, so a face's box is 24
contiguous bytes instead of two cache lines; and coherent query seeding -- `x` is
the inner loop, so consecutive voxels are one voxel apart and share a nearest
triangle, and seeding each search with the previous voxel's winner starts the
traversal with a nearly tight bound.

That last one is worth recording as a trap. The first version seeded `best_dsq`
straight from the previous voxel and measured 6.3x, but that number was wrong: the
seed's distance belongs to the *neighbouring* voxel, and reusing it as this voxel's
bound over-prunes. The symptom was visible only because `test_levelset` failed --
and when it did, dumping the grid and diffing against the original located it in
one step. The seed has to be re-measured at the current position, which is what
makes it exact, and that version is 14% rather than 6.3x.

Poisson CG (128^3, 200 fixed iterations, so no tolerance early-exit):

| precision | 1 thread | 8 threads |
|-----------|----------|-----------|
| fp32 | 8829 -> **7091** ms | 2560 -> **1613** ms |
| fp64 internal | 8617 -> **7529** ms | 4519 -> **4125** ms |
| fp64 storage | 8612 -> **7437** ms | 4564 -> **4160** ms |

The candidate residual stencil ran every iteration, a second full 7-point
application whose only jobs are to report `final_residual_norm` and pick the
returned iterate. Neither the convergence test (a cheap residual dot) nor the
restart test reads it, so it now runs every eighth iteration plus on the last one
and on convergence. The serial per-voxel conversion loop with its early-exit
`isfinite` became one parallel pass with a reduction flag. fp64 scales much worse
(1.8x rather than 4.4x) because 128^3 doubles is a 117 MB working set against a
~32 MB L3 -- memory-bound, not thread-bound.

Separable filters at 128^3, 8 threads: gaussian 59 -> **41 ms** (-31%),
bit-identical across 6 grid shapes x 4 widths x both filters. The tap loop rebuilt a
full 3-D index (three multiplies and a branch on which axis it was) for each of the
`2r+1` taps; the filtered axis is fixed for the whole pass, so the index is a
constant base plus `c*stride`. The first attempt at this double-counted `iy` on the
y axis and ASan caught it immediately -- which is the argument for keeping the
scalar/sanitizer configuration in the matrix.

### Measured: GPU

Reductions that ran on a single workgroup (RTX 5060 Ti, Vulkan):

| grid | op | before | after |
|------|----|--------|-------|
| 128^3 | grid_statistics | 19.16 ms | **11.06 ms** |
| 128^3 | grid_checksum | 18.76 ms | **10.79 ms** |
| 256^3 | grid_statistics | 116.81 ms | **61.16 ms** |
| 256^3 | grid_checksum | 117.78 ms | **62.34 ms** |

`stats`, `checksum` and `levelset_check` used `nthreads = min(count,256)` and
dispatched `(nthreads+255)/256`, i.e. **one** 256-thread workgroup scanning the
entire grid. They now fold a grid-stride slice in shared memory per workgroup and
let the host fold `ngroups <= min(ceil(count/256), 1024)` partials, which is the
shape `measure.comp` already used. min and max needed their own reduction
operators and an opposite-infinity start for threads with an empty slice -- the
first attempt copied `measure.comp`'s plain `+=`, which sums a min. `levelset_check`
had the same empty-slice problem on `max_grad_error`. Checksum values are
unchanged (0xd2d61700 at 128^3, 0x46df5c00 at 256^3), as are min, max and count;
the reductions' summation order does change, which is why `sum`/`stddev` are
compared with a tolerance rather than bit-exactly elsewhere in the suite.

Also: `tvdb_gpu_open`/`tvdb_gpu_close` close the last CPU morphology coverage gap;
`sparse_conv3d`'s scatter-then-convolve chain now defers its first dispatch instead
of taking two blocking fences; the CUDA dense morphology loop dropped a
`cuCtxSynchronize` per iteration, which the NULL stream's ordering already made
unnecessary.

### A rejected optimization, recorded so it is not retried

Carrying each leaf's bounds inline in the dilate output hash (using the padding in
the 16-byte entry) to avoid a second random read of `out->coords` per probe. It
measured 2075 -> 2044 ms, inside the noise, and a first version of it that also
computed the input lookup unconditionally came out 5% *slower*. The inline-coordinate
variant was then removed rather than kept on a 2% claim.

Rewriting `tvdb_dilate_sparse_step` around probe/append macros was reverted: it
emitted 85 voxels where the original emits 81 and an independent reference agrees
is 81, and the extra four were duplicate appends the original structure cannot
produce. Only the first-occurrence bitmap, which is a self-contained change to a
loop condition, was kept.

### Validation

Four configurations, per the procedure in `AGENTS.md`:

| configuration | result |
|---------------|--------|
| scalar, SIMD off, OpenMP off, ASan+UBSan | 24/24 CPU tests |
| SIMD + OpenMP, `OMP_NUM_THREADS=1` | 24/24 |
| SIMD + OpenMP, `OMP_NUM_THREADS=8` | 24/24 |
| GPU, generated SPIR-V, Vulkan + CUDA on an RTX 5060 Ti | 48/48 |
| GPU, `TINYVDB_GLSLANG_VALIDATOR:FILEPATH=` (no shaders) | 48/48, GPU tests skipped |

All 48 GPU tests ran on real hardware here, so the device-coverage gap that
`AGENTS.md` warns about did not apply to this phase: `test_gpu_backend`,
`test_gpu_fast_sweeping`, `test_gpu_lifetime` (400 iterations, both backends),
`test_gpu_measure`, `test_gpu_index_map`, `test_gpu_fp64` and the CUDA variants all
executed rather than returning 77. The fallback configuration is the one that
skips. No NVRTC-only or mock-driver result is reported as a device result.

### Two GPU optimizations measured and reverted

Both were written, measured, and removed. They are recorded here because the
diagnosis they produced is worth keeping and the change is not worth shipping.

`tvdb_gpu_fast_sweeping` launched one thread per voxel of the **grid** for each of
the `8*(3N-2)` wavefront planes, and the shader returned immediately unless the
thread's level matched the plane. Replacing that with a direct enumeration of the
plane -- solve for one axis, enumerate the other two, solve for the largest extent
so the enumeration is the two smallest -- cut launched threads by a factor of N
(24.6M -> 0.77M per plane-sweep at 32^3, 6.4G -> 50M at 128^3) and changed the
wall time by **nothing**: 494.9 vs 501.1 ms at 32^3, 2055.6 vs 2069.6 ms at 128^3.

That null result is the useful part. Per-dispatch cost was flat at **336 us from
32^3 to 128^3** -- identical to within 3% across a 16x range in voxel count and an
8x range in threads per dispatch:

| grid | dispatches/solve | ms/solve | us/dispatch |
|------|------------------|----------|-------------|
| 32^3 | 1504 | 494.9 | 329.1 |
| 64^3 | 3040 | 1029.0 | 338.5 |
| 96^3 | 4576 | 1541.6 | 336.9 |
| 128^3 | 6112 | 2055.6 | 336.3 |

Runtime is a pure function of dispatch count, so the op is bound by per-dispatch
submission latency and has nothing to do with thread count or bandwidth. Two
consequences:

1. The obvious next fix is bandwidth, since `phi` and `frozen` are HOST_VISIBLE and
   a plane kernel reads a slab of them. Staging both into DEVICE_LOCAL memory for
   the solve -- the recipe `tvdb_mcf_vk` already uses, same threshold, same
   one-stage-in/one-stage-out shape -- also changed nothing. Interleaved A/B over
   five rounds at 128^3: host-visible median 3534.6 ms, device-local median
   3548.4 ms. The slab a plane touches is O(N^2) of an O(N^3) grid, so the traffic
   is ~200 KB per plane, and ~1.2 GB per solve at 128^3 is not the constraint.
2. The actual fix is to record all planes of an iteration into **one** command
   buffer and submit once, turning 6112 submissions into 2. That is a change to
   the dispatch plumbing, not to this op, and it is left as the actionable item.

### A caveat on GPU numbers from this host

This machine is shared, and during the measurements above `nvidia-smi` reported
**100% GPU utilization from another tenant** (5372 MiB resident). Absolute GPU
timings are therefore not comparable across a session: the same fast-sweeping
config measured 2056 ms early in the session and 3535 ms later, with no code
change. Every GPU comparison in this document that carries a claim was
re-measured back to back or interleaved with its own baseline for that reason --
the two-stage reduction A/B and the device-local A/B above are both interleaved --
but the absolute milliseconds should be read as "this host, under this load".
CPU numbers are unaffected.

### Advection: parallelized, and bit-identical

`tvdb_advect_sl`, the gather behind all six `tvdb_advect` schemes, had no pragma at
all, so the higher-order schemes did not scale: MacCormack measured 1093 ms at one
thread and 1303 ms at eight, i.e. slower with more threads. The gather is a pure
read-only sample from `field` and `velocity` into a distinct `result` (both public
entry points route an overlapping call through scratch first), so it takes
`collapse(2)` like every other stencil here. The two error-compensated schemes also
each redid a full RK2 backtrace per voxel in the clamp step -- 2 vector trilinear
samples, 48 taps -- for a trace the first pass had already computed. `tvdb_advect_sl`
now optionally emits the field's trilinear-stencil min/max at the backtrace point
(2 floats per voxel, only when clamping is requested), and both clamp loops become
elementwise.

128^3, digests over the whole output grid in brackets, `clamp=1`:

| scheme | 1 thread | 8 threads | speedup at 8t | digest |
|--------|----------|-----------|---------------|--------|
| RK1 | 205 -> 183 ms | 180 -> **25.5 ms** | 7.1x | 2cf20299 |
| RK2 | 425 -> 339 ms | 337 -> **60.4 ms** | 5.6x | 9216f591 |
| RK3 | 669 -> 635 ms | 604 -> **88.8 ms** | 6.8x | bcf52c53 |
| RK4 | 711 -> 688 ms | 779 -> **102.3 ms** | 7.6x | 0bcca764 |
| MacCormack | 1093 -> 821 ms | 1303 -> **138.6 ms** | 9.4x | 813ace85 |
| BFECC | 1414 -> 1166 ms | 1537 -> **200.9 ms** | 7.6x | 3537600b |

Every digest is unchanged, at one thread and at eight, with `clamp` on and off
(0d440469 and 266bf886 for the two clamped schemes). That is checked rather than
asserted: the probe digests the whole output grid, and the digests from the
unmodified code match.

The single-thread gain (MacCormack 1093 -> 821 ms) is the backtrace fusion alone;
the parallel gain is on top. The trade is memory: 2*N floats of clamp bounds when
`clamp` is set, against the 2 grids the scheme already allocates, so the scratch
for those two schemes goes from 8N to 16N bytes. That is the right side of the
trade for a 9x speedup, and it is skipped entirely when `clamp` is 0.

### The SIMD dot product was accumulating in fp32, and its test could not tell

`tvdb_simd_dot_f32` is the only dot product the SIMD header offers, and it is
currently called from nothing -- so the Poisson solver below still uses the
scalar `poisson_dot_f`. That turned out to be the right call, but not for the
reason I first assumed.

The AVX2 path accumulated into a `__m256` **float** accumulator, then widened the
partial sum to `double` at the end. The scalar path accumulates in `double` on
every term. The comment above it claimed numerical stability "comparable to the
scalar path"; that was false, and the error is not a small constant factor -- it
grows linearly in `n`, because an fp32 accumulator's rounding error accumulates
once per add.

The visible symptom needs the right input shape. A same-sign dot product hides
the bug: every term is positive, so fp32 rounding stays relative to the running
total, and the relative error stays near 1e-7 at any `n`. A conjugate-gradient
`rz = dot(r,z)` has the opposite shape -- the terms cancel, leaving a result far
smaller than the terms -- and that is exactly the case where an fp32 accumulator
falls apart:

| n | exact | old AVX2 | rel err |
|---|-------|----------|---------|
| 2^20 | -1.048576e+14 | -1.047531e+14 | 9.97e-04 |
| 2^21 | -2.097152e+14 | -2.099274e+14 | **1.01e-03** |
| 2^22 | -4.194304e+14 | -4.210336e+14 | **3.82e-03** |
| 2^23 | -8.388608e+14 | -8.432461e+14 | **5.23e-03** |

`2^21` is 128^3, the grid size in the Poisson benchmark above. So the threshold
where this stops being a rounding curiosity and becomes a wrong `alpha` is
squarely inside this library's own working set, and `alpha` feeds straight into
the `pap > 0` breakdown test. The accumulator now widens to four `__m256d` lanes
(FMA when available), which is `double` accumulation in the same spirit as the
scalar path; the same four cases now agree to 0.0e+00, and the same-sign cases to
~1e-12 (double-accumulation ordering, as expected).

`tests/test_simd.c` did not catch this and still would not have: it builds 10000
same-sign elements and asserts `diff < 1e-3`, which is four orders of magnitude
looser than the observed error. It now also checks 2^18/2^21/2^23 sign-cancelling
vectors at 1e-9.

The reason this is written up as a *not-wired-up* finding: `alpha` and `beta` in
this solver are `double`, and the scalar CG update is
`x[i] = (float)((double)x[i] + alpha*p[i])` -- computed in double, rounded once.
`tvdb_simd_axpy_f32` takes a `float` alpha and rounds per-element, and its FMA
path rounds differently again. Wiring either primitive into the CG update would
have changed the iterate, and with it the iteration count and the selected
iterate, for a vector op that is already memory-bound. The dot product could
have been used for the *dot* half; the axpy could not. Doing half of a
floating-point contraction is a reasonable way to make a solver's output depend
on which build flags it was compiled with, so neither was used.

### Poisson preconditioner: measured, not worth the rounding

`poisson_precondition_f` divides by a per-voxel `degree` (the count of in-range
6-neighbours, 0..6) on every call, and it is called once per restart, not once per
iteration -- so it is a small share of the solve. The obvious fix is to
precompute `h*h/degree` once. It is not worth doing: `degree` is a small integer,
so the only exact form is still a division by a variable, and every faster
alternative (a reciprocal table, a multiply) changes the rounding of `z`, which
changes the iterate and therefore the answer. The estimate is ~1% of the fp32
128^3/200-iteration runtime, which does not justify making Poisson's output
flag-dependent. Left alone deliberately.

### Two sparse-tree consistency fixes

`collect_mutable_leaves`'s word-wise `child_mask` scan is documented in the
sparse-tree backlog; that one is already in. The remaining one was the level
lookup in `visit_subtree`: an internal node's own level was recovered by scanning
`layout.levels[]` for a matching `log2dim`, for every internal node visited. The
node already carries `node->level`, so this is now a direct read, validated
against the layout and falling back to the scan if the two disagree, which keeps
the scan as the definition of "matching" rather than assuming the invariant. I
verified the fast path is actually taken rather than silently falling back: an
instrumented build over the fast-sweeping and thread-invariance suites reported
zero fallbacks.

`pow2_` in the same file was `while (p < v) p <<= 1`, which overflows to 0 once
`v > SIZE_MAX/2` and then spins forever, because `0 < v` never becomes false. All
four call sites feed it `count * 2 + 16` from a sparse structure that does not
bound `count`, so nothing upstream prevents that. It now delegates to the
already-checked `tvdb_hash_capacity` (same smallest-power-of-two >= count*2+16,
verified identical for small counts) and the three call sites that can receive 0
check the capacity explicitly rather than relying on `calloc` returning NULL --
`calloc(0, ..)` is permitted to return a non-null pointer, which would have left
the mask at `SIZE_MAX`. This one is hardening for consistency with the
`tvdb_index_map_build` fix above, not a reachable hang: reaching it needs a
sparse grid of ~2^63 voxels, and at that size the `count * 2` multiply overflows
first and produces a *too-small* table instead of a hang.

### Resident volume processing and compact GPU marching cubes (2026-10-02)

The new `tinyvdb_gpu_resident.h` API supports persistent dense and sparse buffers,
transactional processing, and dependent dispatch batches. Host entrypoints for
composition, CSG, filters, stencils, advection, morphology, resampling,
statistics/validation/checksum, measurement, active-coordinate extraction,
sparse convolution, and fp64-capable Poisson now use that implementation.
Sparse maps are built on the device and shared when topology is unchanged;
value-only uploads retain the map. Transpose retains a host API fallback for
its existing clipped-coordinate boundary behavior. Resident Poisson stores all
vectors on the device and reads reduced scalars; its three arithmetic/storage
modes preserve the solver contract rather than identical CPU iteration counts.

Marching cubes now classifies into one uint32 count per cell, scans those counts
on the device, reads one uint32 total, and allocates the exact output. It emits
in CPU cell/table order. The fixed 180-byte-per-cell vertex temporary and CPU
compaction pass are removed. This is a newly tested implementation: no input or
regression record was available for the previously reverted attempt.

`test_gpu_marching_cubes` generates all 256 cell cases plus constant, plane,
sphere, checkerboard, and deterministic noisy fields. It compares ordered
triangle positions to CPU output, checks the four-byte pre-output readback,
and bounds peak logical allocations to exclude the old temporary. The 205³
case exceeds 65,535 workgroups in both classification and scan. Linear resident
kernels flatten a second dispatch axis to stay within Vulkan's guaranteed
workgroup-count limit, with guards for padded reduction workgroups.

The optional `bench_gpu_resident` target generates its own sphere and a chain
of five composition-plus-mean-filter steps. Example build/run:

```sh
cmake -S . -B /tmp/tinyvdb-resident-bench -G Ninja \
  -DCMAKE_BUILD_TYPE=Release -DTINYVDB_BUILD_BENCH=ON \
  -DTINYVDB_BUILD_GPU=ON -DTINYVDB_BUILD_EXAMPLES=OFF \
  -DTINYVDB_BUILD_VDBRENDER=OFF
cmake --build /tmp/tinyvdb-resident-bench --target bench_gpu_resident
/tmp/tinyvdb-resident-bench/bench_gpu_resident cuda 128
/tmp/tinyvdb-resident-bench/bench_gpu_resident vulkan 128
/tmp/tinyvdb-resident-bench/bench_gpu_resident cuda 256
```

Observed on NVIDIA GeForce RTX 5060 Ti, NVIDIA driver 615.71.09. Each timing below
is a single warmed run, not a cross-device performance guarantee. The host
column uses the migrated compatibility APIs and includes their transfers and
allocations; it is not a timing of the previous implementation.

| Backend / grid | Triangles | Compact mesh, ms | Resident chain, ms | Host chain, ms |
|---|---:|---:|---:|---:|
| CUDA / 128³ | 55,532 | 0.563 | 6.033 | 61.423 |
| Vulkan / 128³ | 55,532 | 7.154 | 25.235 | 1,011.787 |
| CUDA / 256³ | 222,524 | 2.423 | 22.015 | 739.304 |

| Grid | Previous fixed vertex temporary, bytes | New peak logical resident buffers, bytes (CUDA) |
|---|---:|---:|
| 128³ | 368,708,940 | 18,598,748 |
| 256³ | 2,984,647,500 | 141,462,684 |

The previous column is the analytical `180 * cell_count` allocation, not an
instrumented old-process peak. The new peak includes the input grid, offsets,
tables, compact output, and resident temporary buffers. It excludes allocator
padding, driver caches, and nonresident staging. Thus the two columns are
explicitly different quantities; they establish that the large fixed temporary
has disappeared, not a total-process VRAM ratio.

Each resident chain has zero grid readback and ten compute submissions. The
128³ host chain uploads 125,829,120 grid bytes and downloads 83,886,080; at 256³
those numbers are 1,006,632,960 and 671,088,640. Small coefficients/uniforms are
additional: the CUDA resident chain records 860 uploaded bytes and Vulkan 60,
because Vulkan's mapped uniform buffers are outside the resident counters.
Both chains return matching values in the benchmark.

The I/O fix routes owned-grid destruction through complete descriptor,
metadata, tree, and point-payload cleanup. Metadata parsing now cleans partial
entries on truncation and allocation failure. Before the fix the scalar-writer
Valgrind run reported 5,656 lost bytes; the repaired run reported zero live
allocations and zero errors. `test_io_ownership` also injects each metadata
allocation failure, truncates at every byte, and checks repeated destruction.

Validation for this change:

- Scalar ASan/UBSan/float-cast-overflow: 25/25, including leak detection. The
  initial sandbox run failed because LeakSanitizer cannot operate under ptrace;
  the full suite passed outside that sandbox with sanitizers enabled.
- SIMD/OpenMP: 25/25 with one thread and 25/25 with eight; configuration logs
  confirmed both optimized paths.
- Generated shaders: final full suite 61/61 on hardware Vulkan and CUDA,
  including registered CUDA filter/advection/composition/measurement variants.
  Vulkan device zero was confirmed as the RTX 5060 Ti. An explicitly selected llvmpipe ICD also
  passed all four resident/compaction cases in the restricted environment.
- Fresh no-generated-shader build: 28 passed and 33 backend skips in the
  restricted environment. A hardware CUDA/failure/fallback-consistency run
  passed 17/17 using that same build; CUDA does not depend on generated SPIR-V.
- Rebuilt Python extensions: 110 passed, one existing disabled NanoVDB
  roundtrip test skipped.
- Failure-injected CUDA dispatch verifies scratch-output preservation and waits
  before freeing in-flight resources. Pipeline-cache exhaustion, Vulkan ABI,
  shader fallback consistency, and whitespace checks passed.

Resident Poisson requires fp64 reductions even for rounded float
arithmetic. Its initial implementation used nine double workspace arrays; the
storage and submission optimization below replaces that layout. Resident point voxelization
currently accepts isotropic spacing. These are explicit API limits; the new
functions do not silently materialize a grid on the CPU to work around them.

### Poisson workspace and submission optimization (2026-10-02)

The resident solver now stores its six PCG vectors in their arithmetic
precision, its two candidate/best vectors in the returned precision, and its
true residual in double precision. The resulting workspace costs 40/64/72
bytes per voxel for float/mixed/double modes, compared with 72 for every mode
before this change. Reductions remain doubles. Vulkan binds two typed views
of the same allocation; CUDA uses equivalent aligned float/double views.
Checked word-address bounds reject overflow before allocation.
The shared binding follows Vulkan's [descriptor aliasing rules](https://docs.vulkan.org/spec/latest/chapters/interfaces.html#interfaces-resources).

Dependent stencil, vector, and reduction kernels are recorded with copied
uniforms and submitted together at scalar readback boundaries. Output commit
also flushes the batch before swapping the transactional scratch buffer into
the output handle. This retains the same host convergence decisions and
32-byte scalar readbacks while eliminating most per-kernel submissions.

`bench_gpu_poisson` generates a Neumann-compatible RHS from a procedural field,
warms the solver, and measures a second solve. It independently recomputes the
returned residual, reports logical resident-buffer peak and transfer counts,
and hashes the output. Build with the benchmark configuration above:

```sh
cmake --build /tmp/tinyvdb-resident-bench --target bench_gpu_poisson
/tmp/tinyvdb-resident-bench/bench_gpu_poisson cuda 64 0 32
/tmp/tinyvdb-resident-bench/bench_gpu_poisson vulkan 64 0 32
# Third argument: 0 float, 1 mixed, 2 double. Fourth: iteration budget.
```

Paired before/after runs on the same RTX 5060 Ti and driver 615.71.09 used a
64³ grid and 32 iterations. Timings are medians of three warmed measurements
per version; runs were sequential. The before binary contains the immediately
preceding resident implementation, including its nine-double-array workspace.

| Backend / mode | Before, ms | After, ms | Before logical peak, bytes | After logical peak, bytes |
|---|---:|---:|---:|---:|
| CUDA / float | 34.419 | 35.370 | 22,151,248 | 13,762,960 |
| CUDA / mixed | 34.310 | 34.063 | 22,151,248 | 20,054,416 |
| CUDA / double | 34.459 | 31.061 | 25,296,976 | 25,297,296 |
| Vulkan / float | 1,357.784 | 741.761 | 22,151,168 | 13,762,560 |
| Vulkan / mixed | 1,342.798 | 754.210 | 22,151,168 | 20,054,016 |
| Vulkan / double | 1,389.331 | 756.976 | 25,296,896 | 25,296,896 |

All six cases reduced compute submissions from 1,017 to 236. Scalar readback
remained 7,520 bytes; no volume vectors were downloaded during the solve.
Float and mixed outputs were byte-identical before/after on both backends.
The double-mode CUDA comparison had a maximum absolute voxel difference of
2.89e-15 and RMS difference of 2.03e-16; double-mode Vulkan hashes matched.
Independent residual checks passed for every run.

These peaks include resident inputs, retained output scratch, solver workspace,
partial reductions, and CUDA device uniforms. Vulkan mapped uniforms, staging,
driver caches, and allocation padding are outside these counters. Double CUDA
peak rises by 320 bytes because uniforms for several kernels coexist in a
batch. CUDA float/mixed timings are effectively unchanged at this size; the
memory reduction and Vulkan submission savings are the observed benefits.

Regression coverage bounds logical workspace and submission counts in every
precision mode, exercises odd vector lengths and partially occupied reduction
groups, and checks aliased RHS/output, Neumann means, nonfinite RHS rejection,
finite budgets, and independently computed residuals. Injected CUDA allocation
and batched-launch failures check output preservation, cleanup, and waiting
before freeing resources; separate cases reject workspace-index overflow.

Validation after this optimization:

- Generated shaders: 61/61 passed on hardware Vulkan and CUDA (RTX 5060 Ti,
  driver 615.71.09), including Vulkan ABI and fallback-source consistency.
- Scalar ASan/UBSan/float-cast-overflow: 25/25 with leak detection enabled.
  The new injected GPU failure cases also passed under those sanitizers.
- SIMD/OpenMP: 25/25 with one thread and 25/25 with eight.
- Fresh explicitly empty-validator fallback: 44 passed, 17 Vulkan shader tests
  skipped; CUDA device arithmetic and resident Poisson tests executed.
- Software Vulkan: the complete resident Poisson contract suite passed with
  the explicitly selected llvmpipe ICD.
- Whitespace and documentation command/link review passed. Windows was not
  exercised; no standalone `spirv-val` executable was available.

## Hierarchical SDF workspaces and task backends (2026-10-02)

Added `tinyvdb_sdf_tree.h`: tree-native in-place fast sweeping, separable mean
and Gaussian filtering, six-neighbor diffusion, seven-point min/max morphology,
and world-distance offsets. The workspace indexes existing leaves and keeps
values packed by active-mask rank; it allocates neither a dense bounding box nor
flat coordinate arrays. Filtering uses signed tiles and stored inactive leaf
values as fixed boundaries. Sweeping solves only the active leaf domain, preserves
frozen seeds and signs, and reports disconnected unseeded components without
replacing their values. Numeric/allocation failures preserve the input.

Fast sweeping uses eight directional block Gauss-Seidel sweeps. Leaf planes are
sorted in four orders (with reverse traversal for opposite directions). Only
occupied planes are stored, so distant islands do not add empty wavefront steps.
Face-neighboring leaves always occupy different planes; synchronization between
planes makes concurrent writes independent. Packed flags are initialized in
complete bytes before parallel sweeps, avoiding races where leaf ranges share a
flag byte. Double arithmetic in the Eikonal update avoids cancellation in the
quadratic discriminants; retained distances are floats.

The synchronous task module defaults to C11 when available and GCD on Apple.
Explicit C11, GCD, pthread and serial configurations are supported. C11/pthread
pools retain workers between calls, participate on the calling thread, serialize
concurrent submissions and handle same-pool nested calls serially. Partial worker
creation failures join created workers and release resources. The SDF-owned
pool caps automatic teams at eight workers and the number of leaves; a borrowed
pool permits larger teams. This cap avoids excessive barriers on short sparse
wavefronts: on this host, an explicit 32-worker pool took 29.20 ms to sweep the
64-cube narrow band, versus 9.57 ms with eight and 17.65 ms with one. Larger teams
can help filters: the full 64-cube Gaussian workload took 6.24 ms with 32 workers
versus 10.24 ms with eight. These measurements inform the default, rather than
assuming every workload scales with the hardware's logical CPU count.

Reproduce with a fresh build:

```sh
cmake -S . -B /tmp/tinyvdb-sdf-bench -G Ninja \
  -DCMAKE_BUILD_TYPE=Release -DTINYVDB_BUILD_BENCH=ON \
  -DTINYVDB_BUILD_EXAMPLES=OFF -DTINYVDB_BUILD_VDBRENDER=OFF \
  -DTINYVDB_BUILD_GPU=OFF -DTINYVDB_OPENMP=OFF \
  -DTINYVDB_THREAD_BACKEND=C11
cmake --build /tmp/tinyvdb-sdf-bench --target bench_sdf_tree
/tmp/tinyvdb-sdf-bench/bench_sdf_tree 64
/tmp/tinyvdb-sdf-bench/bench_sdf_tree 128
# Optional second argument: worker count; zero selects the SDF-owned default.
/tmp/tinyvdb-sdf-bench/bench_sdf_tree 64 0
```

Inputs are procedural spheres (radius `0.28 * N`, unit spacing) with exact seeds
within distance 1.5. The full domain activates all voxels; the narrow domain
activates only `abs(phi) <= 4`. Far active values start at signed 100; inactive leaf values and constant tiles
represent the signed interior/exterior. Timing is
the fastest of three warmed repetitions after an untimed first run, restoring
leaf values before each solve/filter. Each sweep converged in two iterations at
absolute change tolerance `1e-5`; Gaussian timing includes four iterations,
three axis passes per iteration. The workspace is reused between operations.
Measurements: AMD Ryzen Threadripper 1950X, 16 cores/32 logical CPUs, GCC 13.3
Release, C11 tasks, OpenMP disabled. Times are local observations, not universal
speedup guarantees.

| Domain | Active voxels | Leaves | Sweep, 1 worker (ms) | Sweep, 8 workers (ms) | Gaussian ×4, 1 worker (ms) | Gaussian ×4, 8 workers (ms) |
|---|---:|---:|---:|---:|---:|---:|
| 64³ full | 262,144 | 512 | 169.71 | 42.40 | 36.10 | 9.71 |
| 64³ narrow | 32,680 | 152 | 17.51 | 9.97 | 4.67 | 1.99 |
| 128³ full | 2,097,152 | 4,096 | 1,388.95 | 237.05 | 289.70 | 61.07 |
| 128³ narrow | 130,240 | 560 | 68.12 | 22.31 | 19.10 | 5.57 |

The full 128³ case improves by 5.86× for sweeping and 4.74× for filtering from
one to eight workers. The narrow case improves by 3.05× and 3.43× respectively.

| Domain | Sweep-only scratch (bytes) | Retained metadata after sweep (bytes) | Scratch after filtering too (bytes) | Existing dense sweep scratch for the enclosing box (bytes) |
|---|---:|---:|---:|---:|
| 64³ full | 1,114,112 | 102,776 | 2,162,688 | 1,572,864 |
| 64³ narrow | 138,890 | 30,776 | 269,610 | 1,572,864 |
| 128³ full | 8,912,896 | 819,576 | 17,301,504 | 12,582,912 |
| 128³ narrow | 553,520 | 112,376 | 1,074,480 | 12,582,912 |

Sweep-only scratch is `4 * active + ceil(active / 4)` bytes, including both flag
bits; filters retain another `4 * active` bytes. Metadata includes copied masks,
rank tables, cached face neighbors and sweep orders. The dense comparison is its
existing six bytes per bounding-box voxel; its domain differs from the narrow
active domain, so this is a storage comparison rather than an arithmetic speed
comparison. Counters exclude grid storage, pools/OS thread resources and temporary
constructor/sort allocations. Four isolated active voxels with origins separated
by one billion coordinates remain below 10 KB peak workspace allocation in the
allocation-tracking regression.

Validation covers all six supported node dimensions (1, 2, 4, 8, 16, 32),
int32 boundary origins, root/internal signed tiles, inactive/nonfinite boundaries,
empty grids, malformed hierarchies, isotropic spacing, numeric overflow, every
constructor/lazy-buffer allocation failure, retry after failure and partial worker
creation failure. Procedural plane/sphere sweeps agree with analytic expectations
and the existing dense CPU implementation within `1e-4`; one/eight-worker results
are bit-identical. Filters match an independent stencil reference. The existing
sphere VDB also exercises an owned default pool.

Scalar C11 ASan/LeakSanitizer/UBSan/float-cast checks: 28/28 passed, with UBSan set
to halt on error. SIMD/OpenMP builds: 28/28 passed at one and eight OpenMP threads.
Explicit pthread and serial builds: 27/27 passed each. Pthread ThreadSanitizer:
both task and SDF suites passed. Clang 21 ThreadSanitizer crashes in this host's
C11 thread entry even in an independent standalone `thrd_create` reproducer;
this does not establish C11 race coverage. Native macOS/iOS execution is unavailable
locally; CI now registers GCD and pthread SDF tests on macOS. Rebuilt Python
bindings: 110 passed, one existing skip. Generated GPU and fallback builds are
also validated, with backend results recorded below.

The empty-grid regression additionally exposed three pre-existing NULL-base
`qsort` calls in the sparse tree builder. Sorting is now skipped for fewer than
two entries, keeping empty construction valid under UBSan.

Generated-shader GPU build: 64/64 tests passed on the NVIDIA GeForce RTX 5060 Ti
with native Vulkan and CUDA arithmetic. The fresh explicitly disabled-glslang
build contained no generated SPIR-V includes: 47 tests passed and 17 Vulkan
shader paths skipped, with CUDA arithmetic still exercised. Both builds reran
the affected SDF suite after finalizing the automatic worker cap and procedural
signed interior values. C++11 public-header compilation/linking, CI YAML parsing,
strict C11 warnings for all three available task backends and whitespace checks
also passed. Apple GCD execution remains an unavailable local check, rather than
a claimed pass.

## Mesh/volume conversion: task parallelism and bounded edge caches (2026-10-02)

`tinyvdb_mesh_conversion.h` adds checked indexed marching cubes, an explicit
outward-winding option, and a reusable mesh-to-SDF workspace. The workspace
retains closest-triangle BVH data and face normals. Grid generation partitions
rows through the C11/GCD/pthread/serial task module, preserving each row's coherent
closest-face seed and the lowest-face-index tie break. The default caps workers
at eight. It no longer requires enabling OpenMP for mesh voxelization.

Marching cubes first counts shared crossing edges and triangles in parallel,
then emits the indexed mesh in stable raster/edge order. Output is allocated
exactly once per array, unless existing capacity suffices. Edge storage selects
the smaller of a rolling two-plane cache and a pre-sized surface hash. Rolling
storage uses `4 * (2*(nx-1)*ny + 2*nx*(ny-1) + nx*ny)` bytes, plus one count record
per z plane. The hash key encodes a 64-bit sample index and axis, avoiding the
old packed pair of 32-bit indices. Empty fields allocate no output or edge cache.
Emission remains serial; the multithreading gain reported for mesh voxelization
does not describe the entire marching-cubes algorithm.

Procedural benchmark on an AMD Ryzen Threadripper 1950X (16 cores, 32 logical
CPUs), Linux/GCC Release `-O3`, OpenMP and SIMD disabled for both mesh
implementations. The pre-change mesh implementation was rebuilt with the same
flags and linked into the same harness. Times are the minimum of three measured
runs after a warmup. Input fields cover `[-1,1]^3`, with a sphere radius of 0.7
or alternating checkerboard signs. The sphere mesh is oriented outward before
voxelization with spacing `2/n` and band `3*spacing`.

| Input | Before MC (ms) | After MC (ms) | Before default mesh-to-SDF (ms) | After default mesh-to-SDF (ms) |
|---|---:|---:|---:|---:|
| 64³ sphere, 9,408 vertices / 18,812 faces | 6.03 | 3.55 | 878.84 | 142.00 |
| 128³ sphere, 37,920 vertices / 75,836 faces | 22.71 | 19.64 | 11,277.43 | 1,615.35 |
| 64³ checkerboard, 774,144 vertices / 1,000,188 faces | 204.39 | 31.68 | — | — |

The sphere outputs contain 132,651 and 884,736 samples respectively. Default
128³ mesh voxelization improves by 6.98×. Reusing its acceleration gives
10,865.61 ms with one worker and 1,367.09 ms with eight (7.95×); BVH construction
takes 18.79 ms and retains 5,655,000 bytes. The one-worker result includes the
new numeric validation and fallback behavior. Timings depend on host load and
are observations, not performance guarantees.

Heap allocation instrumentation excludes the input grid, task pool/OS resources,
and allocator bookkeeping. The before/after fields produce identical counts.
Peak includes growing output/cache buffers that coexist before old buffers are
freed; retained bytes are output capacity after conversion.

| Input | Before peak bytes | After peak bytes | Before retained bytes | After retained bytes |
|---|---:|---:|---:|---:|
| 128³ sphere | 4,194,304 | 1,693,776 | 2,359,296 | 1,365,072 |
| 64³ checkerboard | 75,497,472 | 21,374,416 | 25,165,824 | 21,291,984 |

Peak drops by 59.6% and 71.7%, respectively. The checkerboard's new peak is
dominated by its required output: cache/count scratch is only 82,432 bytes.
Temporary normals, BVH data and edge caches always use the heap. Successful
arena conversion retains only its output and alignment padding; remeshing also
keeps the intermediate SDF off the output arena.

Reproduce the current procedural benchmark without external fixtures:

```sh
mesh_build=$(mktemp -d "${TMPDIR:-/tmp}/tinyvdb-mesh-bench.XXXXXX")
cmake -S . -B "$mesh_build" -G Ninja -DCMAKE_BUILD_TYPE=Release \
  -DTINYVDB_BUILD_BENCH=ON -DTINYVDB_BUILD_TESTS=OFF \
  -DTINYVDB_BUILD_EXAMPLES=OFF -DTINYVDB_BUILD_VDBRENDER=OFF \
  -DTINYVDB_BUILD_GPU=OFF -DTINYVDB_OPENMP=OFF -DTINYVDB_SIMD=OFF
cmake --build "$mesh_build" --target bench_mesh_conversion
"$mesh_build/bench_mesh_conversion" 64 0
"$mesh_build/bench_mesh_conversion" 128 0
"$mesh_build/bench_mesh_conversion" 64 1
```

Regression fixtures cover all 256 MC cases, planes, spheres, checkerboards,
random fields, exact-isovalue endpoints, a sparse surface using the hash cache,
append/capacity reuse, grid/mesh overlap and arena overlap before zeroing.
An independent triangle-soup reference verifies positions, topology and crossing
edge counts. One/eight-worker results are bit-identical. Box distances agree
with the analytic reference, and outward remeshing retains negative interior
values on re-voxelization. Invalid indices, nonfinite values/parameters, world
coordinate overflow and every conversion-owned allocation failure preserve
outputs; allocation tracking checks cleanup, peak scratch bounds and arena
retention.

The original interpolation returned an edge corner for both `±1e-30` and
`±FLT_MAX`, instead of the midpoint. CPU interpolation now uses double arithmetic;
Vulkan/CUDA scale large values by an exact power of two before subtraction.
Dividing by `FLT_MAX` was tested and rejected: the native Vulkan driver's
subnormal reciprocal flushed to zero. Native GPU regression tests explicitly
check finite output and include asymmetric large values. A repeated-edge triangle
previously produced NaN distances; degenerate closest-point predicates now fall
back to double segment/point distances with zero normals.

The checked mesh-to-SDF API replaces an initialized owning grid on success;
the legacy constructor still accepts an uninitialized output handle. Checked
marching cubes appends and offers outward winding for negative-inside fields.
The legacy MC entry point retains table winding; `tvdb_make_manifold` now requests
outward faces. Closest-face-normal signs remain approximate at sharp corners
and for open/inconsistently wound meshes. `_vdb` sign-method selection is still
advisory. Classic MC ambiguity and exact-isovalue degeneracies remain; this
change does not establish watertightness or a manifold guarantee.

Validation: scalar C11 ASan/LeakSanitizer/UBSan/float-cast-overflow 30/30;
SIMD/OpenMP 30/30 at one and eight OpenMP threads; explicit pthread and serial
backends 29/29 each. Pthread ThreadSanitizer passes the mesh-conversion and shared
task-pool suites. C11 ThreadSanitizer remains unavailable because of the host
runtime failure recorded above. Rebuilt Python bindings pass 110 tests with one
existing skip. The README example compiles as C11 and C++11; CI YAML and
whitespace checks pass. Native macOS/iOS execution is unavailable locally; the
macOS GCD/pthread CI matrix now includes both mesh-conversion regressions.

Final generated-shader GPU suite: 66/66 passed on NVIDIA GeForce RTX 5060 Ti,
driver 615.71.09, with native Vulkan device 0 and CUDA arithmetic. This includes
marching-cubes finite-value parity, mesh-to-SDF parity, allocation/dispatch failure
paths and the Vulkan shader ABI check. A fresh build with explicitly empty
`TINYVDB_GLSLANG_VALIDATOR` contains no generated SPIR-V includes: 49 tests passed
and 17 Vulkan shader paths skipped, with CUDA still exercised. A successful
fallback build is not counted as Vulkan arithmetic coverage.
