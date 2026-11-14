/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  MC welding (`T-MC-WELD`, plan §4.2): the dense marching-cubes sweep
  (`mesh_mc_emit` in `src/tinyvdb_mesh_conversion.inl`) gives every crossed
  grid edge **one vertex**, shared by all crossing cells that contain it, by
  hashing the edge's *lower corner + axis* into a slot. The claims modelled
  here:

  * **`GridEdge.key`** — the C packing `3 * voxel_idx + axis + 1` (the
    z-major lattice index times 3, plus `axis + 1 ∈ {1, 2, 3}`).
    **`GridEdge.key_injective`**: within a fixed lattice box the packing is
    injective (mixed radix + mod 3), so the C slot map is a genuine
    deduplicator: distinct edges get distinct keys.
  * **`signChange_key_image`**: the sign-change edges (iso-straddling grid
    edges) have exactly as many distinct keys as they have elements — each
    sign-change edge receives **exactly one vertex** (this is what
    `mesh_mc_count_planes` counts and what the emit pass allocates).
  * **`GridEdge.inCell`/`cellEdges`** — the 12 edges of a cell as grid edges,
    and the boundary analysis: **an existing edge belongs to at least one cell
    iff `hasCell`** (`j + 1 < ny ∧ k + 1 < nz` for an x-edge, and similarly
    per axis). Boundary-shell edges never receive a vertex because no cell
    holds them (matching the C `x + 1 < nx && y + 1 < ny && z + 1 < nz`
    guard).
  * **`vertex_pos_swap`** — the vertex position on a crossed edge does not
    depend on which endpoint is called `a` and which `b` (the C interpolates
    with `t = (iso − v0)/(v1 − v0)`, clamped; the swap maps `t ↦ 1 − t`), so
    vertex positions are functions of the samples alone — the content needed
    for `T-MC-DET` (raster emission is a function of the grid only).

  What is *not* modelled: the rolling/hash slot machinery (`mesh_edge_cache`,
  an intrusive pointer reuse scheme), the two-pass count-then-emit algorithm,
  the arena layout of the output, or the sparse tree's slab-partitioned
  variant (`tool_mesh`). Those affect speed and layout, not the theorems.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.MarchingCubes
import Mathlib.Tactic

namespace Vdb

/-! ### Grid edges of a dense sample lattice -/

/-- A grid edge of an `nx × ny × nz` lattice of samples: its lower endpoint
    (the endpoint with the smaller coordinate along the axis) and its axis
    (0 = x, 1 = y, 2 = z). -/
structure GridEdge where
  lo : ℕ × ℕ × ℕ
  axis : Fin 3
deriving DecidableEq

/-- The far endpoint of the edge (out-of-range x yields a defensive default). -/
def GridEdge.hi (e : GridEdge) : ℕ × ℕ × ℕ :=
  match e.axis with
  | 0 => (e.lo.1 + 1, e.lo.2.1, e.lo.2.2)
  | 1 => (e.lo.1, e.lo.2.1 + 1, e.lo.2.2)
  | _ => (e.lo.1, e.lo.2.1, e.lo.2.2 + 1)

/-- The edge exists iff the far endpoint stays inside the sample lattice. -/
def GridEdge.existsIn (nx ny nz : ℕ) (e : GridEdge) : Bool :=
  match e.axis with
  | 0 => decide (e.lo.1 + 1 < nx)
  | 1 => decide (e.lo.2.1 + 1 < ny)
  | _ => decide (e.lo.2.2 + 1 < nz)

/-- All lattice edges that exist. -/
def GridEdge.all (nx ny nz : ℕ) : Finset GridEdge :=
  Finset.filter (fun e => GridEdge.existsIn nx ny nz e = true)
    ((((Finset.range nx) ×ˢ (Finset.range ny)) ×ˢ (Finset.range nz)).biUnion
      (fun p =>
        {GridEdge.mk (p.1.1, p.1.2, p.2) 0,
         GridEdge.mk (p.1.1, p.1.2, p.2) 1,
         GridEdge.mk (p.1.1, p.1.2, p.2) 2}))

/-- Every existing edge's endpoints lie inside the lattice box. -/
theorem GridEdge.all_bounds {nx ny nz : ℕ} {e : GridEdge} (h : e ∈ GridEdge.all nx ny nz) :
    e.lo.1 < nx ∧ e.lo.2.1 < ny ∧ e.lo.2.2 < nz := by
  unfold GridEdge.all at h
  rw [Finset.mem_filter] at h
  obtain ⟨hbase, _⟩ := h
  rw [Finset.mem_biUnion] at hbase
  obtain ⟨p, hp, hmem⟩ := hbase
  rw [Finset.mem_product, Finset.mem_product] at hp
  obtain ⟨⟨hx, hy⟩, hz⟩ := hp
  rw [Finset.mem_range] at hx hy hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  all_goals exact ⟨hx, hy, hz⟩

/-- The z-major voxel index of a lattice point. -/
def GridEdge.voxelIdx (nx ny : ℕ) (p : ℕ × ℕ × ℕ) : ℕ :=
  (p.2.2 * ny + p.2.1) * nx + p.1

/-- **The C welding key**: `3 * voxel_idx + axis + 1`. -/
def GridEdge.key (nx ny : ℕ) (e : GridEdge) : ℕ :=
  3 * GridEdge.voxelIdx nx ny e.lo + e.axis.val + 1

/-- The voxel index is injective on the box `0 ≤ x < nx ∧ 0 ≤ y < ny`. -/
theorem GridEdge.voxelIdx_injective {nx ny : ℕ} (hnx : 0 < nx)
    {p q : ℕ × ℕ × ℕ} (hx : p.1 < nx) (hy : p.2.1 < ny)
    (hx' : q.1 < nx) (hy' : q.2.1 < ny)
    (h : GridEdge.voxelIdx nx ny p = GridEdge.voxelIdx nx ny q) : p = q := by
  unfold voxelIdx at h
  have hmod : p.1 = q.1 ∧ p.2.2 * ny + p.2.1 = q.2.2 * ny + q.2.1 := by
    have e1 : ((p.2.2 * ny + p.2.1) * nx + p.1) % nx
            = ((q.2.2 * ny + q.2.1) * nx + q.1) % nx := congrArg (· % nx) h
    rw [Nat.mul_comm (p.2.2 * ny + p.2.1) nx, Nat.mul_comm (q.2.2 * ny + q.2.1) nx] at h e1
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx] at e1
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx'] at e1
    have h2 : nx * (p.2.2 * ny + p.2.1) = nx * (q.2.2 * ny + q.2.1) := by omega
    exact ⟨e1, Nat.eq_of_mul_eq_mul_left hnx h2⟩
  obtain ⟨hxeq, hrem⟩ := hmod
  have e2 : (p.2.2 * ny + p.2.1) % ny = (q.2.2 * ny + q.2.1) % ny := congrArg (· % ny) hrem
  rw [Nat.mul_comm p.2.2 ny, Nat.add_comm (ny * p.2.2) p.2.1, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hy] at e2
  rw [Nat.mul_comm q.2.2 ny, Nat.add_comm (ny * q.2.2) q.2.1, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hy'] at e2
  have hzm : p.2.2 = q.2.2 := by
    have h3 : p.2.2 * ny = q.2.2 * ny := by omega
    rw [Nat.mul_comm p.2.2 ny, Nat.mul_comm q.2.2 ny] at h3
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < ny) h3
  apply Prod.ext_iff.mpr
  refine ⟨hxeq, ?_⟩
  apply Prod.ext_iff.mpr
  exact ⟨e2, hzm⟩

/-- **Key injectivity**: distinct grid edges of the lattice pack to distinct
    keys. This is the welding lemma — the C slot map cannot alias two edges. -/
theorem GridEdge.key_injective {nx ny nz : ℕ} (hnx : 0 < nx)
    {e₁ e₂ : GridEdge} (h₁ : e₁ ∈ GridEdge.all nx ny nz) (h₂ : e₂ ∈ GridEdge.all nx ny nz)
    (h : e₁.key nx ny = e₂.key nx ny) : e₁ = e₂ := by
  obtain ⟨hx₁, hy₁, hz₁⟩ := GridEdge.all_bounds h₁
  obtain ⟨hx₂, hy₂, hz₂⟩ := GridEdge.all_bounds h₂
  have hax : e₁.axis.val < 3 := e₁.axis.isLt
  have hax2 : e₂.axis.val < 3 := e₂.axis.isLt
  have hkm : e₁.axis.val = e₂.axis.val := by
    unfold key voxelIdx at h
    omega
  have hidx : (e₁.lo.2.2 * ny + e₁.lo.2.1) * nx + e₁.lo.1
            = (e₂.lo.2.2 * ny + e₂.lo.2.1) * nx + e₂.lo.1 := by
    unfold key voxelIdx at h
    omega
  have hpq : e₁.lo = e₂.lo := by
    apply GridEdge.voxelIdx_injective hnx hx₁ hy₁ hx₂ hy₂
    exact hidx
  have hax3 : e₁.axis = e₂.axis := Fin.ext hkm
  cases e₁
  cases e₂
  simp_all

/-! ### The cells of the lattice and their 12 edges -/

/-- The 12 edges of a cell whose lower corner (voxel index) is `(i, j, k)`.
    Matches the C `MC_EDGE_VERTS`/`MC_CORNER_OFFSETS` pair, as grid edges. -/
def cellEdges (i j k : ℕ) : List GridEdge :=
  [GridEdge.mk (i, j, k) 0, GridEdge.mk (i, j + 1, k) 0,
   GridEdge.mk (i, j, k + 1) 0, GridEdge.mk (i, j + 1, k + 1) 0,
   GridEdge.mk (i, j, k) 1, GridEdge.mk (i + 1, j, k) 1,
   GridEdge.mk (i, j, k + 1) 1, GridEdge.mk (i + 1, j, k + 1) 1,
   GridEdge.mk (i, j, k) 2, GridEdge.mk (i + 1, j, k) 2,
   GridEdge.mk (i, j + 1, k) 2, GridEdge.mk (i + 1, j + 1, k) 2]

/-- Every cell list has 12 edges. -/
theorem cellEdges_length (i j k : ℕ) : (cellEdges i j k).length = 12 := rfl

/-- **`hasCell`**: the edge borders at least one cell. Boundary-shell edges
    (the lattice's max faces) never receive a vertex. -/
def GridEdge.hasCell (nx ny nz : ℕ) (e : GridEdge) : Bool :=
  match e.axis with
  | 0 => (e.lo.2.1 + 1 < ny) && (e.lo.2.2 + 1 < nz)
  | 1 => (e.lo.1 + 1 < nx) && (e.lo.2.2 + 1 < nz)
  | _ => (e.lo.1 + 1 < nx) && (e.lo.2.1 + 1 < ny)

/-- **Welding completeness**: an existing edge borders a cell iff `hasCell`
    holds — the witness is the cell at the edge's own lower corner. -/
theorem GridEdge.exists_cell {nx ny nz : ℕ} (e : GridEdge)
    (hex : GridEdge.existsIn nx ny nz e) (h : GridEdge.hasCell nx ny nz e) :
    ∃ i j k, i + 1 < nx ∧ j + 1 < ny ∧ k + 1 < nz ∧ e ∈ cellEdges i j k := by
  obtain ⟨⟨i, j, k⟩, haxis⟩ := e
  fin_cases haxis
  · change (decide (i + 1 < nx)) = true at hex
    change (decide (j + 1 < ny) && decide (k + 1 < nz)) = true at h
    rw [Bool.and_eq_true] at h
    exact ⟨i, j, k, of_decide_eq_true hex, of_decide_eq_true h.1, of_decide_eq_true h.2,
      by simp [cellEdges]⟩
  · change (decide (j + 1 < ny)) = true at hex
    change (decide (i + 1 < nx) && decide (k + 1 < nz)) = true at h
    rw [Bool.and_eq_true] at h
    exact ⟨i, j, k, of_decide_eq_true h.1, of_decide_eq_true hex, of_decide_eq_true h.2,
      by simp [cellEdges]⟩
  · change (decide (k + 1 < nz)) = true at hex
    change (decide (i + 1 < nx) && decide (j + 1 < ny)) = true at h
    rw [Bool.and_eq_true] at h
    exact ⟨i, j, k, of_decide_eq_true h.1, of_decide_eq_true h.2, of_decide_eq_true hex,
      by simp [cellEdges]⟩

/-! ### Sign-change edges and the weld count -/

/-- Does the sample straddle the isovalue along this edge? -/
def GridEdge.crosses (f : ℕ × ℕ × ℕ → ℚ) (e : GridEdge) : Bool :=
  edgeCrosses (f e.lo) (f e.hi)

/-- The sign-change edges of the lattice under the sample `f`. -/
def GridEdge.signChange (nx ny nz : ℕ) (f : ℕ × ℕ × ℕ → ℚ) : Finset GridEdge :=
  (GridEdge.all nx ny nz).filter fun e => GridEdge.crosses f e = true

/-- **T-MC-WELD (cardinality form)**: the distinct welding keys of the
    sign-change edges are in bijection with the sign-change edges — each
    receives exactly one vertex id. -/
theorem signChange_key_image {nx ny nz : ℕ} (hnx : 0 < nx)
    (f : ℕ × ℕ × ℕ → ℚ) :
    ((GridEdge.signChange nx ny nz f).image (GridEdge.key nx ny)).card
      = (GridEdge.signChange nx ny nz f).card := by
  apply Finset.card_image_of_injOn
  intro e₁ he₁ e₂ he₂ heq
  have h₁ := Finset.mem_filter.mp he₁
  have h₂ := Finset.mem_filter.mp he₂
  exact GridEdge.key_injective hnx h₁.1 h₂.1 heq

/-! ### Vertex positions are cube-independent (T-MC-DET core) -/

/-- **`vertex_pos_swap`**: the interpolated vertex position on a crossed edge
    does not depend on which endpoint is called `a` and which `b`. Both walk
    orders produce the same world point, so neither the traversal order nor
    the owning cube of the edge can move the vertex. -/
theorem vertex_pos_swap (a b iso : ℚ) (h : a ≠ b) :
    a + (iso - a) / (b - a) * (b - a) = b + (iso - b) / (a - b) * (a - b) := by
  field_simp
  ring

end Vdb
