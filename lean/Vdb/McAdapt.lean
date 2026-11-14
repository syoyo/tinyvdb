/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  MC adaptive-vertex clustering (`tool_adapt`, `src/tinyvdb_sparse_tools.c`) —
  the ℝ-level clustering guarantee, proved over `Point =
  EuclideanSpace ℝ (Fin 3)`, the same model used by the level-set modules.

  The C tool clusters vertices into cells with a per-axis Morton-style key
  `⌊v / step⌋` (`step = tolerance / √3`), merges a same-cell group into its
  average **only when** all members are within `tolerance` of the average
  (the `safe` loop — enforced by the C), and otherwise keeps the vertices
  separate. What is provable over ℝ, and pinned here:

  * `same_cell_coord_abs_le` — same cell ⇒ |uᵢ − vᵢ| ≤ step per axis.
  * `same_cell_dist_le` — same cell ⇒ dist u v ≤ √3 · step
    (= `tolerance` when `step = tolerance / √3`).
  * `same_cell_dist_le_tolerance` — the clustering-scale corollary: any two
    vertices that cluster into one cell are within `tolerance` of each other,
    exactly what the caller's `tolerance` parameter promises.
  * `cell_midpoint_coord_abs_le` / `midpoint_dist_le` — the cell midpoint is
    within step/2 per axis, `√3/2 · step` overall, and `tolerance / 2` at the
    clustering scale.

  Deliberately not modelled (out of scope, as before): the Float floor
  semantics for negative/overflowing coordinates (the `isfinite` guard,
  `q < 2^63`), the int64 key packing, the Morton comparison order and the
  `memcmp` on the three keys, the hash/queue of the clustering passes, and
  the C `safe` re-check itself (it is an enforcement, not a theorem).
  Quantify over ℝ only.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Defs

namespace Vdb

/-- Points in 3D, the model of `tool_adapt`'s vertex coordinates. -/
abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- A cell midpoint vector: per axis, `(⌊uᵢ / s⌋ + 1/2) · s`. -/
noncomputable def cellMidpoint (s : ℝ) (u : Point) : Point :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => (⌊u i / s⌋ + 1 / 2) * s)

@[simp]
theorem cellMidpoint_apply (s : ℝ) (u : Point) (i : Fin 3) :
    cellMidpoint s u i = (⌊u i / s⌋ + 1 / 2) * s :=
  rfl

/-- Same-cell membership: equal per-axis Morton keys, mirroring the C
    `memcmp(clusters[i].c, clusters[j].c, 3·sizeof(int64_t))`. -/
def SameCell (s : ℝ) (u v : Point) : Prop :=
  ∀ i, ⌊u i / s⌋ = ⌊v i / s⌋

/-- The shared floor inequalities for `u i / s` and `v i / s`, both pinned by
    the common cell key. -/
theorem floor_interval {s : ℝ} (hs : 0 < s) {u v : Point} (h : SameCell s u v)
    (i : Fin 3) :
    (⌊u i / s⌋ : ℝ) * s ≤ u i ∧ u i < (⌊u i / s⌋ + 1) * s ∧
      (⌊u i / s⌋ : ℝ) * s ≤ v i ∧ v i < (⌊u i / s⌋ + 1) * s := by
  have hk : ⌊v i / s⌋ = ⌊u i / s⌋ := (h i).symm
  have h1u : (⌊u i / s⌋ : ℝ) ≤ u i / s := Int.floor_le _
  have h2u : u i / s < ⌊u i / s⌋ + 1 := Int.lt_floor_add_one _
  have h1v : (⌊v i / s⌋ : ℝ) ≤ v i / s := Int.floor_le _
  have h2v : v i / s < ⌊v i / s⌋ + 1 := Int.lt_floor_add_one _
  rw [hk] at h1v h2v
  constructor
  · rwa [le_div_iff₀ hs] at h1u
  constructor
  · exact (div_lt_iff₀ hs).mp h2u
  constructor
  · rwa [le_div_iff₀ hs] at h1v
  · exact (div_lt_iff₀ hs).mp h2v

/-- Two vertices in the same cell differ by at most one cell width per axis. -/
theorem same_cell_coord_abs_le {s : ℝ} (hs : 0 < s) {u v : Point}
    (h : SameCell s u v) (i : Fin 3) : |u i - v i| ≤ s := by
  obtain ⟨h1u, h2u, h1v, h2v⟩ := floor_interval hs h i
  rw [abs_le]
  constructor <;> nlinarith

/-- Same cell ⇒ Euclidean distance at most `√3 · step`. -/
theorem same_cell_dist_le {s : ℝ} (hs : 0 < s) {u v : Point} (h : SameCell s u v) :
    dist u v ≤ Real.sqrt 3 * s := by
  rw [EuclideanSpace.dist_eq]
  have hsum : (∑ i : Fin 3, dist (u i) (v i) ^ 2) ≤ 3 * s ^ 2 := by
    calc (∑ i : Fin 3, dist (u i) (v i) ^ 2)
        ≤ ∑ _i : Fin 3, s ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [Real.dist_eq]
            exact pow_le_pow_left₀ (abs_nonneg _) (same_cell_coord_abs_le hs h i) 2
      _ = 3 * s ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc √(∑ i : Fin 3, dist (u i) (v i) ^ 2)
      ≤ √(3 * s ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 3 * s := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_sq hs.le]

/-- At the C clustering scale (`step = tolerance / √3`), two vertices that
    fall into one clustering cell are within `tolerance` of each other. -/
theorem same_cell_dist_le_tolerance {s : ℝ} {u v : Point} {tolerance : ℝ}
    (ht : 0 < tolerance) (hstep : s = tolerance / Real.sqrt 3) (h : SameCell s u v) :
    dist u v ≤ tolerance := by
  have hs : 0 < s := by
    rw [hstep]
    exact div_pos ht (Real.sqrt_pos.mpr (by norm_num))
  have h1 := same_cell_dist_le hs h
  rw [hstep] at h1
  have h3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h2 : Real.sqrt 3 * (tolerance / Real.sqrt 3) = tolerance := by
    field_simp
  rwa [h2] at h1

/-- The floor inequalities a single vertex satisfies, for the midpoint bound. -/
theorem floor_interval_self {s : ℝ} (hs : 0 < s) (u : Point) (i : Fin 3) :
    (⌊u i / s⌋ : ℝ) * s ≤ u i ∧ u i < (⌊u i / s⌋ + 1) * s := by
  have h1u : (⌊u i / s⌋ : ℝ) ≤ u i / s := Int.floor_le _
  have h2u : u i / s < ⌊u i / s⌋ + 1 := Int.lt_floor_add_one _
  constructor
  · rwa [le_div_iff₀ hs] at h1u
  · exact (div_lt_iff₀ hs).mp h2u

/-- Per-coordinate deviation of a vertex from its cell midpoint. -/
theorem cell_midpoint_coord_abs_le {s : ℝ} (hs : 0 < s) (u : Point) (i : Fin 3) :
    |u i - cellMidpoint s u i| ≤ s / 2 := by
  rw [cellMidpoint_apply]
  obtain ⟨h1u, h2u⟩ := floor_interval_self hs u i
  rw [abs_le]
  constructor <;> nlinarith

/-- Distance from a vertex to its cell midpoint is at most `√3/2 · step`. -/
theorem midpoint_dist_le {s : ℝ} (hs : 0 < s) (u : Point) :
    dist u (cellMidpoint s u) ≤ Real.sqrt 3 * (s / 2) := by
  rw [EuclideanSpace.dist_eq]
  have hsum : (∑ i : Fin 3, dist (u i) (cellMidpoint s u i) ^ 2) ≤ 3 * (s / 2) ^ 2 := by
    calc (∑ i : Fin 3, dist (u i) (cellMidpoint s u i) ^ 2)
        ≤ ∑ _i : Fin 3, (s / 2) ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [Real.dist_eq]
            exact pow_le_pow_left₀ (abs_nonneg _) (cell_midpoint_coord_abs_le hs u i) 2
      _ = 3 * (s / 2) ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  calc √(∑ i : Fin 3, dist (u i) (cellMidpoint s u i) ^ 2)
      ≤ √(3 * (s / 2) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 3 * (s / 2) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_sq (by positivity)]

/-- At the clustering scale, the midpoint is within `tolerance / 2` —
    the clustering representative's maximal per-vertex distortion. -/
theorem midpoint_dist_le_half_tolerance {s : ℝ} {u : Point} {tolerance : ℝ}
    (ht : 0 < tolerance) (hstep : s = tolerance / Real.sqrt 3) :
    dist u (cellMidpoint s u) ≤ tolerance / 2 := by
  subst hstep
  have hs : (0:ℝ) < tolerance / Real.sqrt 3 :=
    div_pos ht (Real.sqrt_pos.mpr (by norm_num))
  have h1 := midpoint_dist_le hs u
  have h2 : Real.sqrt 3 * (tolerance / Real.sqrt 3 / 2) = tolerance / 2 := by
    field_simp
  rwa [h2] at h1

end Vdb
