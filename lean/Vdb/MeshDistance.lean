/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Mesh-to-volume geometry: the distance to a segment (an edge of the mesh)
  and the capsule signed distance field (the swept sphere around an edge).
  The segment is compact and the space is proper, so the nearest point is
  attained; the distance is 1-Lipschitz, hence the capsule field is a signed
  distance field.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic
import Vdb.LevelSet

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

/-- The distance from a point to the closed segment `[a, b]`. -/
noncomputable def segDist (a b p : Point) : ℝ :=
  Metric.infDist p (segment ℝ a b)

theorem segDist_nonneg (a b p : Point) : 0 ≤ segDist a b p :=
  Metric.infDist_nonneg

theorem segDist_le_dist {a b : Point} {q : Point} (hq : q ∈ segment ℝ a b) (p : Point) :
    segDist a b p ≤ dist p q :=
  Metric.infDist_le_dist_of_mem hq

theorem segDist_abs_sub_le (a b p q : Point) :
    |segDist a b p - segDist a b q| ≤ dist p q := by
  have h1 : segDist a b p ≤ segDist a b q + dist p q := by
    simpa [segDist] using
      Metric.infDist_le_infDist_add_dist (s := segment ℝ a b) (x := p) (y := q)
  have h2 : segDist a b q ≤ segDist a b p + dist p q := by
    have := Metric.infDist_le_infDist_add_dist (s := segment ℝ a b) (x := q) (y := p)
    rw [dist_comm] at this
    simpa [segDist] using this
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The segment distance is 1-Lipschitz, i.e. a signed distance field shape. -/
theorem segDist_isSDF (a b : Point) : IsSDF (segDist a b) :=
  fun p q => segDist_abs_sub_le a b p q

theorem isCompact_segment' (a b : Point) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image (𝕜 := ℝ) a b]
  exact isCompact_Icc.image (by fun_prop)

/-- The minimum is attained on the segment (the space is proper and the
    segment is compact). -/
theorem segDist_exists_nearest (a b p : Point) :
    ∃ q : Point, q ∈ segment ℝ a b ∧ segDist a b p = dist p q :=
  (isCompact_segment' a b).exists_infDist_eq_dist ⟨a, left_mem_segment ℝ a b⟩ p

/-- The capsule field: the signed distance to the segment, shifted by `r`. -/
noncomputable def sdfCapsule (a b : Point) (r : ℝ) (p : Point) : ℝ :=
  segDist a b p - r

theorem sdfCapsule_isSDF (a b : Point) (r : ℝ) : IsSDF (sdfCapsule a b r) := by
  intro p q
  unfold sdfCapsule
  have h := segDist_abs_sub_le a b p q
  have he : |segDist a b p - r - (segDist a b q - r)| = |segDist a b p - segDist a b q| := by
    congr 1
    ring
  rw [he]
  exact h

theorem sdfCapsule_zero_iff (a b : Point) (r : ℝ) (p : Point) :
    sdfCapsule a b r p = 0 ↔ segDist a b p = r := by
  unfold sdfCapsule
  constructor <;> intro h <;> linarith

/-- The capsule surface consists exactly of the points at distance `r` from
    the segment, and the field magnitude is the distance to that set. -/
theorem sdfCapsule_exact (a b : Point) (r : ℝ) (p : Point) :
    (∃ q : Point, q ∈ segment ℝ a b ∧ segDist a b p = dist p q) ∧
      segDist a b p = sdfCapsule a b r p + r := by
  refine ⟨segDist_exists_nearest a b p, ?_⟩
  unfold sdfCapsule
  ring


/-! ### Unions of fields -/

theorem abs_min_sub_min_le_max' (a b c d : ℝ) :
    |min a b - min c d| ≤ max (|a - c|) (|b - d|) :=
  abs_min_sub_min_le_max a b c d

/-- The pointwise minimum of two signed distance fields is a signed distance
    field (the union of the two surfaces). -/
theorem IsSDF.min {f g : Point → ℝ} (hf : IsSDF f) (hg : IsSDF g) :
    IsSDF (fun p => min (f p) (g p)) := by
  intro p q
  refine le_trans (abs_min_sub_min_le_max (f p) (g p) (f q) (g q)) (max_le ?_ ?_)
  · exact hf p q
  · exact hg p q


/-! ### Finite meshes -/

/-- The point set of a finite mesh (a union of segments). -/
def meshSet (edges : Finset (Point × Point)) : Set Point :=
  {p | ∃ e ∈ edges, p ∈ segment ℝ e.1 e.2}

theorem meshSet_nonempty {edges : Finset (Point × Point)} (hne : edges.Nonempty) :
    (meshSet edges).Nonempty := by
  obtain ⟨e, he⟩ := hne
  exact ⟨e.1, e, he, left_mem_segment ℝ e.1 e.2⟩

theorem isCompact_meshSet (edges : Finset (Point × Point)) : IsCompact (meshSet edges) := by
  classical
  induction edges using Finset.induction_on with
  | empty => simp [meshSet]
  | insert e s he ih =>
    have hsplit : meshSet (insert e s) = segment ℝ e.1 e.2 ∪ meshSet s := by
      ext p
      simp only [meshSet, Finset.mem_insert, Set.mem_ofPred_eq, Set.mem_union]
      constructor
      · rintro ⟨e', rfl | hmem, hp⟩
        · exact Or.inl hp
        · exact Or.inr ⟨e', hmem, hp⟩
      · rintro (hp | ⟨e', hmem, hp⟩)
        · exact ⟨e, Or.inl rfl, hp⟩
        · exact ⟨e', Or.inr hmem, hp⟩
    rw [hsplit]
    exact (isCompact_segment' e.1 e.2).union ih

/-- The distance to a finite mesh. -/
noncomputable def meshDist (edges : Finset (Point × Point)) (p : Point) : ℝ :=
  Metric.infDist p (meshSet edges)

theorem meshDist_nonneg (edges : Finset (Point × Point)) (p : Point) :
    0 ≤ meshDist edges p :=
  Metric.infDist_nonneg

theorem meshDist_abs_sub_le (edges : Finset (Point × Point)) (p q : Point) :
    |meshDist edges p - meshDist edges q| ≤ dist p q := by
  have h1 : meshDist edges p ≤ meshDist edges q + dist p q := by
    simpa [meshDist] using
      Metric.infDist_le_infDist_add_dist (s := meshSet edges) (x := p) (y := q)
  have h2 : meshDist edges q ≤ meshDist edges p + dist p q := by
    have := Metric.infDist_le_infDist_add_dist (s := meshSet edges) (x := q) (y := p)
    rw [dist_comm] at this
    simpa [meshDist] using this
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem meshDist_isSDF (edges : Finset (Point × Point)) : IsSDF (meshDist edges) :=
  fun p q => meshDist_abs_sub_le edges p q

theorem meshDist_exists_nearest (edges : Finset (Point × Point)) (hne : edges.Nonempty)
    (p : Point) : ∃ q : Point, q ∈ meshSet edges ∧ meshDist edges p = dist p q :=
  (isCompact_meshSet edges).exists_infDist_eq_dist (meshSet_nonempty hne) p

/-- The mesh band field: the distance to the mesh shifted by `r`. -/
noncomputable def sdfMesh (edges : Finset (Point × Point)) (r : ℝ) (p : Point) : ℝ :=
  meshDist edges p - r

theorem sdfMesh_isSDF (edges : Finset (Point × Point)) (r : ℝ) : IsSDF (sdfMesh edges r) := by
  intro p q
  unfold sdfMesh
  have h := meshDist_abs_sub_le edges p q
  have he : |meshDist edges p - r - (meshDist edges q - r)| =
      |meshDist edges p - meshDist edges q| := by
    congr 1
    ring
  rw [he]
  exact h

theorem sdfMesh_zero_iff (edges : Finset (Point × Point)) (r : ℝ) (p : Point) :
    sdfMesh edges r p = 0 ↔ meshDist edges p = r := by
  unfold sdfMesh
  constructor <;> intro h <;> linarith

end Vdb
