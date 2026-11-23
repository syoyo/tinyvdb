/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-4 narrowphase: a broadphase bound. If a sphere of radius `r` touches a
  triangle at `q`, the sphere's axis-aligned box and the triangle's box must
  intersect; separated boxes can therefore be pruned without losing contacts.
  The proof is coordinatewise, using `abs_coord_le_dist` from the geometry layer.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Vdb.Convex
import Vdb.LevelSet

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

namespace NarrowPhase

/-- The axis-aligned box of a sphere. -/
def sphereBox (p : Point) (r : ℝ) : Box3 :=
  (WithLp.toLp 2 (fun i => p i - r), WithLp.toLp 2 (fun i => p i + r))

/-- A contact at `q` within radius `r` of `p` implies the sphere box contains
    `q` (hence intersects any box containing `q`). -/
theorem mem_sphereBox_of_contact {p q : Point} {r : ℝ}
    (hdist : dist p q ≤ r) : memBox (sphereBox p r) q := by
  intro i
  constructor
  · have h := abs_coord_le_dist p q i
    have hle : |p i - q i| ≤ r := h.trans hdist
    have : p i - q i ≤ r := le_trans (le_abs_self _) hle
    simp [sphereBox]
    linarith
  · have h := abs_coord_le_dist p q i
    have hle : |p i - q i| ≤ r := h.trans hdist
    have : q i - p i ≤ r := by
      have hneg : -(p i - q i) ≤ |p i - q i| := neg_le_abs _
      linarith
    simp [sphereBox]
    linarith

theorem boxes_intersect_of_contact {p q : Point} {r : ℝ} {b : Box3}
    (hdist : dist p q ≤ r) (hq : memBox b q) :
    ∃ x, memBox (sphereBox p r) x ∧ memBox b x :=
  ⟨q, mem_sphereBox_of_contact hdist, hq⟩

theorem sphereBox_disjoint_of_separated {p : Point} {r : ℝ} {b : Box3}
    (i : Fin 3) (h : b.2 i < p i - r) :
    Disjoint {x | memBox (sphereBox p r) x} {x | memBox b x} := by
  rw [Set.disjoint_left]
  intro x hx hb
  simp [sphereBox] at hx
  have hxi : p i - r ≤ x i := (hx i).1
  exact not_lt_of_ge hxi (lt_of_le_of_lt (hb i).2 h)

end NarrowPhase
end Vdb
