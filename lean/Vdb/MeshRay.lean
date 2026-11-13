/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Ray-crossing parity for the concrete closed DMC surface.

  The non-planar bump field's dual vertices are exactly the cube corners
  `{1/6, 11/6}^3`, and its six dual quads are exactly the six faces of that
  cube. We triangulate each quad, cast the `+x` ray, and intersect it with
  each triangle (Möller–Trumbore, exact over `ℚ`). The crossing parity at
  sample points is inside exactly for points inside the cube; the signed
  Chebyshev field of the same cube supplies the zero set and sign.

  The concrete parity evaluations are `native_decide` checks (the project
  already uses `native_decide` for concrete characterisations); the signed
  field theorems are ordinary kernel-checked proofs.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.BoxInside
import Vdb.CubeField

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Vdb

/-! ### Ray–triangle intersection over `ℚ` -/

/-- The point `(x, y, z)` as a rational 3-vector. -/
def pt (x y z : ℚ) : RQ3
  | 0 => x
  | 1 => y
  | _ => z

def dot3 (u v : RQ3) : ℚ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

def sub3 (u v : RQ3) : RQ3 := fun i => u i - v i

def cross3 (u v : RQ3) : RQ3
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | _ => u 0 * v 1 - u 1 * v 0

/-- The `+x` ray direction. -/
def rayDir : RQ3
  | 0 => 1
  | _ => 0

/-- Möller–Trumbore ray–triangle intersection for the `+x` ray from `p`. -/
def rayTri (p a b c : RQ3) : Bool :=
  let e1 := sub3 b a
  let e2 := sub3 c a
  let h := cross3 rayDir e2
  let det := dot3 e1 h
  if det = 0 then false
  else
    let s := sub3 p a
    let u := dot3 s h / det
    let q := cross3 s e1
    let v := dot3 rayDir q / det
    let t := dot3 e2 q / det
    decide (0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1 ∧ 0 < t)

/-! ### The concrete bump surface -/

/-- The cube anchor as a rational point. -/
def anchorQ (c : C3) : RQ3
  | 0 => (c.1.val : ℚ)
  | 1 => (c.2.1.val : ℚ)
  | _ => (c.2.2.val : ℚ)

/-- The world dual vertex of a cube for the bump field (anchor + local
    average of its crossed-edge crossings). -/
def bumpCorner (c : C3) : RQ3 := fun i => anchorQ c i + fieldDualQ bumpField c i

/-- Two triangles of an index quad placed at the bump dual vertices. -/
def triOf (q : IxQuad C3) : List (RQ3 × RQ3 × RQ3) :=
  let v := bumpCorner
  [(v q.a, v q.b, v q.c), (v q.a, v q.c, v q.d)]

/-- The triangulated concrete bump surface. -/
def meshTris : List (RQ3 × RQ3 × RQ3) :=
  (stencilQuadsOf bumpSign).flatMap triOf

/-- The ray-crossing parity of the concrete surface at `p`. -/
def parity (p : RQ3) : Bool :=
  (meshTris.filter (fun t => rayTri p t.1 t.2.1 t.2.2)).length % 2 == 1

/-- The dual vertices are the cube corners `{1/6, 11/6}^3`. -/
theorem bumpCorner_cube :
    ∀ c : C3, ∀ i : Fin 3, bumpCorner c i = 1 / 6 ∨ bumpCorner c i = 11 / 6 := by
  native_decide

/-- The surface has twelve triangles. -/
theorem meshTris_length : meshTris.length = 12 := by
  native_decide

/-! ### Parity at sample points -/

/-- An inside point (not on a face diagonal): odd parity. -/
theorem parity_inside : parity (pt 1 (3 / 4) (5 / 4)) = true := by
  native_decide

/-- A point left of the cube: the ray enters and exits, even parity. -/
theorem parity_outside_left : parity (pt 0 (3 / 4) (5 / 4)) = false := by
  native_decide

/-- A point right of the cube: no crossing, even parity. -/
theorem parity_outside_right : parity (pt 2 (3 / 4) (5 / 4)) = false := by
  native_decide

/-- A point outside the `y`-range: the ray misses the cube. -/
theorem parity_outside_y : parity (pt 1 0 1) = false := by
  native_decide

/-- A point outside the `z`-range: the ray misses the cube. -/
theorem parity_outside_z : parity (pt 1 (3 / 4) 0) = false := by
  native_decide

/-! ### Signed Chebyshev field of the same cube -/

/-- The signed Chebyshev field of the cube `[1/6, 11/6]^3` (centre `(1,1,1)`,
    half-extent `5/6`). -/
def bumpFieldQ (p : RQ3) : ℚ :=
  max (|p 0 - 1| - 5 / 6) (max (|p 1 - 1| - 5 / 6) (|p 2 - 1| - 5 / 6))

/-- Strictly inside the cube. -/
def bumpInside (p : RQ3) : Prop := ∀ i : Fin 3, |p i - 1| < 5 / 6

/-- The signed field is negative exactly inside. -/
theorem bumpFieldQ_neg_iff (p : RQ3) :
    bumpFieldQ p < 0 ↔ bumpInside p := by
  unfold bumpFieldQ bumpInside
  rw [max_lt_iff, max_lt_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  · intro hall
    exact ⟨by simpa using hall 0, by simpa using hall 1, by simpa using hall 2⟩

/-- The signed field vanishes exactly on the cube boundary. -/
theorem bumpFieldQ_zero_iff (p : RQ3) :
    bumpFieldQ p = 0 ↔
      (∀ i : Fin 3, |p i - 1| ≤ 5 / 6) ∧ (∃ i : Fin 3, |p i - 1| = 5 / 6) := by
  unfold bumpFieldQ
  constructor
  · intro h0
    have hle := (max_le_iff.mp (le_of_eq h0))
    obtain ⟨h0', hrest⟩ := hle
    obtain ⟨h1', h2'⟩ := max_le_iff.mp hrest
    have hall : ∀ i : Fin 3, |p i - 1| - 5 / 6 ≤ 0 := by
      intro i; fin_cases i
      · simpa using h0'
      · simpa using h1'
      · simpa using h2'
    refine ⟨fun i => by linarith [hall i], ?_⟩
    have hge : 0 ≤ max (|p 0 - 1| - 5 / 6) (max (|p 1 - 1| - 5 / 6) (|p 2 - 1| - 5 / 6)) :=
      le_of_eq h0.symm
    rcases le_max_iff.mp hge with hA | hBC
    · exact ⟨0, by linarith [hall 0]⟩
    · rcases le_max_iff.mp hBC with hB | hC
      · exact ⟨1, by linarith [hall 1]⟩
      · exact ⟨2, by linarith [hall 2]⟩
  · rintro ⟨hle, i, hi⟩
    have hle' : max (|p 0 - 1| - 5 / 6) (max (|p 1 - 1| - 5 / 6) (|p 2 - 1| - 5 / 6)) ≤ 0 := by
      apply max_le
      · linarith [hle 0]
      · apply max_le <;> linarith [hle 1, hle 2]
    refine le_antisymm hle' ?_
    fin_cases i
    · have hi0 : |p 0 - 1| = 5 / 6 := by simpa using hi
      have h0 : |p 0 - 1| - 5 / 6 = 0 := by linarith
      calc (0 : ℚ) = |p 0 - 1| - 5 / 6 := h0.symm
        _ ≤ max (|p 0 - 1| - 5 / 6) (max (|p 1 - 1| - 5 / 6) (|p 2 - 1| - 5 / 6)) := le_max_left _ _
    · have hi1 : |p 1 - 1| = 5 / 6 := by simpa using hi
      have h1 : |p 1 - 1| - 5 / 6 = 0 := by linarith
      calc (0 : ℚ) = |p 1 - 1| - 5 / 6 := h1.symm
        _ ≤ max (|p 1 - 1| - 5 / 6) (|p 2 - 1| - 5 / 6) := le_max_left _ _
        _ ≤ max (|p 0 - 1| - 5 / 6) (max (|p 1 - 1| - 5 / 6) (|p 2 - 1| - 5 / 6)) := le_max_right _ _
    · have hi2 : |p 2 - 1| = 5 / 6 := by simpa using hi
      have h2 : |p 2 - 1| - 5 / 6 = 0 := by linarith
      calc (0 : ℚ) = |p 2 - 1| - 5 / 6 := h2.symm
        _ ≤ max (|p 1 - 1| - 5 / 6) (|p 2 - 1| - 5 / 6) := le_max_right _ _
        _ ≤ max (|p 0 - 1| - 5 / 6) (max (|p 1 - 1| - 5 / 6) (|p 2 - 1| - 5 / 6)) := le_max_right _ _

/-- The signed field is positive exactly outside (away from the boundary). -/
theorem bumpFieldQ_pos_iff (p : RQ3) :
    0 < bumpFieldQ p ↔ ¬ (∀ i : Fin 3, |p i - 1| ≤ 5 / 6) := by
  constructor
  · intro hp hle
    have h0 : bumpFieldQ p ≤ 0 := by
      unfold bumpFieldQ
      apply max_le
      · linarith [hle 0]
      · apply max_le <;> linarith [hle 1, hle 2]
    linarith
  · intro hout
    by_contra hnot
    apply hout
    have hle : bumpFieldQ p ≤ 0 := not_lt.mp hnot
    unfold bumpFieldQ at hle
    have h0 := (max_le_iff.mp hle)
    obtain ⟨h0', hrest⟩ := h0
    obtain ⟨h1', h2'⟩ := max_le_iff.mp hrest
    intro i
    fin_cases i
    · have h : |p 0 - 1| ≤ 5 / 6 := by linarith
      simpa using h
    · have h : |p 1 - 1| ≤ 5 / 6 := by linarith
      simpa using h
    · have h : |p 2 - 1| ≤ 5 / 6 := by linarith
      simpa using h

/-- Sign consistency at the inside sample point. -/
theorem bumpFieldQ_inside_point : bumpFieldQ (pt 1 (3 / 4) (5 / 4)) < 0 := by
  rw [bumpFieldQ_neg_iff]
  unfold bumpInside
  intro i
  fin_cases i <;> norm_num [pt]


/-! ### Face-level all-points parity and the triangle identification -/

/-- The x-interval parity for the cube `[1/6, 11/6]`: the `+x` ray crosses
    the two `x` faces, and the crossing parity is 1 exactly inside the slab. -/
theorem xFaceParity_iff (x : ℚ) (_h1 : x ≠ 1/6) (h2 : x ≠ 11/6) :
    (((1/6 < x) != (11/6 < x)) = true) ↔ |x - 1| < 5/6 := by
  constructor
  · intro hpar
    by_cases hA : 1/6 < x
    · by_cases hB : 11/6 < x
      · simp [hA, hB] at hpar
        linarith
      · have hxlt : x < 11/6 := lt_of_le_of_ne (not_lt.mp hB) h2
        rw [abs_lt]; constructor <;> linarith
    · have hB : ¬ 11/6 < x := by linarith
      simp [hA, hB] at hpar
      linarith
  · intro hin
    rw [abs_lt] at hin
    have hx1 : 1/6 < x := by linarith [hin.1]
    have hx2 : ¬ 11/6 < x := by linarith [hin.2]
    simp [hx1, hx2]
    linarith

/-- The face-level x-ray parity of the cube `[1/6, 11/6]^3`: crosses only when
    the other two coordinates are within the cube. -/
def boxFaceParity (p : RQ3) : Bool :=
  (decide (|p 1 - 1| ≤ 5/6) && decide (|p 2 - 1| ≤ 5/6)) &&
    ((1/6 < p 0) != (11/6 < p 0))

/-- **All-points inside test for the closed cube surface**: for a point off the
    boundary, the face-level ray parity is true exactly inside. -/
theorem boxFaceParity_iff (p : RQ3)
    (hbd : p 0 ≠ 1/6 ∧ p 0 ≠ 11/6 ∧ ∀ i : Fin 3, |p i - 1| ≠ 5/6) :
    boxFaceParity p = true ↔ bumpInside p := by
  unfold boxFaceParity bumpInside
  by_cases hy : |p 1 - 1| ≤ 5/6
  · by_cases hz : |p 2 - 1| ≤ 5/6
    · have hy' : |p 1 - 1| < 5/6 := lt_of_le_of_ne hy (hbd.2.2 1)
      have hz' : |p 2 - 1| < 5/6 := lt_of_le_of_ne hz (hbd.2.2 2)
      have hx := xFaceParity_iff (p 0) hbd.1 hbd.2.1
      simp only [hy, hz, decide_eq_true_eq, Bool.true_and]
      constructor
      · intro hpar i
        fin_cases i
        · simpa using hx.mp hpar
        · exact hy'
        · exact hz'
      · intro hall
        exact hx.mpr (by simpa using hall 0)
    · have hz' : 5/6 < |p 2 - 1| := lt_of_not_ge hz
      simp [hy, hz]
      exact ⟨2, le_of_lt hz'⟩
  · have hy' : 5/6 < |p 1 - 1| := lt_of_not_ge hy
    simp [hy]
    exact ⟨1, le_of_lt hy'⟩

/-- A rational point is one of the eight cube corners. -/
def isCubeCorner (v : RQ3) : Bool :=
  (decide (v 0 = 1/6) || decide (v 0 = 11/6)) &&
    ((decide (v 1 = 1/6) || decide (v 1 = 11/6)) &&
      (decide (v 2 = 1/6) || decide (v 2 = 11/6)))

/-- Every vertex of every triangle is a cube corner `{1/6, 11/6}^3`. -/
theorem meshTris_vertices_cube :
    (meshTris.all fun t =>
      isCubeCorner t.1 && isCubeCorner t.2.1 && isCubeCorner t.2.2) = true := by
  native_decide

/-- The concrete triangle parity agrees with the face parity at the inside
    sample point. -/
theorem parity_inside_face : parity (pt 1 (3/4) (5/4)) = boxFaceParity (pt 1 (3/4) (5/4)) := by
  native_decide

end Vdb
