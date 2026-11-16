/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Follow-ups to `Vdb/WindingDipole.lean` (the Barnes–Hut dipole far field,
  `src/tinyvdb_winding.c`):

  * **`triResidual_eq_zero`** — the residual the landed `triNum = triDipole +
    ●` identity splits off (`dot a' (cross b' c')`, with `a', b', c'` the
    vertex deviations from the centroid) is **identically zero**: the
    deviations sum to zero, and a triple whose sum is zero has vanishing
    scalar triple product. The `triDipole_residual_bound` (`≤ ε³`) is
    therefore sharp as a bound on the triangle-determinant identity but
    **vacuous in its winding application** — the model's per-triangle
    dipole is exact, and the actual Barnes–Hut approximation error is the
    *aggregation* step (using one `1/|c̄ − p|³` for the cluster instead of the
    per-face factors), which `Vdb/WindingDipole.lean` does not model.
  * **`triNum_eq_dipole`** — the consequence: `triNum = triDipole` for every
    triangle. The C's far-node contribution is therefore exact in its
    numerator; the approximation lives entirely in `wn_solid_angle`'s
    `2·atan2(num, den)` (`den ≈ |a||b||c|` replaced by `|r|³`) and in the
    cluster aggregation.
  * **`tri_residual_tight`** — the generic bound `|dot a (cross b c)| ≤ ε³`
    of `tri_residual_abs_le` is attained (mutually orthogonal equal-length
    vectors): no uniform constant improvement is possible, which is the
    precise sense in which the residual bound is direction-dependent.

  What is **not** claimed: the asymptotic consistency of the C's far-field
  estimator against the exact sum (each far node's contribution tending to
  the exact sum as `p → ∞`), which requires real analysis (the `atan2`/`den`
  machinery). See the ledger.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.WindingDipole

set_option linter.unusedSimpArgs false

namespace Vdb

namespace V3

/-- The sum of three `V3`s is zero iff their scalar triple product is zero
    (`z = -x - y` kills `x · (y × z)`). Kept as a reusable determinant fact. -/
theorem dot_cross_of_sum_eq_zero {x y z : V3} (h : add (add x y) z = ⟨0, 0, 0⟩) :
    dot x (cross y z) = 0 := by
  have hx := congrArg V3.x h
  have hy := congrArg V3.y h
  have hz := congrArg V3.z h
  simp only [add] at hx hy hz
  have h1 : z.x = -(x.x + y.x) := by nlinarith [hx]
  have h2 : z.y = -(x.y + y.y) := by nlinarith [hy]
  have h3 : z.z = -(x.z + y.z) := by nlinarith [hz]
  unfold dot cross
  rw [h1, h2, h3]
  ring

/-- The vertex deviations from the centroid sum to zero. -/
theorem centroid_dev_sum_zero (A B C : V3) :
    add (add (sub A (centroid A B C)) (sub B (centroid A B C)))
        (sub C (centroid A B C)) = ⟨0, 0, 0⟩ := by
  apply V3.ext <;> simp [centroid, sub, add] <;> ring

/-- **The dipole residual is identically zero**: the `O(ε³)` term split off by
    `triDipole_identity` vanishes for every triangle. -/
theorem triResidual_eq_zero (A B C : V3) :
    dot (sub A (centroid A B C))
      (cross (sub B (centroid A B C)) (sub C (centroid A B C))) = 0 := by
  exact dot_cross_of_sum_eq_zero (centroid_dev_sum_zero A B C)

/-- **The per-triangle dipole term is exact**: `triNum = triDipole` for every
    triangle and query point. -/
theorem triNum_eq_dipole (A B C p : V3) :
    triNum A B C p = triDipole A B C p := by
  rw [triDipole_identity, triResidual_eq_zero]
  ring

/-- The generic triple-product bound `|dot a (cross b c)| ≤ ε³` is tight:
    with `a = ε • e₁`, `b = ε • e₂`, `c = ε • e₃` (mutually orthogonal,
    equal length) the determinant equals `ε³`. -/
theorem tri_residual_tight (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ a b c : V3,
      dot a a = ε ^ 2 ∧ dot b b = ε ^ 2 ∧ dot c c = ε ^ 2 ∧
        |dot a (cross b c)| = ε ^ 3 := by
  refine ⟨⟨ε, 0, 0⟩, ⟨0, ε, 0⟩, ⟨0, 0, ε⟩, ?_, ?_, ?_, ?_⟩
  · simp only [dot]; ring
  · simp only [dot]; ring
  · simp only [dot]; ring
  · simp only [dot, cross]
    have h : ε * (ε * ε - 0 * 0) + 0 * (0 * 0 - 0 * ε) + 0 * (0 * 0 - ε * 0) = ε ^ 3 := by ring
    rw [h, abs_of_nonneg (pow_nonneg hε 3)]

end V3

end Vdb
