/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The **far-field asymptotic consistency of the dipole** approximation
  (`src/tinyvdb_winding.c`, `TVDB_WINDING_FAST`): along a ray `p = t • d`
  with `d ≠ 0`, the solid angle of a fixed triangle and the per-face
  dipole term the C's Barnes–Hut tree aggregates for a far node agree to
  second order:

  * both `solidAngle A B C (t • d)` and `faceDipole A B C (t • d)` are
    `-(T · d)/(2|d|³) · t⁻²` + lower order, so
    `t² · (solidAngle - faceDipole) → 0` as `t → ∞` — the error is
    `o(t⁻²)`, the classical far-field consistency of the dipole
    approximation.

  Proof sketch. The numerator is affine in `t`: `num(t) = c₂·t + c₃` with
  `c₂ = -(T·d)` (machine-checked, `triNum_sub_ray`). The denominator is
  asymptotically `4|d|³t³` (each of the four terms tends to `|d|³t³`).
  The arc-tangent tail bound `|atan x - x| ≤ |x|³/3` (landed in
  `Vdb/WindingDipole.lean`) makes `wn = 2·atan2'(num, den)` indistinguishable
  from `2·(num/den)` at this order. The dipole term `D = (T/2·r)/|r|³`
  with `r = ctr - t·d` matches at the same leading order
  (`faceDipole_t2`). The two leading coefficients are equal
  (`triNum_sub_ray`), so the difference is `o(t⁻²)`.

  What is **not** claimed: the error for a *bounded* query point, the
  closed-form remainder (it involves the octupole moment of the triangle,
  not modelled), and the whole-tree cutoff argument (every node becomes
  far eventually) — that is a statement about the C program's tree, not
  about this per-face identity. The consistency here is per face; the
  aggregate error is additive over faces (`meshWinding_append`).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.WindingDipole
import Vdb.WindingNumber
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Topology Filter
open Vdb Vdb.V3

namespace Vdb

/-! ### The ray and the field components -/

/-- The ray from the origin through `d` at parameter `t`: the query point
    `t • d`. -/
def ray (t : ℝ) (d : V3) : V3 := ⟨t * d.x, t * d.y, t * d.z⟩

/-- The C code's `num` (Van Oosterom–Strackee numerator), along `ray`. -/
def numOf (A B C d : V3) (t : ℝ) : ℝ := triNum A B C (ray t d)

/-- The C code's `den` (the four-term denominator of the solid angle). -/
noncomputable def denOf (A B C d : V3) (t : ℝ) : ℝ :=
  Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) *
    Real.sqrt (dot (sub B (ray t d)) (sub B (ray t d))) *
    Real.sqrt (dot (sub C (ray t d)) (sub C (ray t d)))
  + dot (sub A (ray t d)) (sub B (ray t d)) * Real.sqrt (dot (sub C (ray t d)) (sub C (ray t d)))
  + dot (sub B (ray t d)) (sub C (ray t d)) * Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d)))
  + dot (sub C (ray t d)) (sub A (ray t d)) * Real.sqrt (dot (sub B (ray t d)) (sub B (ray t d)))

/-- The C code's far-node dipole contribution per face: `dot T r / (2 |r|³)`
    with `r = centroid - p` (`N = T/2` is the area-weighted normal sum of the
    face). -/
noncomputable def faceDipole (A B C d : V3) (t : ℝ) : ℝ :=
  dot (T A B C) (sub (centroid A B C) (ray t d))
    / (2 * (Real.sqrt (dot (sub (centroid A B C) (ray t d))
      (sub (centroid A B C) (ray t d)))) ^ 3)

/-! ### Polynomial identities (all closed by `ring`) -/

theorem dot_sub_ray_self (A d : V3) (t : ℝ) :
    dot (sub A (ray t d)) (sub A (ray t d))
      = dot A A - 2 * t * dot A d + t ^ 2 * dot d d := by
  unfold ray sub dot
  ring

theorem dot_sub_ray (A B d : V3) (t : ℝ) :
    dot (sub A (ray t d)) (sub B (ray t d))
      = dot A B - t * dot A d - t * dot B d + t ^ 2 * dot d d := by
  unfold ray sub dot
  ring

theorem triNum_affine (A B C d : V3) (t : ℝ) :
    triNum A B C (ray t d)
      = t * (triNum A B C (ray 1 d) - triNum A B C (ray 0 d)) + triNum A B C (ray 0 d) := by
  simp only [ray, triNum, sub, dot, cross]
  ring

/-- The leading coefficient of the numerator is `-(T · d)`. -/
theorem triNum_sub_ray (A B C d : V3) :
    triNum A B C (ray 1 d) - triNum A B C (ray 0 d) = -dot (T A B C) d := by
  simp only [ray, triNum, T, sub, dot, cross, add]
  ring

/-! ### Basic convergence helpers -/

theorem tendsto_const_div_atTop (c : ℝ) :
    Tendsto (fun t : ℝ => c / t) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h := h.const_mul c
  simp only [mul_zero] at h
  exact h.congr fun t => (div_eq_mul_inv c t).symm

theorem tendsto_const_div_sq_atTop (c : ℝ) :
    Tendsto (fun t : ℝ => c / t ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h1 := (h.mul h).const_mul c
  simp only [mul_zero] at h1
  exact h1.congr fun t => by
    rw [pow_two, div_eq_mul_inv, mul_inv]

/-- The t²-scaled norm expansion converges to `dot d d`. -/
theorem sqAux_tendsto (A d : V3) :
    Tendsto (fun t : ℝ => dot A A / t ^ 2 - 2 * dot A d / t + dot d d) atTop (𝓝 (dot d d)) := by
  have h1 := (tendsto_const_div_sq_atTop (dot A A)).sub (tendsto_const_div_atTop (2 * dot A d))
  simp only [sub_zero] at h1
  simpa using h1.add_const (dot d d)

/-- Norm expansion identity. -/
theorem sqNorm_expand (A d : V3) (t : ℝ) :
    dot (sub A (ray t d)) (sub A (ray t d))
      = dot A A - 2 * t * dot A d + t ^ 2 * dot d d := dot_sub_ray_self A d t

/-- The t²-scaled norm converges to `dot d d`. -/
theorem sqNorm_div_tendsto (A d : V3) :
    Tendsto (fun t : ℝ => dot (sub A (ray t d)) (sub A (ray t d)) / t ^ 2)
      atTop (𝓝 (dot d d)) := by
  have heq : (fun t : ℝ => dot A A / t ^ 2 - 2 * dot A d / t + dot d d) =ᶠ[atTop]
      (fun t : ℝ => dot (sub A (ray t d)) (sub A (ray t d)) / t ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [sqNorm_expand]
    field_simp
  exact (sqAux_tendsto A d).congr' heq

/-- The inner-product analogue (each bilinear term). -/
theorem dot_sub_ray_div_tendsto (A B d : V3) :
    Tendsto (fun t : ℝ => dot (sub A (ray t d)) (sub B (ray t d)) / t ^ 2)
      atTop (𝓝 (dot d d)) := by
  have hexpand : ∀ t : ℝ, dot (sub A (ray t d)) (sub B (ray t d))
      = dot A B - t * dot A d - t * dot B d + t ^ 2 * dot d d := fun t => dot_sub_ray A B d t
  have heq : (fun t => dot A B / t ^ 2 - dot A d / t - dot B d / t + dot d d) =ᶠ[atTop]
      (fun t : ℝ => dot (sub A (ray t d)) (sub B (ray t d)) / t ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [hexpand]
    field_simp
  have h1 := ((tendsto_const_div_sq_atTop (dot A B)).sub (tendsto_const_div_atTop (dot A d))).sub
    (tendsto_const_div_atTop (dot B d))
  simp only [sub_zero] at h1
  have h2 : Tendsto (fun t : ℝ => dot A B / t ^ 2 - dot A d / t - dot B d / t + dot d d) atTop
      (𝓝 (dot d d)) := by
    simpa using h1.add_const (dot d d)
  exact h2.congr' heq

/-- `sqrtAux` is nonnegative (it is the squared norm divided by t²). -/
theorem sqrtAux_nonneg (A d : V3) {t : ℝ} (ht : t ≠ 0) :
    0 ≤ dot A A / t ^ 2 - 2 * dot A d / t + dot d d := by
  have e : dot (sub A (ray t d)) (sub A (ray t d)) / t ^ 2
      = dot A A / t ^ 2 - 2 * dot A d / t + dot d d := by
    rw [sqNorm_expand]
    field_simp
  rw [← e]
  exact div_nonneg (dot_self_nonneg _) (sq_nonneg t)

/-- The t-scaled square root of the squared norm tends to `|d|`. -/
theorem sqrtNorm_div_tendsto (A d : V3) :
    Tendsto (fun t : ℝ => Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t)
      atTop (𝓝 (Real.sqrt (dot d d))) := by
  have heq : (fun t : ℝ => Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t) =ᶠ[atTop]
      fun t => Real.sqrt (dot A A / t ^ 2 - 2 * dot A d / t + dot d d) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hsq : (Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t) ^ 2
        = dot A A / t ^ 2 - 2 * dot A d / t + dot d d := by
      rw [div_pow, Real.sq_sqrt (dot_self_nonneg _), sqNorm_expand]
      field_simp
    have hnn : 0 ≤ Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t :=
      div_nonneg (Real.sqrt_nonneg _) ht.le
    rw [← Real.sqrt_sq hnn, hsq]
  exact ((Real.continuous_sqrt.tendsto _).comp (sqAux_tendsto A d)).congr' heq.symm



/-! ### The denominator's asymptotic `4 |d|³ t³` -/

theorem denOf_div_tendsto (A B C d : V3) :
    Tendsto (fun t : ℝ => denOf A B C d t / t ^ 3)
      atTop (𝓝 (4 * Real.sqrt (dot d d) ^ 3)) := by
  have hna := sqrtNorm_div_tendsto A d
  have hnb := sqrtNorm_div_tendsto B d
  have hnc := sqrtNorm_div_tendsto C d
  have hab := dot_sub_ray_div_tendsto A B d
  have hbc := dot_sub_ray_div_tendsto B C d
  have hca := dot_sub_ray_div_tendsto C A d
  have h1 : Tendsto (fun t : ℝ =>
      Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t *
        (Real.sqrt (dot (sub B (ray t d)) (sub B (ray t d))) / t) *
        (Real.sqrt (dot (sub C (ray t d)) (sub C (ray t d))) / t))
      atTop (𝓝 (Real.sqrt (dot d d) * Real.sqrt (dot d d) * Real.sqrt (dot d d))) :=
    (hna.mul hnb).mul hnc
  have h2 : Tendsto (fun t : ℝ =>
      dot (sub A (ray t d)) (sub B (ray t d)) / t ^ 2 *
        (Real.sqrt (dot (sub C (ray t d)) (sub C (ray t d))) / t))
      atTop (𝓝 (dot d d * Real.sqrt (dot d d))) := hab.mul hnc
  have h3 : Tendsto (fun t : ℝ =>
      dot (sub B (ray t d)) (sub C (ray t d)) / t ^ 2 *
        (Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t))
      atTop (𝓝 (dot d d * Real.sqrt (dot d d))) := hbc.mul hna
  have h4 : Tendsto (fun t : ℝ =>
      dot (sub C (ray t d)) (sub A (ray t d)) / t ^ 2 *
        (Real.sqrt (dot (sub B (ray t d)) (sub B (ray t d))) / t))
      atTop (𝓝 (dot d d * Real.sqrt (dot d d))) := hca.mul hnb
  have heq : (fun t : ℝ => denOf A B C d t / t ^ 3) =ᶠ[atTop]
      (fun t : ℝ =>
        Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t *
          (Real.sqrt (dot (sub B (ray t d)) (sub B (ray t d))) / t) *
          (Real.sqrt (dot (sub C (ray t d)) (sub C (ray t d))) / t)
        + dot (sub A (ray t d)) (sub B (ray t d)) / t ^ 2 *
            (Real.sqrt (dot (sub C (ray t d)) (sub C (ray t d))) / t)
        + dot (sub B (ray t d)) (sub C (ray t d)) / t ^ 2 *
            (Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t)
        + dot (sub C (ray t d)) (sub A (ray t d)) / t ^ 2 *
            (Real.sqrt (dot (sub B (ray t d)) (sub B (ray t d))) / t)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [denOf]
    field_simp
  have hsum : Tendsto (fun t : ℝ =>
        Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t *
          (Real.sqrt (dot (sub B (ray t d)) (sub B (ray t d))) / t) *
          (Real.sqrt (dot (sub C (ray t d)) (sub C (ray t d))) / t)
        + dot (sub A (ray t d)) (sub B (ray t d)) / t ^ 2 *
            (Real.sqrt (dot (sub C (ray t d)) (sub C (ray t d))) / t)
        + dot (sub B (ray t d)) (sub C (ray t d)) / t ^ 2 *
            (Real.sqrt (dot (sub A (ray t d)) (sub A (ray t d))) / t)
        + dot (sub C (ray t d)) (sub A (ray t d)) / t ^ 2 *
            (Real.sqrt (dot (sub B (ray t d)) (sub B (ray t d))) / t))
      atTop (𝓝 (Real.sqrt (dot d d) * Real.sqrt (dot d d) * Real.sqrt (dot d d)
        + dot d d * Real.sqrt (dot d d)
        + dot d d * Real.sqrt (dot d d)
        + dot d d * Real.sqrt (dot d d))) :=
    ((h1.add h2).add h3).add h4
  have hconst : Real.sqrt (dot d d) * Real.sqrt (dot d d) * Real.sqrt (dot d d)
        + dot d d * Real.sqrt (dot d d)
        + dot d d * Real.sqrt (dot d d)
        + dot d d * Real.sqrt (dot d d)
      = 4 * Real.sqrt (dot d d) ^ 3 := by
    set s := Real.sqrt (dot d d) with hs
    have hsq : s * s = dot d d := by
      rw [← pow_two, Real.sq_sqrt (dot_self_nonneg _)]
    calc s * s * s + dot d d * s + dot d d * s + dot d d * s
        = (s * s) * s + dot d d * s + dot d d * s + dot d d * s := by ring
      _ = dot d d * s + dot d d * s + dot d d * s + dot d d * s := by rw [hsq]
      _ = 4 * s ^ 3 := by rw [← hsq]; ring
  rw [hconst] at hsum
  exact hsum.congr' heq.symm

/-- The denominator is eventually positive (`4|d|³ > 0`). -/
theorem denOf_pos_eventually (A B C d : V3) (hd : 0 < dot d d) :
    ∀ᶠ t : ℝ in atTop, 0 < denOf A B C d t := by
  have hcon := denOf_div_tendsto A B C d
  have hpos : (0:ℝ) < 4 * Real.sqrt (dot d d) ^ 3 := by
    have hs : 0 < Real.sqrt (dot d d) := Real.sqrt_pos_of_pos hd
    positivity
  have h5 : ∀ᶠ t : ℝ in atTop, 0 < denOf A B C d t / t ^ 3 :=
    Filter.Tendsto.eventually_const_lt hpos hcon
  filter_upwards [h5, eventually_gt_atTop (0 : ℝ)] with t ht5 ht0
  have ht3 : 0 < t ^ 3 := pow_pos ht0 3
  rcases div_pos_iff.mp ht5 with h | h
  · exact h.1
  · exact absurd h.2 (not_lt.mpr ht3.le)

/-! ### The inverse-of-a-nonzero-limit lemma and `t³/denOf → 1/(4|d|³)` -/

/-- If `f x → L` with `L > 0`, then `f x⁻¹ → L⁻¹` (epsilon argument; avoids
    needing a general continuity-of-inverse lemma). -/
theorem tendsto_inv_nhds_of_pos {α : Type*} {l : Filter α} {f : α → ℝ} {L : ℝ}
    (hf : Tendsto f l (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 L⁻¹) := by
  have hL2 : 0 < L / 2 := by linarith
  have h2 : ∀ᶠ x in l, L / 2 < f x :=
    hf.eventually (Ioi_mem_nhds (by linarith))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hdl : ∀ᶠ x in l, |f x - L| < ε * L ^ 2 / 2 := by
    have hu2 : 0 < ε * L ^ 2 / 2 := by positivity
    have h_up' : ∀ᶠ x in l, f x < L + ε * L ^ 2 / 2 :=
      hf.eventually (Iio_mem_nhds (by linarith))
    have h_dn' : ∀ᶠ x in l, L - ε * L ^ 2 / 2 < f x :=
      hf.eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [h_up', h_dn'] with x hxu hxd
    rw [abs_sub_comm, abs_lt]
    exact ⟨by linarith, by linarith⟩
  filter_upwards [h2, hdl] with x h2x hdlx
  have hfpos : 0 < f x := lt_of_lt_of_le hL2 h2x.le
  have e1 : (f x)⁻¹ - L⁻¹ = (L - f x) / (f x * L) := by
    field_simp
  have hd2 : dist ((f x)⁻¹) L⁻¹ = |(f x)⁻¹ - L⁻¹| := Real.dist_eq _ _
  rw [hd2, e1, abs_div, abs_of_pos (mul_pos hfpos hL)]
  have h3 : |L - f x| < ε * L ^ 2 / 2 := by
    rw [abs_sub_comm]
    exact hdlx
  have h4 : f x * L ≥ L / 2 * L := mul_le_mul_of_nonneg_right h2x.le (le_of_lt hL)
  have h5 : 0 < L / 2 * L := by positivity
  have hfxL : L / 2 * L ≤ f x * L := mul_le_mul_of_nonneg_right h2x.le (le_of_lt hL)
  calc |L - f x| / (f x * L)
      ≤ |L - f x| / (L / 2 * L) := div_le_div_of_nonneg_left (abs_nonneg _) h5 hfxL
    _ < (ε * L ^ 2 / 2) / (L / 2 * L) := div_lt_div_of_pos_right h3 h5
    _ = ε := by field_simp

/-- `t³ / denOf → 1 / (4 |d|³)` along the ray. -/
theorem t3_inv_denOf_tendsto (A B C d : V3) (hd : 0 < dot d d) :
    Tendsto (fun t : ℝ => t ^ 3 / denOf A B C d t) atTop
      (𝓝 (1 / (4 * Real.sqrt (dot d d) ^ 3))) := by
  have hcon := denOf_div_tendsto A B C d
  have hpos : (0:ℝ) < 4 * Real.sqrt (dot d d) ^ 3 := by
    have hs : 0 < Real.sqrt (dot d d) := Real.sqrt_pos_of_pos hd
    positivity
  have h5 : ∀ᶠ t : ℝ in atTop, 0 < denOf A B C d t / t ^ 3 :=
    Filter.Tendsto.eventually_const_lt hpos hcon
  have hne : ∀ᶠ t : ℝ in atTop, denOf A B C d t ≠ 0 := by
    filter_upwards [h5, eventually_gt_atTop (0:ℝ)] with t ht ht0
    have ht3 : 0 < t ^ 3 := pow_pos ht0 3
    rcases div_pos_iff.mp ht with h | h
    · exact ne_of_gt h.1
    · exact absurd h.2 (not_lt.mpr ht3.le)
  have h9 : Tendsto (fun t : ℝ => (denOf A B C d t / t ^ 3)⁻¹) atTop
      (𝓝 (4 * Real.sqrt (dot d d) ^ 3)⁻¹) :=
    tendsto_inv_nhds_of_pos hcon hpos
  have heq : (fun t : ℝ => t ^ 3 / denOf A B C d t) =ᶠ[atTop]
      fun t : ℝ => (denOf A B C d t / t ^ 3)⁻¹ := by
    filter_upwards [hne] with t ht
    field_simp
  have h1 : Tendsto (fun t : ℝ => (denOf A B C d t / t ^ 3)⁻¹) atTop
      (𝓝 (1 / (4 * Real.sqrt (dot d d) ^ 3))) := by
    have hinv : (4 * Real.sqrt (dot d d) ^ 3)⁻¹ = 1 / (4 * Real.sqrt (dot d d) ^ 3) := (one_div _).symm
    rw [← hinv]
    exact h9
  exact h1.congr' heq.symm

/-! ### `numOf / denOf → 0` -/

theorem numOf_div_tendsto (A B C d : V3) :
    Tendsto (fun t : ℝ => triNum A B C (ray t d) / t)
      atTop (𝓝 (triNum A B C (ray 1 d) - triNum A B C (ray 0 d))) := by
  have heq : (fun t : ℝ => triNum A B C (ray t d) / t) =ᶠ[atTop]
      fun t => triNum A B C (ray 1 d) - triNum A B C (ray 0 d) + triNum A B C (ray 0 d) / t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [triNum_affine]
    field_simp
  have h3 : Tendsto (fun t : ℝ => triNum A B C (ray 1 d) - triNum A B C (ray 0 d)) atTop
      (𝓝 (triNum A B C (ray 1 d) - triNum A B C (ray 0 d))) := tendsto_const_nhds
  simpa using (h3.add (tendsto_const_div_atTop (triNum A B C (ray 0 d)))).congr' heq.symm

theorem denOf_div_sq_atTop (A B C d : V3) (hd : 0 < dot d d) :
    Tendsto (fun t : ℝ => denOf A B C d t / t ^ 2) atTop atTop := by
  have hcon := denOf_div_tendsto A B C d
  have hpos : (0:ℝ) < 4 * Real.sqrt (dot d d) ^ 3 := by
    have hs : 0 < Real.sqrt (dot d d) := Real.sqrt_pos_of_pos hd
    positivity
  have h2 : ∀ᶠ t : ℝ in atTop, 2 * Real.sqrt (dot d d) ^ 3 ≤ denOf A B C d t / t ^ 3 := by
    have hlt : 2 * Real.sqrt (dot d d) ^ 3 < 4 * Real.sqrt (dot d d) ^ 3 := by
      have hs := Real.sqrt_pos_of_pos hd
      have h3 : 0 < Real.sqrt (dot d d) ^ 3 := pow_pos hs 3
      linarith
    exact hcon.eventually_const_le hlt
  have hpos2 : (0:ℝ) < 2 * Real.sqrt (dot d d) ^ 3 := by
    have hs : 0 < Real.sqrt (dot d d) := Real.sqrt_pos_of_pos hd
    positivity
  have hg : Tendsto (fun t : ℝ => t * (2 * Real.sqrt (dot d d) ^ 3)) atTop atTop :=
    Tendsto.atTop_mul_const hpos2 tendsto_id
  refine tendsto_atTop_mono' atTop ?_ hg
  filter_upwards [h2, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  have ht2 : (0:ℝ) < t ^ 2 := pow_pos ht0 2
  have ht3 : (0:ℝ) < t ^ 3 := pow_pos ht0 3
  rw [le_div_iff₀ ht2]
  rw [le_div_iff₀ ht3] at ht
  have h6 : t * (2 * Real.sqrt (dot d d) ^ 3) * t ^ 2
      = (2 * Real.sqrt (dot d d) ^ 3) * t ^ 3 := by ring
  rw [h6]
  exact ht

theorem numOf_div_denOf_tendsto_zero (A B C d : V3) (hd : 0 < dot d d) :
    Tendsto (fun t : ℝ => triNum A B C (ray t d) / denOf A B C d t) atTop (𝓝 0) := by
  have h3 := numOf_div_tendsto A B C d
  have h4 := denOf_div_sq_atTop A B C d hd
  set c := triNum A B C (ray 1 d) - triNum A B C (ray 0 d) with hc
  have hb : ∀ᶠ t : ℝ in atTop, c - 1 ≤ triNum A B C (ray t d) / t :=
    h3.eventually (Ici_mem_nhds (show c - 1 < c by linarith))
  have hB : ∀ᶠ t : ℝ in atTop, triNum A B C (ray t d) / t ≤ c + 1 :=
    h3.eventually (Iic_mem_nhds (show c < c + 1 by linarith))
  have hsplit : (fun t : ℝ => triNum A B C (ray t d) / denOf A B C d t)
      =ᶠ[atTop] (fun t : ℝ => ((triNum A B C (ray t d) / t) / (denOf A B C d t / t ^ 2)) / t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have ht2 : t ≠ 0 := ne_of_gt ht
    field_simp

  have h1 : Tendsto (fun t : ℝ => (triNum A B C (ray t d) / t) / (denOf A B C d t / t ^ 2))
      atTop (𝓝 0) := tendsto_bdd_div_atTop_nhds_zero hb hB h4
  have h2 : Tendsto (fun t : ℝ => ((triNum A B C (ray t d) / t) / (denOf A B C d t / t ^ 2)) / t)
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, one_div] using h1.mul (tendsto_const_div_atTop 1)
  exact h2.congr' hsplit.symm

/-! ### The dipole term's `t⁻²` limit -/

/-- `t² · faceDipole A B C (t • d) → -(T · d) / (2 |d|³)`. -/
theorem t2_faceDipole_tendsto (A B C d : V3) (hd : 0 < dot d d) :
    Tendsto (fun t : ℝ => t ^ 2 * faceDipole A B C d t)
      atTop (𝓝 (-dot (T A B C) d / (2 * (dot d d * Real.sqrt (dot d d))))) := by
  have hu := sqrtNorm_div_tendsto (centroid A B C) d
  have hnum : Tendsto (fun t : ℝ => dot (T A B C) (sub (centroid A B C) (ray t d)) / t) atTop
      (𝓝 (-dot (T A B C) d)) := by
    have heq : (fun t : ℝ => dot (T A B C) (sub (centroid A B C) (ray t d)) / t) =ᶠ[atTop]
        fun t : ℝ => dot (T A B C) (centroid A B C) / t - dot (T A B C) d := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      unfold sub T dot cross add ray
      field_simp
      ring
    have h0 := tendsto_const_div_atTop (dot (T A B C) (centroid A B C))
    simpa using (h0.sub (tendsto_const_nhds (x := dot (T A B C) d))).congr' heq.symm
  have hu3 : Tendsto (fun t : ℝ =>
        Real.sqrt (dot (sub (centroid A B C) (ray t d)) (sub (centroid A B C) (ray t d))) / t *
          (Real.sqrt (dot (sub (centroid A B C) (ray t d)) (sub (centroid A B C) (ray t d))) / t) *
          (Real.sqrt (dot (sub (centroid A B C) (ray t d)) (sub (centroid A B C) (ray t d))) / t))
      atTop (𝓝 (Real.sqrt (dot d d) * Real.sqrt (dot d d) * Real.sqrt (dot d d))) :=
    (hu.mul hu).mul hu
  have hden : Tendsto (fun t : ℝ => 2 *
        (Real.sqrt (dot (sub (centroid A B C) (ray t d)) (sub (centroid A B C) (ray t d))) / t) ^ 3)
      atTop (𝓝 (2 * (Real.sqrt (dot d d) * Real.sqrt (dot d d) * Real.sqrt (dot d d)))) := by
    have hfun : (fun t : ℝ => 2 *
          (Real.sqrt (dot (sub (centroid A B C) (ray t d)) (sub (centroid A B C) (ray t d))) / t) ^ 3)
        = (fun t : ℝ => 2 *
          ((Real.sqrt (dot (sub (centroid A B C) (ray t d)) (sub (centroid A B C) (ray t d))) / t) *
           (Real.sqrt (dot (sub (centroid A B C) (ray t d)) (sub (centroid A B C) (ray t d))) / t) *
           (Real.sqrt (dot (sub (centroid A B C) (ray t d)) (sub (centroid A B C) (ray t d))) / t))) := by
      funext t
      ring
    rw [hfun]
    exact hu3.const_mul 2
  have heq2 : (fun t : ℝ => t ^ 2 * faceDipole A B C d t) =ᶠ[atTop]
      fun t : ℝ => (dot (T A B C) (sub (centroid A B C) (ray t d)) / t)
        / (2 * (Real.sqrt (dot (sub (centroid A B C) (ray t d)) (sub (centroid A B C) (ray t d))) / t) ^ 3) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [faceDipole]
    field_simp
  have hne : 2 * (Real.sqrt (dot d d) * Real.sqrt (dot d d) * Real.sqrt (dot d d)) ≠ 0 := by
    have hs : 0 < Real.sqrt (dot d d) := Real.sqrt_pos_of_pos hd
    positivity
  have hdiv := hnum.div hden hne
  have hconst : -dot (T A B C) d / (2 * (Real.sqrt (dot d d) * Real.sqrt (dot d d) * Real.sqrt (dot d d)))
      = -dot (T A B C) d / (2 * (dot d d * Real.sqrt (dot d d))) := by
    rw [show Real.sqrt (dot d d) * Real.sqrt (dot d d) = dot d d from Real.mul_self_sqrt (dot_self_nonneg _)]
  rw [hconst] at hdiv
  exact hdiv.congr' heq2.symm

/-! ### The numerator over the denominator at order `t⁻²` -/

/-- `t² · (num/den) → -(T·d) / (4 |d|³)` (as `t → ∞`). -/
theorem t2_numOf_div_denOf_tendsto (A B C d : V3) (hd : 0 < dot d d) :
    Tendsto (fun t : ℝ => t ^ 2 * (triNum A B C (ray t d) / denOf A B C d t))
      atTop (𝓝 (-dot (T A B C) d / (4 * (dot d d * Real.sqrt (dot d d))))) := by
  have hnum := numOf_div_tendsto A B C d
  have hden := t3_inv_denOf_tendsto A B C d hd
  have hs3 : Real.sqrt (dot d d) ^ 3 = dot d d * Real.sqrt (dot d d) := by
    rw [pow_succ', Real.sq_sqrt (dot_self_nonneg _), mul_comm]
  have heq : (fun t : ℝ => t ^ 2 * (triNum A B C (ray t d) / denOf A B C d t)) =ᶠ[atTop]
      fun t : ℝ => (triNum A B C (ray t d) / t) * (t ^ 3 / denOf A B C d t) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), denOf_pos_eventually A B C d hd] with t ht ht2
    field_simp
  have h1 : Tendsto (fun t : ℝ => (triNum A B C (ray t d) / t) * (t ^ 3 / denOf A B C d t))
      atTop
      (𝓝 ((triNum A B C (ray 1 d) - triNum A B C (ray 0 d))
        * (1 / (4 * Real.sqrt (dot d d) ^ 3)))) := hnum.mul hden
  have hconst : (triNum A B C (ray 1 d) - triNum A B C (ray 0 d))
        * (1 / (4 * Real.sqrt (dot d d) ^ 3))
      = -dot (T A B C) d / (4 * (dot d d * Real.sqrt (dot d d))) := by
    rw [triNum_sub_ray, hs3]
    field_simp
  rw [hconst] at h1
  exact h1.congr' heq.symm

/-- `t² · (2·num/den) → -(T·d) / (2 |d|³)` — matching `t² · faceDipole`. -/
theorem t2_two_numOf_div_denOf_tendsto (A B C d : V3) (hd : 0 < dot d d) :
    Tendsto (fun t : ℝ => t ^ 2 * (2 * (triNum A B C (ray t d) / denOf A B C d t)))
      atTop (𝓝 (-dot (T A B C) d / (2 * (dot d d * Real.sqrt (dot d d))))) := by
  have h := t2_numOf_div_denOf_tendsto A B C d hd
  have h2 := h.const_mul 2
  have heq : (fun t : ℝ => t ^ 2 * (2 * (triNum A B C (ray t d) / denOf A B C d t)))
      = fun t : ℝ => 2 * (t ^ 2 * (triNum A B C (ray t d) / denOf A B C d t)) := by
    funext t; ring
  rw [heq]
  have hconst : 2 * (-dot (T A B C) d / (4 * (dot d d * Real.sqrt (dot d d))))
      = -dot (T A B C) d / (2 * (dot d d * Real.sqrt (dot d d))) := by
    field_simp; ring
  rw [hconst] at h2
  exact h2

/-! ### `solidAngle` in `atan` form, valid for large `t` -/

/-- The Van Oosterom–Strackee numerator equals the `triNum` scalar product. -/
theorem triple_ray_eq_triNum (A B C d : V3) (t : ℝ) :
    triple (sub A (ray t d)) (sub B (ray t d)) (sub C (ray t d))
      = triNum A B C (ray t d) := by
  rw [triple, Matrix.det_fin_three]
  simp only [cols_00, cols_01, cols_02, cols_10, cols_11, cols_12,
    cols_20, cols_21, cols_22, triNum, sub, dot, cross, ray]
  ring

/-- `solidAngle` unwraps to `2 * atan2' (triNum ...) (denOf ...)`. -/
theorem solidAngle_eq (A B C d : V3) (t : ℝ) :
    solidAngle A B C (ray t d)
      = 2 * atan2' (triNum A B C (ray t d)) (denOf A B C d t) := by
  rw [solidAngle, denOf, triple_ray_eq_triNum]

/-- With a positive denominator, `atan2'` is `arctan` of the ratio. -/
theorem solidAngle_eq_arctan_of_pos (A B C d : V3) (t : ℝ)
    (ht : 0 < denOf A B C d t) :
    solidAngle A B C (ray t d)
      = 2 * Real.arctan (triNum A B C (ray t d) / denOf A B C d t) := by
  rw [solidAngle_eq, atan2']
  simp only [ht, ite_true]

/-! ### The far-field consistency -/

/-- **Far-field consistency of the dipole estimate**: along a ray `t • d`
    with `0 < dot d d`, the solid angle and the per-face dipole agree to
    better than second order — `t² · (solidAngle - faceDipole) → 0`. Both
    have the same `t⁻²` coefficient `-(T·d)/(2|d|³)`. -/
theorem farfield_consistency (A B C d : V3) (hd : 0 < dot d d) :
    Tendsto (fun t : ℝ => t ^ 2 * (solidAngle A B C (ray t d) - faceDipole A B C d t))
      atTop (𝓝 0) := by
  set u : ℝ → ℝ := fun t => triNum A B C (ray t d) / denOf A B C d t with hu
  have hu0 : Tendsto u atTop (𝓝 0) := numOf_div_denOf_tendsto_zero A B C d hd
  have hLu : Tendsto (fun t : ℝ => t ^ 2 * u t)
      atTop (𝓝 (-dot (T A B C) d / (4 * (dot d d * Real.sqrt (dot d d))))) :=
    t2_numOf_div_denOf_tendsto A B C d hd
  have hLu' : Tendsto (fun t : ℝ => 2 * (t ^ 2 * u t))
      atTop (𝓝 (-dot (T A B C) d / (2 * (dot d d * Real.sqrt (dot d d))))) := by
    have h2 := hLu.const_mul 2
    have hconst : 2 * (-dot (T A B C) d / (4 * (dot d d * Real.sqrt (dot d d))))
        = -dot (T A B C) d / (2 * (dot d d * Real.sqrt (dot d d))) := by
      field_simp; ring
    rw [hconst] at h2
    exact h2
  -- A₁: the arc-tangent defect, squeezed by the cubic tail bound
  have hA1 : Tendsto (fun t : ℝ => t ^ 2 * (Real.arctan (u t) - u t)) atTop (𝓝 0) := by
    have hB : Tendsto (fun t : ℝ => ‖t ^ 2 * u t‖ * ‖u t‖ ^ 2 / 3) atTop (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => ‖t ^ 2 * u t‖) atTop
          (𝓝 ‖-dot (T A B C) d / (4 * (dot d d * Real.sqrt (dot d d)))‖) := hLu.norm
      have h2 : Tendsto (fun t : ℝ => ‖u t‖ ^ 2) atTop (𝓝 0) := by
        have := hu0.norm
        simpa using this.pow 2
      simpa using (h1.mul h2).div_const 3
    have hclose : ∀ᶠ t : ℝ in atTop,
        ‖t ^ 2 * (Real.arctan (u t) - u t)‖ ≤ ‖t ^ 2 * u t‖ * ‖u t‖ ^ 2 / 3 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
      have hb := abs_atan_sub_id_le (u t)
      have hnorm : ‖t ^ 2 * (Real.arctan (u t) - u t)‖
          = t ^ 2 * |Real.arctan (u t) - u t| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht2]
      rw [hnorm]
      have h2 : t ^ 2 * |Real.arctan (u t) - u t| ≤ t ^ 2 * (|u t| ^ 3 / 3) :=
        mul_le_mul_of_nonneg_left hb ht2
      refine h2.trans_eq ?_
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht2]
      ring
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _) hclose hB)
  -- assemble: solidAngle = 2 arctan u eventually; faceDipole matches 2 t²u
  have heq : (fun t : ℝ => t ^ 2 * (solidAngle A B C (ray t d) - faceDipole A B C d t))
      =ᶠ[atTop] fun t : ℝ =>
        2 * (t ^ 2 * u t) + 2 * (t ^ 2 * (Real.arctan (u t) - u t)) - t ^ 2 * faceDipole A B C d t := by
    filter_upwards [denOf_pos_eventually A B C d hd] with t ht
    rw [solidAngle_eq_arctan_of_pos A B C d t ht]
    simp only [hu]
    ring
  have hsum := (hLu'.add (hA1.const_mul 2)).sub (t2_faceDipole_tendsto A B C d hd)
  have hconst : -dot (T A B C) d / (2 * (dot d d * Real.sqrt (dot d d))) + 2 * 0
        - -dot (T A B C) d / (2 * (dot d d * Real.sqrt (dot d d))) = 0 := by
    ring
  rw [hconst] at hsum
  exact hsum.congr' heq.symm

end Vdb
