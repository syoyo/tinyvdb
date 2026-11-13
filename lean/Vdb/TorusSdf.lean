/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  The exact signed distance field of a torus, matching the marching-cubes and
  mesh-to-volume machinery: `sdfTorus R r p = sqrt ((sqrt (x^2 + z^2) - R)^2 + y^2) - r`
  for `R > r > 0`. The module proves:

  * `sdfTorus_zero_iff`, `sdfTorus_neg_iff`, `sdfTorus_pos_iff` — the zero set
    is the torus surface and the sign is the exact inside/outside test;
  * `dist_to_circle` — distance to a circle in ℝ² is `|dist x c - r|`;
  * `dist_to_torus` — distance to the torus surface equals `|sdfTorus R r p|`;
  * `sdfTorus_isSDF` — the field is 1-Lipschitz (an exact distance field).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Vdb.LevelSet

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

/-- Applying a subtraction is subtraction of the components. -/
@[simp] theorem ofLp_sub {n : Nat} (x y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (x - y) i = x i - y i := rfl

/-- Applying the `EuclideanSpace` equivalence's inverse. -/
@[simp] theorem symm_apply' {n : Nat} (f : Fin n → ℝ) (i : Fin n) :
    ((EuclideanSpace.equiv (Fin n) ℝ).symm f) i = f i := rfl

/-- 2-D point on the meridian plane. -/
abbrev Mer : Type := EuclideanSpace ℝ (Fin 2)

/-- The meridian point of a 3-D point: its `(x, z)` column. -/
def mer2 (p : Point) : Mer :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then p 0 else p 2)

@[simp] theorem mer2_apply (p : Point) (i : Fin 2) :
    mer2 p i = if i = 0 then p 0 else p 2 := rfl
@[simp] theorem mer2_zero (p : Point) :
    mer2 p 0 = p 0 := rfl
@[simp] theorem mer2_one (p : Point) : mer2 p 1 = p 2 := rfl

theorem mer2_norm_sq (p : Point) : ‖mer2 p‖ ^ 2 = (p 0) ^ 2 + (p 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- The circle of radius `r` around `c` in the meridian plane. -/
abbrev circle (c : Mer) (r : ℝ) : Set Mer := Metric.sphere c r

theorem mem_circle {c : Mer} {r : ℝ} {q : Mer} :
    q ∈ circle c r ↔ dist q c = r := by
  simp [circle]; rw [dist_eq_norm]

theorem circle_nonempty (c : Mer) {r : ℝ} (hr : 0 < r) :
    (circle c r).Nonempty := by
  have he : ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then (1 : ℝ) else 0)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : (fun i => if i = 0 then (1 : ℝ) else 0) = ![1, 0] := by
      ext i; fin_cases i <;> rfl
    rw [this]
    simp [Fin.sum_univ_two]
  refine ⟨c + r • (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then (1 : ℝ) else 0),
    mem_circle.mpr ?_⟩
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
    Real.norm_of_nonneg hr.le]

/-- Distance to a circle equals `|dist x c - r|` — the attaining point is the
    point of the circle on the ray from `c` through `x`. -/
theorem dist_to_circle (c : Mer) {r : ℝ} (hr : 0 < r) (x : Mer) :
    Metric.infDist x (circle c r) = |dist x c - r| := by
  have hne := circle_nonempty c hr
  apply le_antisymm
  · by_cases hx : x = c
    · rw [hx]
      have he : ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then (1 : ℝ) else 0)‖ = 1 := by
        rw [EuclideanSpace.norm_eq]
        have h : (fun i => if i = 0 then (1 : ℝ) else 0) = ![1, 0] := by
          ext i; fin_cases i <;> rfl
        rw [h]
        simp [Fin.sum_univ_two]
      have hq : c + r • (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun i => if i = 0 then (1 : ℝ) else 0) ∈ circle c r := by
        rw [mem_circle, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
          Real.norm_of_nonneg hr.le]
      calc Metric.infDist c (circle c r) ≤ dist c (c + r • _) := Metric.infDist_le_dist_of_mem hq
        _ = r := by rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
            Real.norm_of_nonneg hr.le]
        _ = |dist c c - r| := by rw [dist_self, zero_sub, abs_neg, abs_of_nonneg hr.le]
    · have hd : 0 < dist x c := by
        rw [dist_eq_norm]
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hx)
      let q : Mer := c + (r / dist x c) • (x - c)
      have hq : q ∈ circle c r := by
        rw [mem_circle]
        show ‖q - c‖ = r
        show ‖(c + (r / dist x c) • (x - c)) - c‖ = r
        rw [add_sub_cancel_left, norm_smul]
        have hn : ‖x - c‖ = dist x c := (dist_eq_norm x c).symm
        rw [hn, Real.norm_of_nonneg (div_nonneg hr.le dist_nonneg), div_mul_cancel₀ _ hd.ne']
      have hxq : x - q = (1 - r / dist x c) • (x - c) := by
        show x - (c + (r / dist x c) • (x - c)) = _
        rw [sub_smul, one_smul]
        abel
      have hdist : dist x q = |dist x c - r| := by
        rw [dist_eq_norm, hxq, norm_smul]
        have hn : ‖x - c‖ = dist x c := (dist_eq_norm x c).symm
        rw [hn]
        rcases le_total (dist x c) r with hle | hgt
        · have h1 : 1 - r / dist x c ≤ 0 := by
            have h1' : 1 ≤ r / dist x c := by
              rw [one_le_div hd]; linarith
            linarith
          rw [Real.norm_of_nonpos h1, abs_of_nonpos (sub_nonpos.mpr hle)]
          field_simp [hd.ne']
        · have h1 : 0 ≤ 1 - r / dist x c := by
            have h1' : r / dist x c ≤ 1 := by
              rw [div_le_one hd]; linarith
            linarith
          rw [Real.norm_of_nonneg h1, abs_of_nonneg (sub_nonneg.mpr hgt)]
          field_simp [hd.ne']
      exact (Metric.infDist_le_dist_of_mem hq).trans_eq hdist
  · rw [Metric.le_infDist hne]
    intro y hy
    have hyd : dist y c = r := mem_circle.mp hy
    rcases le_total (dist x c) r with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      have h2 : dist y c ≤ dist y x + dist x c := dist_triangle y x c
      rw [dist_comm y x] at h2
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      have h3 : dist x c ≤ dist x y + dist y c := dist_triangle x y c
      rw [hyd] at h3
      linarith

/-- The attaining circle point for any `x`: the point of the circle on the
    ray from `c` through `x` (or an arbitrary one when `x = c`). -/
theorem circle_exists_mem_dist_eq (c : Mer) {r : ℝ} (hr : 0 < r) (x : Mer) :
    ∃ q ∈ circle c r, dist x q = |dist x c - r| := by
  by_cases hx : x = c
  · rw [hx]
    have he : ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then (1 : ℝ) else 0)‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      have h : (fun i => if i = 0 then (1 : ℝ) else 0) = ![1, 0] := by
        ext i; fin_cases i <;> rfl
      rw [h]
      simp [Fin.sum_univ_two]
    refine ⟨c + r • (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then (1 : ℝ) else 0), ?_, ?_⟩
    · rw [mem_circle, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
        Real.norm_of_nonneg hr.le]
    · rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
        Real.norm_of_nonneg hr.le, dist_self, zero_sub, abs_neg, abs_of_nonneg hr.le]
  · have hd : 0 < dist x c := by
      rw [dist_eq_norm]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    let q : Mer := c + (r / dist x c) • (x - c)
    have hq : q ∈ circle c r := by
      rw [mem_circle]
      show ‖q - c‖ = r
      show ‖(c + (r / dist x c) • (x - c)) - c‖ = r
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (div_nonneg hr.le dist_nonneg)]
      have hn : ‖x - c‖ = dist x c := (dist_eq_norm x c).symm
      rw [hn, div_mul_cancel₀ _ hd.ne']
    refine ⟨q, hq, ?_⟩
    have hxq : x - q = (1 - r / dist x c) • (x - c) := by
      show x - (c + (r / dist x c) • (x - c)) = _
      rw [sub_smul, one_smul]
      abel
    rw [dist_eq_norm, hxq, norm_smul]
    have hn : ‖x - c‖ = dist x c := (dist_eq_norm x c).symm
    rw [hn]
    rcases le_total (dist x c) r with hle | hgt
    · have h1 : 1 - r / dist x c ≤ 0 := by
        have h1' : 1 ≤ r / dist x c := by
          rw [one_le_div hd]; linarith
        linarith
      rw [Real.norm_of_nonpos h1, abs_of_nonpos (sub_nonpos.mpr hle)]
      field_simp [hd.ne']
    · have h1 : 0 ≤ 1 - r / dist x c := by
        have h1' : r / dist x c ≤ 1 := by
          rw [div_le_one hd]; linarith
        linarith
      rw [Real.norm_of_nonneg h1, abs_of_nonneg (sub_nonneg.mpr hgt)]
      field_simp [hd.ne']

/-- The meridian `(sqrt (x^2 + z^2), y)` of a 3-D point. -/
def radMap (p : Point) : Mer :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then Real.sqrt ((p 0)^2 + (p 2)^2) else p 1)

@[simp] theorem radMap_apply (p : Point) (i : Fin 2) :
    radMap p i = if i = 0 then Real.sqrt ((p 0)^2 + (p 2)^2) else p 1 := rfl
@[simp] theorem radMap_zero (p : Point) :
    radMap p 0 = Real.sqrt ((p 0)^2 + (p 2)^2) := rfl
@[simp] theorem radMap_one (p : Point) : radMap p 1 = p 1 := rfl

theorem radMap_norm_sq (p : Point) :
    ‖radMap p‖ ^ 2 = (Real.sqrt ((p 0)^2 + (p 2)^2)) ^ 2 + (p 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- The center of the meridian circle. -/
def cR (R : ℝ) : Mer := (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then R else 0)

@[simp] theorem cR_apply (R : ℝ) (i : Fin 2) :
    cR R i = if i = 0 then R else 0 := rfl
@[simp] theorem cR_zero (R : ℝ) : cR R 0 = R := rfl
@[simp] theorem cR_one (R : ℝ) : cR R 1 = 0 := rfl

theorem dist_radMap (R : ℝ) (p : Point) :
    dist (radMap p) (cR R) = Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) := by
  have h2 : dist (radMap p) (cR R) ^ 2 = (Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [cR]
  have : dist (radMap p) (cR R) = Real.sqrt ((dist (radMap p) (cR R))^2) :=
    (Real.sqrt_sq dist_nonneg).symm
  rw [this, h2]

theorem dist_radMap_sq (R : ℝ) (p : Point) :
    Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) ^ 2 =
      (Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2 :=
  Real.sq_sqrt (by positivity)

/-- The torus surface: points with `sqrt ((sqrt (x^2 + z^2) - R)^2 + y^2) = r`. -/
def torusSurface (R r : ℝ) : Set Point :=
  {p | (Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2 = r^2}

theorem mem_torusSurface {R r : ℝ} (hr : 0 < r) {q : Point} :
    q ∈ torusSurface R r ↔ dist (radMap q) (cR R) = r := by
  show ((Real.sqrt ((q 0)^2 + (q 2)^2) - R)^2 + (q 1)^2 = r^2) ↔ _
  rw [dist_radMap]
  constructor
  · intro h
    have hs : Real.sqrt ((Real.sqrt ((q 0)^2 + (q 2)^2) - R)^2 + (q 1)^2) = Real.sqrt (r^2) := by
      rw [h]
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hr.le] at hs
  · intro h
    have hs : (Real.sqrt ((Real.sqrt ((q 0)^2 + (q 2)^2) - R)^2 + (q 1)^2))^2 = r^2 := by rw [h]
    rw [Real.sq_sqrt (by positivity)] at hs
    exact hs

theorem torusSurface_nonempty {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    (torusSurface R r).Nonempty := by
  refine ⟨(EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => if i = 0 then R + r else 0), ?_⟩
  show (Real.sqrt (((EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
      if i = 0 then R + r else 0) 0)^2 + ((EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
      if i = 0 then R + r else 0) 2)^2) - R)^2 + ((EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
      if i = 0 then R + r else 0) 1)^2 = r^2
  rw [show (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
      if i = 0 then R + r else 0) 0 = R + r from rfl,
    show (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
      if i = 0 then R + r else 0) 2 = 0 from rfl,
    show (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
      if i = 0 then R + r else 0) 1 = 0 from rfl]
  have h : Real.sqrt ((R + r)^2 + (0:ℝ)^2) = R + r := by
    rw [show (R + r)^2 + (0:ℝ)^2 = (R + r)^2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ R + r)]
  rw [h]
  ring


/-- Cauchy–Schwarz on the `(x, z)` pair, in squared form. -/
theorem key_cs (a b c d : ℝ) : (a * b + c * d)^2 ≤ (a^2 + c^2) * (b^2 + d^2) := by
  nlinarith [sq_nonneg (a * d - c * b)]

/-- Cauchy–Schwarz for the projected `(x, z)` parts: the radial distance
    between two points never exceeds the 3-D distance. -/
theorem sq_radial_le (p q : Point) :
    (Real.sqrt ((p 0)^2 + (p 2)^2) - Real.sqrt ((q 0)^2 + (q 2)^2))^2 ≤
      (p 0 - q 0)^2 + (p 2 - q 2)^2 := by
  have hcs : p 0 * q 0 + p 2 * q 2 ≤
      Real.sqrt ((p 0)^2 + (p 2)^2) * Real.sqrt ((q 0)^2 + (q 2)^2) := by
    have hcs' := key_cs (p 0) (q 0) (p 2) (q 2)
    have habs : |p 0 * q 0 + p 2 * q 2| ≤
        Real.sqrt ((p 0)^2 + (p 2)^2) * Real.sqrt ((q 0)^2 + (q 2)^2) := by
      have h1 : Real.sqrt ((p 0 * q 0 + p 2 * q 2)^2) = |p 0 * q 0 + p 2 * q 2| :=
        Real.sqrt_sq_eq_abs _
      rw [← h1, ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ (p 0)^2 + (p 2)^2)]
      exact Real.sqrt_le_sqrt hcs'
    exact (le_abs_self _).trans habs
  have hsp : Real.sqrt ((p 0)^2 + (p 2)^2)^2 = (p 0)^2 + (p 2)^2 :=
    Real.sq_sqrt (by positivity)
  have hsq : Real.sqrt ((q 0)^2 + (q 2)^2)^2 = (q 0)^2 + (q 2)^2 :=
    Real.sq_sqrt (by positivity)
  rw [sub_sq, hsp, hsq]
  simp only [sub_sq']
  nlinarith [hcs]

/-- Distance contraction under the radial projection. -/
theorem dist_radMap_le (p q : Point) : dist (radMap p) (radMap q) ≤ dist p q := by
  rw [dist_eq_norm, dist_eq_norm, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq,
    Fin.sum_univ_two, Fin.sum_univ_three]
  have hge := sq_radial_le p q
  apply Real.sqrt_le_sqrt
  have h1 : (Real.sqrt ((p 0)^2 + (p 2)^2) - Real.sqrt ((q 0)^2 + (q 2)^2))^2 + (p 1 - q 1)^2 ≤
      (p 0 - q 0)^2 + (p 1 - q 1)^2 + (p 2 - q 2)^2 := by
    linarith [hge]
  simp only [Real.norm_eq_abs, sq_abs, ofLp_sub]
  exact h1

theorem dist_ge_circle {R r : ℝ} {p : Point} {q : Point} (hr : 0 < r)
    (hq : q ∈ torusSurface R r) :
    |Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) - r| ≤ dist p q := by
  have hq' : radMap q ∈ circle (cR R) r := (mem_torusSurface hr).mp hq
  calc |Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) - r|
      = |dist (radMap p) (cR R) - r| := by rw [dist_radMap]
    _ = Metric.infDist (radMap p) (circle (cR R) r) :=
        (dist_to_circle (cR R) hr (radMap p)).symm
    _ ≤ dist (radMap p) (radMap q) := Metric.infDist_le_dist_of_mem hq'
    _ ≤ dist p q := dist_radMap_le p q


/-- The torus signed distance field. -/
noncomputable def sdfTorus (R r : ℝ) (p : Point) : ℝ :=
  Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) - r

theorem sdfTorus_le_infDist (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (_hRr : r < R) (p : Point) :
    |sdfTorus R r p| ≤ Metric.infDist p (torusSurface R r) := by
  rw [Metric.le_infDist (torusSurface_nonempty hR hr)]
  intro q hq
  exact dist_ge_circle hr hq

theorem abs_sdfTorus (R r : ℝ) (p : Point) :
    |sdfTorus R r p| = |dist (radMap p) (cR R) - r| := by
  rw [sdfTorus, dist_radMap]

/-- The attaining point on the torus for any `p`. -/
theorem torusSurface_exists_mem_dist_eq (R r : ℝ) (_hR : 0 < R) (hr : 0 < r) (hRr : r < R)
    (p : Point) : ∃ q ∈ torusSurface R r, dist p q = |sdfTorus R r p| := by
  set ρ := Real.sqrt ((p 0)^2 + (p 2)^2) with hρdef
  obtain ⟨q', hq'mem, hq'd⟩ := circle_exists_mem_dist_eq (cR R) hr (radMap p)
  have hq'eq : (q' 0 - R)^2 + (q' 1)^2 = r^2 := by
    have h := mem_circle.mp hq'mem
    rw [dist_eq_norm] at h
    have hsq : ‖q' - cR R‖^2 = r^2 := by rw [h]
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at hsq
    simp [cR] at hsq
    exact hsq
  have h01 : (q' 0 - R)^2 ≤ r^2 := by nlinarith [sq_nonneg (q' 1), hq'eq]
  have habs : |q' 0 - R| ≤ r := by
    calc |q' 0 - R| = Real.sqrt ((q' 0 - R)^2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (r^2) := Real.sqrt_le_sqrt h01
      _ = r := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr.le]
  have hq0_ge : R - r ≤ q' 0 := by
    have := abs_le.mp habs
    linarith
  have hu0 : 0 < q' 0 := by linarith [hRr]
  have hρ2 : ρ^2 = (p 0)^2 + (p 2)^2 := by
    rw [hρdef, Real.sq_sqrt (by positivity)]
  by_cases hρ : ρ = 0
  · have hsum : (p 0)^2 + (p 2)^2 = 0 := (Real.sqrt_eq_zero (by positivity)).mp hρ
    have hp0 : p 0 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (p 2)])
    have hp2 : p 2 = 0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (p 0)])
    refine ⟨(EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
      if i = 0 then q' 0 else if i = 1 then q' 1 else 0), ?_, ?_⟩
    · rw [mem_torusSurface hr]
      have hqm : radMap ((EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
          if i = 0 then q' 0 else if i = 1 then q' 1 else 0)) = q' := by
        ext i
        fin_cases i
        · simp [radMap]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hu0.le]
        · simp [radMap]
      rw [hqm]
      exact mem_circle.mp hq'mem
    · have hp_rad : radMap p = (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => if i = 0 then 0 else p 1) := by
        ext i
        fin_cases i
        · show Real.sqrt ((p 0)^2 + (p 2)^2) = 0
          rw [hsum, Real.sqrt_zero]
        · rfl
      have hsq : dist p ((EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
          if i = 0 then q' 0 else if i = 1 then q' 1 else 0)) ^ 2 = dist (radMap p) q' ^ 2 := by
        rw [dist_eq_norm, dist_eq_norm, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
          Fin.sum_univ_three, Fin.sum_univ_two]
        rw [hp_rad]
        simp [hp0, hp2]
      have key : dist p ((EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
          if i = 0 then q' 0 else if i = 1 then q' 1 else 0)) = dist (radMap p) q' := by
        have h := congrArg Real.sqrt hsq
        rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq dist_nonneg] at h
      rw [key, hq'd, abs_sdfTorus]
  · refine ⟨(EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
      if i = 0 then q' 0 * (p 0 / ρ) else if i = 1 then q' 1 else q' 0 * (p 2 / ρ)), ?_, ?_⟩
    · rw [mem_torusSurface hr]
      have hqm : radMap ((EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
          if i = 0 then q' 0 * (p 0 / ρ) else if i = 1 then q' 1 else q' 0 * (p 2 / ρ))) = q' := by
        have hs : (q' 0 * (p 0 / ρ))^2 + (q' 0 * (p 2 / ρ))^2 = q' 0^2 := by
          field_simp [hρ]
          linarith [hρ2]
        ext i
        fin_cases i
        · simp [radMap, hs]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hu0.le]
        · simp [radMap]
      rw [hqm]
      exact mem_circle.mp hq'mem
    · have e1 : p 0 - q' 0 * (p 0 / ρ) = ((ρ - q' 0) / ρ) * p 0 := by
        field_simp [hρ]
      have e2 : p 2 - q' 0 * (p 2 / ρ) = ((ρ - q' 0) / ρ) * p 2 := by
        field_simp [hρ]
      have sum_eq : (p 0 - q' 0 * (p 0 / ρ))^2 + (p 1 - q' 1)^2 + (p 2 - q' 0 * (p 2 / ρ))^2 =
          (ρ - q' 0)^2 + (p 1 - q' 1)^2 := by
        rw [e1, e2, mul_pow, mul_pow]
        have hs : ((ρ - q' 0) / ρ)^2 * ((p 0)^2 + (p 2)^2) = (ρ - q' 0)^2 := by
          rw [← hρ2, div_pow]
          field_simp [pow_ne_zero 2 hρ]
        calc ((ρ - q' 0) / ρ)^2 * (p 0)^2 + (p 1 - q' 1)^2 + ((ρ - q' 0) / ρ)^2 * (p 2)^2
            = ((ρ - q' 0) / ρ)^2 * ((p 0)^2 + (p 2)^2) + (p 1 - q' 1)^2 := by ring
          _ = (ρ - q' 0)^2 + (p 1 - q' 1)^2 := by rw [hs]
      have hsq : dist p ((EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
          if i = 0 then q' 0 * (p 0 / ρ) else if i = 1 then q' 1 else q' 0 * (p 2 / ρ))) ^ 2 =
          dist (radMap p) q' ^ 2 := by
        rw [dist_eq_norm, dist_eq_norm, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
          Fin.sum_univ_three, Fin.sum_univ_two]
        simp
        rw [← hρdef, sum_eq]
      have key : dist p ((EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i =>
          if i = 0 then q' 0 * (p 0 / ρ) else if i = 1 then q' 1 else q' 0 * (p 2 / ρ))) =
          dist (radMap p) q' := by
        have h := congrArg Real.sqrt hsq
        rwa [Real.sqrt_sq dist_nonneg, Real.sqrt_sq dist_nonneg] at h
      rw [key, hq'd, abs_sdfTorus]


theorem dist_to_torus (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hRr : r < R) (p : Point) :
    Metric.infDist p (torusSurface R r) = |sdfTorus R r p| := by
  apply le_antisymm
  · obtain ⟨q, hqmem, hqdist⟩ := torusSurface_exists_mem_dist_eq R r hR hr hRr p
    rw [← hqdist]
    exact Metric.infDist_le_dist_of_mem hqmem
  · exact sdfTorus_le_infDist R r hR hr hRr p

/-- Zero set of the torus field is the torus surface. -/
theorem sdfTorus_zero_iff (R r : ℝ) (hr : 0 < r) (p : Point) :
    sdfTorus R r p = 0 ↔ (Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2 = r^2 := by
  unfold sdfTorus
  constructor
  · intro h
    have hs : Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) = r := by
      linarith [h]
    have := congrArg (fun t => t ^ 2) hs
    rwa [Real.sq_sqrt (by positivity)] at this
  · intro h
    have hs : Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) = Real.sqrt (r^2) := by
      rw [h]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr.le] at hs
    linarith [hs]

/-- The sign is exact: negative exactly inside the torus. -/
theorem sdfTorus_neg_iff (R r : ℝ) (hr : 0 < r) (p : Point) :
    sdfTorus R r p < 0 ↔ (Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2 < r^2 := by
  unfold sdfTorus
  have hsqrt_lt : ∀ a : ℝ, 0 ≤ a → (Real.sqrt a < r ↔ a < r^2) := by
    intro a ha
    constructor
    · intro h1
      have h2 : (Real.sqrt a)^2 = a := Real.sq_sqrt ha
      nlinarith [Real.sqrt_nonneg a]
    · intro h1
      have h2 := Real.sqrt_le_sqrt (le_of_lt h1)
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr.le] at h2
      rcases h2.eq_or_lt with h3 | h4
      · exfalso
        rw [← h3] at h1
        rw [Real.sq_sqrt ha] at h1
        linarith
      · exact h4
  rw [show (Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) - r) < 0 ↔
      Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) < r from by
    constructor <;> intro h <;> linarith [h]]
  exact hsqrt_lt _ (by positivity)

/-- Positive exactly outside. -/
theorem sdfTorus_pos_iff (R r : ℝ) (hr : 0 < r) (p : Point) :
    0 < sdfTorus R r p ↔ r^2 < (Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2 := by
  unfold sdfTorus
  have hsqrt_le : ∀ a : ℝ, 0 ≤ a → (r^2 < a ↔ r < Real.sqrt a) := by
    intro a ha
    constructor
    · intro h1
      have h2 : Real.sqrt (r^2) < Real.sqrt a := Real.sqrt_lt_sqrt (sq_nonneg r) h1
      rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg hr.le] at h2
    · intro h1
      have h2 : r^2 < (Real.sqrt a)^2 := by
        have h3 := Real.sq_sqrt ha
        nlinarith [Real.sqrt_nonneg a]
      rwa [Real.sq_sqrt ha] at h2
  rw [show (0 < Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) - r) ↔
      r < Real.sqrt ((Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2) from by
    constructor <;> intro h <;> linarith [h]]
  exact (hsqrt_le _ (by positivity)).symm

/-- The torus SDF is the negative distance inside. -/
theorem sdfTorus_dist_sign (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hRr : r < R) (p : Point)
    (hin : (Real.sqrt ((p 0)^2 + (p 2)^2) - R)^2 + (p 1)^2 < r^2) :
    sdfTorus R r p = -Metric.infDist p (torusSurface R r) := by
  have h := dist_to_torus R r hR hr hRr p
  have hs : sdfTorus R r p < 0 := (sdfTorus_neg_iff R r hr p).mpr hin
  rw [h, abs_of_nonpos hs.le, neg_neg]


theorem sdfTorus_isSDF (R r : ℝ) (hR : 0 < R) (hr : 0 < r) (hRr : r < R) :
    IsSDF (sdfTorus R r) := by
  intro p q
  have hT := dist_to_torus R r hR hr hRr
  rcases le_total (sdfTorus R r p) 0 with hp | hp
  · rcases le_total (sdfTorus R r q) 0 with hq | hq
    · -- both ≤ 0: f = −infDist
      have hp' : sdfTorus R r p = -Metric.infDist p (torusSurface R r) := by
        rw [hT p, abs_of_nonpos hp, neg_neg]
      have hq' : sdfTorus R r q = -Metric.infDist q (torusSurface R r) := by
        rw [hT q, abs_of_nonpos hq, neg_neg]
      rw [hp', hq']
      have e1 : Metric.infDist p (torusSurface R r) - Metric.infDist q (torusSurface R r) ≤ dist p q := by
        have h := Metric.infDist_le_infDist_add_dist (x := p) (y := q) (s := torusSurface R r)
        linarith [h]
      have e2 : Metric.infDist q (torusSurface R r) - Metric.infDist p (torusSurface R r) ≤ dist p q := by
        have h := Metric.infDist_le_infDist_add_dist (x := q) (y := p) (s := torusSurface R r)
        rw [dist_comm] at h
        linarith [h]
      rw [abs_sub_comm, abs_le]
      constructor <;> linarith [e1, e2]
    · -- p ≤ 0 < q
      have hq' : sdfTorus R r q = Metric.infDist q (torusSurface R r) := by
        have habs : |sdfTorus R r q| = sdfTorus R r q := abs_of_nonneg (by linarith [hq])
        rw [hT q, habs]
      have hp' : sdfTorus R r p = -Metric.infDist p (torusSurface R r) := by
        rw [hT p, abs_of_nonpos hp, neg_neg]
      rw [hp', hq']
      have hgt : Continuous (sdfTorus R r) := by
        unfold sdfTorus
        fun_prop
      have hg : ContinuousOn (fun (t : ℝ) => sdfTorus R r (p + t • (q - p))) (Set.Icc 0 1) := by
        exact (hgt.comp (by fun_prop : Continuous (fun t => p + t • (q - p)))).continuousOn
      have hcross := intermediate_value_Icc (a := 0) (b := 1) (f := fun (t : ℝ) => sdfTorus R r (p + t • (q - p)))
        (show (0:ℝ) ≤ 1 by norm_num) hg
      have hm : ∃ m ∈ Set.Icc (0:ℝ) 1, sdfTorus R r (p + m • (q - p)) = 0 := by
        have h0 : sdfTorus R r (p + (0:ℝ) • (q - p)) = sdfTorus R r p := by simp
        have h1 : sdfTorus R r (p + (1:ℝ) • (q - p)) = sdfTorus R r q := by simp
        rw [h0, h1] at hcross
        have : (0:ℝ) ∈ Set.Icc (sdfTorus R r p) (sdfTorus R r q) := by
          rw [Set.mem_Icc]; constructor <;> linarith [hq, hp]
        obtain ⟨t, ht, ht'⟩ := hcross this
        exact ⟨t, ht, ht'⟩
      obtain ⟨t, ht, ht'⟩ := hm
      have hmT : p + t • (q - p) ∈ torusSurface R r := by
        exact (sdfTorus_zero_iff R r hr _).mp ht'
      have key1 : Metric.infDist p (torusSurface R r) ≤ dist p (p + t • (q - p)) :=
        Metric.infDist_le_dist_of_mem hmT
      have key2 : Metric.infDist q (torusSurface R r) ≤ dist q (p + t • (q - p)) :=
        Metric.infDist_le_dist_of_mem hmT
      have hsum : dist p q = dist p (p + t • (q - p)) + dist (p + t • (q - p)) q := by
        have h1 : dist (p + t • (q - p)) q = (1 - t) * dist p q := by
          rw [dist_eq_norm, dist_eq_norm]
          have this : (p + t • (q - p)) - q = (1 - t) • (p - q) := by module
          rw [this, norm_smul, Real.norm_of_nonneg (by linarith [ht.2])]
        have h2 : dist p (p + t • (q - p)) = t * dist p q := by
          rw [dist_eq_norm, dist_eq_norm]
          have this : (p + t • (q - p)) - p = t • (q - p) := by module
          rw [norm_sub_rev, this, norm_smul, Real.norm_of_nonneg (by linarith [ht.1]), norm_sub_rev]
        rw [h1, h2]
        ring
      have habs2 : |(-Metric.infDist p (torusSurface R r)) - Metric.infDist q (torusSurface R r)| =
          Metric.infDist p (torusSurface R r) + Metric.infDist q (torusSurface R r) := by
        rw [abs_of_nonpos (by linarith [Metric.infDist_nonneg (x := p) (s := torusSurface R r), Metric.infDist_nonneg (x := q) (s := torusSurface R r)])]
        ring
      rw [habs2]
      calc Metric.infDist p (torusSurface R r) + Metric.infDist q (torusSurface R r)
          ≤ dist p (p + t • (q - p)) + dist (p + t • (q - p)) q := by
            linarith [key1, key2, dist_comm q (p + t • (q - p))]
        _ = dist p q := hsum.symm
  · rcases le_total (sdfTorus R r q) 0 with hq | hq
    · -- p > 0 ≥ q: symmetric to the previous case
      have hp' : sdfTorus R r p = Metric.infDist p (torusSurface R r) := by
        have habs : |sdfTorus R r p| = sdfTorus R r p := abs_of_nonneg (by linarith [hp])
        rw [hT p, habs]
      have hq' : sdfTorus R r q = -Metric.infDist q (torusSurface R r) := by
        rw [hT q, abs_of_nonpos hq, neg_neg]
      rw [hp', hq']
      have hgt : Continuous (sdfTorus R r) := by
        unfold sdfTorus
        fun_prop
      have hg : ContinuousOn (fun (t : ℝ) => sdfTorus R r (p + t • (q - p))) (Set.Icc 0 1) := by
        exact (hgt.comp (by fun_prop : Continuous (fun t => p + t • (q - p)))).continuousOn
      have hcross := intermediate_value_Icc' (a := 0) (b := 1) (f := fun (t : ℝ) => sdfTorus R r (p + t • (q - p)))
        (show (0:ℝ) ≤ 1 by norm_num) hg
      have h0 : sdfTorus R r (p + (0:ℝ) • (q - p)) = sdfTorus R r p := by simp
      have h1 : sdfTorus R r (p + (1:ℝ) • (q - p)) = sdfTorus R r q := by simp
      rw [h0, h1] at hcross
      have hm : ∃ m ∈ Set.Icc (0:ℝ) 1, sdfTorus R r (p + m • (q - p)) = 0 := by
        have : (0:ℝ) ∈ Set.Icc (sdfTorus R r q) (sdfTorus R r p) := by
          rw [Set.mem_Icc]; constructor <;> linarith [hp, hq]
        obtain ⟨t, ht, ht'⟩ := hcross this
        exact ⟨t, ht, ht'⟩
      obtain ⟨t, ht, ht'⟩ := hm
      have hmT : p + t • (q - p) ∈ torusSurface R r := by
        exact (sdfTorus_zero_iff R r hr _).mp ht'
      have key1 : Metric.infDist p (torusSurface R r) ≤ dist p (p + t • (q - p)) :=
        Metric.infDist_le_dist_of_mem hmT
      have key2 : Metric.infDist q (torusSurface R r) ≤ dist q (p + t • (q - p)) :=
        Metric.infDist_le_dist_of_mem hmT
      have hsum : dist p q = dist p (p + t • (q - p)) + dist (p + t • (q - p)) q := by
        have h1 : dist (p + t • (q - p)) q = (1 - t) * dist p q := by
          rw [dist_eq_norm, dist_eq_norm]
          have this : (p + t • (q - p)) - q = (1 - t) • (p - q) := by module
          rw [this, norm_smul, Real.norm_of_nonneg (by linarith [ht.2])]
        have h2 : dist p (p + t • (q - p)) = t * dist p q := by
          rw [dist_eq_norm, dist_eq_norm]
          have this : (p + t • (q - p)) - p = t • (q - p) := by module
          rw [norm_sub_rev, this, norm_smul, Real.norm_of_nonneg (by linarith [ht.1]), norm_sub_rev]
        rw [h1, h2]
        ring
      rw [abs_sub_comm]
      have habs2 : |(-Metric.infDist q (torusSurface R r)) - Metric.infDist p (torusSurface R r)| =
          Metric.infDist q (torusSurface R r) + Metric.infDist p (torusSurface R r) := by
        rw [abs_of_nonpos (by linarith [Metric.infDist_nonneg (x := q) (s := torusSurface R r), Metric.infDist_nonneg (x := p) (s := torusSurface R r)])]
        ring
      rw [habs2]
      calc Metric.infDist q (torusSurface R r) + Metric.infDist p (torusSurface R r)
          ≤ dist q (p + t • (q - p)) + dist p (p + t • (q - p)) := by
            linarith [key1, key2, dist_comm p (p + t • (q - p))]
        _ = dist p q := by
          rw [dist_comm q (p + t • (q - p)), add_comm]
          exact hsum.symm
    · -- both > 0: f = +infDist
      have hp' : sdfTorus R r p = Metric.infDist p (torusSurface R r) := by
        have habs : |sdfTorus R r p| = sdfTorus R r p := abs_of_nonneg (by linarith [hp])
        rw [hT p, habs]
      have hq' : sdfTorus R r q = Metric.infDist q (torusSurface R r) := by
        have habs : |sdfTorus R r q| = sdfTorus R r q := abs_of_nonneg (by linarith [hq])
        rw [hT q, habs]
      rw [hp', hq']
      have e1 : Metric.infDist p (torusSurface R r) - Metric.infDist q (torusSurface R r) ≤ dist p q := by
        have h := Metric.infDist_le_infDist_add_dist (x := p) (y := q) (s := torusSurface R r)
        linarith [h]
      have e2 : Metric.infDist q (torusSurface R r) - Metric.infDist p (torusSurface R r) ≤ dist p q := by
        have h := Metric.infDist_le_infDist_add_dist (x := q) (y := p) (s := torusSurface R r)
        rw [dist_comm] at h
        linarith [h]
      rw [abs_sub_comm, abs_le]
      constructor <;> linarith [e1, e2]

end Vdb
