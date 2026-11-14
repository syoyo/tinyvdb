/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Barnes–Hut dipole far field (`src/tinyvdb_winding.c`), modelled over ℝ:
  the C AABB-tree far-field approximates a distant triangle cluster by the
  *dipole* — `dot (centroid − p) (Σ area-weighted normals) / |centroid − p|³`
  — rather than summing per-face solid angles. The field of a single
  triangle seen from `p` decomposes exactly into its dipole term plus an
  O(ε³) residual sitting on the vertices:

      a·(b×c) = r · T + a'·(b'×c')

  with `r = centroid − p`, `T = A×B + B×C + C×A` (twice the area-weighted
  normal), `a'/b'/c'` the vertex deviations from the centroid. The residual
  — which the C's dipole term discards — is bounded exactly by
  `|a'·(b'×c')| ≤ ε³` when the vertices sit within `ε` of their centroid
  (`ε²` bounds each squared length). `cluster_triNum_eq` lifts the identity
  to lists of triangles, and `cluster_triNum_residual_bound` bounds the
  total residual by `Σ ε_f³`.

  What is *not* proved: that the residual is the *optimal* approximation
  constant (it is not — the exact constant depends on the query direction),
  or the arc-tangent tail (`|atan x − x| ≤ |x|³/3` machinery is deliberately
  out of scope). The `atan2'` solid-angle machinery lives in
  `Vdb/WindingNumber.lean`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.WindingNumber
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

namespace Vdb
namespace V3

/-- Cross product, explicit. -/
def cross (a b : V3) : V3 := ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

/-- Dot with self is non-negative. -/
theorem dot_self_nonneg (a : V3) : 0 ≤ dot a a := by
  unfold dot
  nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]

/-- Left-distributivity over addition. -/
theorem cross_add_left (a b c : V3) : cross (add a b) c = add (cross a c) (cross b c) := by
  apply V3.ext <;> simp [cross, add] <;> ring

/-- Right-distributivity over addition. -/
theorem cross_add_right (a b c : V3) : cross a (add b c) = add (cross a b) (cross a c) := by
  apply V3.ext <;> simp [cross, add] <;> ring

/-- Distribution over subtraction, left. -/
theorem cross_sub_left (a b c : V3) : cross (sub a b) c = sub (cross a c) (cross b c) := by
  apply V3.ext <;> simp [cross, sub] <;> ring

/-- Distribution over subtraction, right. -/
theorem cross_sub_right (a b c : V3) : cross a (sub b c) = sub (cross a b) (cross a c) := by
  apply V3.ext <;> simp [cross, sub] <;> ring

theorem cross_self (a : V3) : cross a a = ⟨0, 0, 0⟩ := by
  apply V3.ext <;> simp [cross] <;> ring

theorem dot_self_cross_left (a c : V3) : dot a (cross a c) = 0 := by
  unfold dot cross
  ring

theorem dot_self_cross_right (a b : V3) : dot a (cross b a) = 0 := by
  unfold dot cross
  ring

/-- Lagrange's identity: `(|a|²)(|b|²) − (a·b)² = |a×b|²`. -/
theorem lagrange (a b : V3) :
    dot a a * dot b b - dot a b * dot a b = dot (cross a b) (cross a b) := by
  simp only [dot, cross]; ring

/-- Square sizes are non-negative sums; norm bound via the sqrt of the dot. -/
noncomputable def norm (a : V3) : ℝ := Real.sqrt (dot a a)

/-- Cauchy–Schwarz for `V3` (via Lagrange). -/
theorem dot_abs_le (a b : V3) : |dot a b| ≤ norm a * norm b := by
  have hprod : dot a b * dot a b ≤ dot a a * dot b b := by
    have h := lagrange a b
    have hnn := dot_self_nonneg (cross a b)
    linarith
  have h : Real.sqrt (dot a b * dot a b) ≤ Real.sqrt (dot a a * dot b b) :=
    Real.sqrt_le_sqrt hprod
  have h1 : Real.sqrt (dot a b * dot a b) = |dot a b| := by
    rw [show dot a b * dot a b = dot a b ^ 2 from (pow_two (dot a b)).symm]
    exact Real.sqrt_sq_eq_abs _
  have h2 : Real.sqrt (dot a a * dot b b) = norm a * norm b := by
    rw [norm, norm, Real.sqrt_mul (dot_self_nonneg _) _]
  rwa [h1, h2] at h

theorem norm_nonneg (a : V3) : 0 ≤ norm a := Real.sqrt_nonneg _

theorem norm_sq (a : V3) : norm a * norm a = dot a a := by
  unfold norm
  exact Real.mul_self_sqrt (dot_self_nonneg _)

/-- The `|a×b|` factor: `|a×b| ≤ |a|·|b|`. -/
theorem cross_norm_le (a b : V3) : dot (cross a b) (cross a b) ≤ dot a a * dot b b := by
  have h := lagrange a b
  have hnn := sq_nonneg (dot a b)
  linarith [sq_nonneg (dot a b)]

/-- The triple `a'·(b'×c')` bound: vertex deviations bounded by `ε²` in
    squared length give a residual `≤ ε³`. -/
theorem tri_residual_abs_le {a b c : V3} {ε : ℝ}
    (ha : dot a a ≤ ε ^ 2) (hb : dot b b ≤ ε ^ 2) (hc : dot c c ≤ ε ^ 2) (hε : 0 ≤ ε) :
    |dot a (cross b c)| ≤ ε ^ 3 := by
  have h1 : |dot a (cross b c)| ≤ norm a * norm (cross b c) := dot_abs_le a (cross b c)
  have h2 : dot (cross b c) (cross b c) ≤ dot b b * dot c c := cross_norm_le b c
  have h3 : norm (cross b c) ≤ norm b * norm c := by
    rw [norm, norm, norm]
    have hnn : 0 ≤ dot b b * dot c c := le_trans (dot_self_nonneg _) h2
    have h4 : Real.sqrt (dot b b * dot c c) = Real.sqrt (dot b b) * Real.sqrt (dot c c) :=
      Real.sqrt_mul (dot_self_nonneg _) _
    rw [← h4]
    exact Real.sqrt_le_sqrt h2
  have hna : norm a ≤ ε := by
    rw [norm]
    have hbb : dot a a ≤ ε * ε := by nlinarith
    have := Real.sqrt_le_sqrt hbb
    rwa [Real.sqrt_mul_self hε] at this
  have hnb : norm b ≤ ε := by
    rw [norm]
    have hbb : dot b b ≤ ε * ε := by nlinarith
    have := Real.sqrt_le_sqrt hbb
    rwa [Real.sqrt_mul_self hε] at this
  have hnc : norm c ≤ ε := by
    rw [norm]
    have hbb : dot c c ≤ ε * ε := by nlinarith
    have := Real.sqrt_le_sqrt hbb
    rwa [Real.sqrt_mul_self hε] at this
  have hna : norm a ≤ ε := by
    rw [norm]
    have hbb : dot a a ≤ ε * ε := by nlinarith
    have := Real.sqrt_le_sqrt hbb
    rwa [Real.sqrt_mul_self hε] at this
  have hprod : norm b * norm c ≤ ε * ε :=
    mul_le_mul hnb hnc (norm_nonneg _) hε
  have h5 : norm a * norm (cross b c) ≤ ε * (ε * ε) := by
    calc norm a * norm (cross b c) ≤ ε * norm (cross b c) :=
        mul_le_mul_of_nonneg_right hna (norm_nonneg _)
      _ ≤ ε * (ε * ε) := mul_le_mul_of_nonneg_left (le_trans h3 hprod) hε
  calc |dot a (cross b c)| ≤ ε * (ε * ε) := le_trans h1 h5
    _ = ε ^ 3 := by ring

/-- The centroid of a triangle. -/
noncomputable def centroid (A B C : V3) : V3 :=
  ⟨(A.x + B.x + C.x) / 3, (A.y + B.y + C.y) / 3, (A.z + B.z + C.z) / 3⟩

/-- `T = A×B + B×C + C×A`: twice the area-weighted normal of the triangle. -/
def T (A B C : V3) : V3 := add (add (cross A B) (cross B C)) (cross C A)

/-- The exact Van Oosterom–Strackee numerator of the triangle's solid
    angle from `p`. -/
def triNum (A B C p : V3) : ℝ := dot (sub A p) (cross (sub B p) (sub C p))

/-- The dipole term of the triangle (what the C Barnes–Hut tree aggregates
    for a distant cluster). -/
noncomputable def triDipole (A B C p : V3) : ℝ := dot (sub (centroid A B C) p) (T A B C)

/-- **The dipole residual identity**: the exact Van Oosterom–Strackee
    numerator splits exactly into the dipole term plus an O(ε³) residual
    sitting on the vertex deviations from the centroid:
    `a·(b×c) = r · T + a'·(b'×c')` where `r = centroid − p`,
    `a'/b'/c' = A/B/C − centroid`. -/
theorem triDipole_identity (A B C p : V3) :
    triNum A B C p =
      triDipole A B C p +
        dot (sub A (centroid A B C))
          (cross (sub B (centroid A B C)) (sub C (centroid A B C))) := by
  unfold triNum triDipole centroid T sub dot cross add
  ring

/-- **The dipole error bound**: the exact solid-angle numerator differs from
    the dipole term by at most `ε³`, when every vertex sits within `ε`
    (in squared length `≤ ε²`) of the centroid. -/
theorem triDipole_residual_bound (A B C p : V3) (ε : ℝ)
    (hA : dot (sub A (centroid A B C)) (sub A (centroid A B C)) ≤ ε ^ 2)
    (hB : dot (sub B (centroid A B C)) (sub B (centroid A B C)) ≤ ε ^ 2)
    (hC : dot (sub C (centroid A B C)) (sub C (centroid A B C)) ≤ ε ^ 2)
    (hε : 0 ≤ ε) :
    |triNum A B C p - triDipole A B C p| ≤ ε ^ 3 := by
  rw [triDipole_identity]
  have hsub : triDipole A B C p + dot (sub A (centroid A B C))
        (cross (sub B (centroid A B C)) (sub C (centroid A B C))) - triDipole A B C p =
      dot (sub A (centroid A B C))
        (cross (sub B (centroid A B C)) (sub C (centroid A B C))) := by
    ring
  rw [hsub]
  exact tri_residual_abs_le hA hB hC hε

/-- Lifting the identity over a list of triangles (the tree cluster). -/
theorem cluster_triNum_eq (fs : List (V3 × V3 × V3)) (p : V3) :
    (fs.map fun f => triNum f.1 f.2.1 f.2.2 p).sum =
      (fs.map fun f => triDipole f.1 f.2.1 f.2.2 p).sum +
        (fs.map fun f =>
          dot (sub f.1 (centroid f.1 f.2.1 f.2.2))
            (cross (sub f.2.1 (centroid f.1 f.2.1 f.2.2))
                   (sub f.2.2 (centroid f.1 f.2.1 f.2.2)))).sum := by
  induction fs with
  | nil => simp [List.sum_nil, List.map_nil]
  | cons f fs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [triDipole_identity f.1 f.2.1 f.2.2 p, ih]
      ring

/-- **Cluster dipole error bound**: total residual ≤ Σ ε_f³. -/
theorem cluster_triNum_residual_bound (fs : List (V3 × V3 × V3)) (p : V3)
    (εs : V3 × V3 × V3 → ℝ)
    (hεs : ∀ f ∈ fs, 0 ≤ εs f)
    (h : ∀ f ∈ fs,
      dot (sub f.1 (centroid f.1 f.2.1 f.2.2)) (sub f.1 (centroid f.1 f.2.1 f.2.2))
          ≤ εs f ^ 2 ∧
      dot (sub f.2.1 (centroid f.1 f.2.1 f.2.2)) (sub f.2.1 (centroid f.1 f.2.1 f.2.2))
          ≤ εs f ^ 2 ∧
      dot (sub f.2.2 (centroid f.1 f.2.1 f.2.2)) (sub f.2.2 (centroid f.1 f.2.1 f.2.2))
          ≤ εs f ^ 2) :
    |(fs.map fun f => triNum f.1 f.2.1 f.2.2 p).sum -
        (fs.map fun f => triDipole f.1 f.2.1 f.2.2 p).sum| ≤
      (fs.map fun f => εs f ^ 3).sum := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
      simp only [List.map_cons, List.sum_cons]
      have hf1 : dot (sub f.1 (centroid f.1 f.2.1 f.2.2)) (sub f.1 (centroid f.1 f.2.1 f.2.2)) ≤ εs f ^ 2 ∧
          dot (sub f.2.1 (centroid f.1 f.2.1 f.2.2)) (sub f.2.1 (centroid f.1 f.2.1 f.2.2)) ≤ εs f ^ 2 ∧
          dot (sub f.2.2 (centroid f.1 f.2.1 f.2.2)) (sub f.2.2 (centroid f.1 f.2.1 f.2.2)) ≤ εs f ^ 2 :=
        h f (by simp)
      have hε := hεs f (by simp)
      have hres := triDipole_residual_bound f.1 f.2.1 f.2.2 p (εs f) hf1.1 hf1.2.1 hf1.2.2 hε
      have hfn1 : triNum f.1 f.2.1 f.2.2 p = triDipole f.1 f.2.1 f.2.2 p +
          dot (sub f.1 (centroid f.1 f.2.1 f.2.2))
            (cross (sub f.2.1 (centroid f.1 f.2.1 f.2.2)) (sub f.2.2 (centroid f.1 f.2.1 f.2.2))) :=
        triDipole_identity f.1 f.2.1 f.2.2 p
      have hres2 : |dot (sub f.1 (centroid f.1 f.2.1 f.2.2))
          (cross (sub f.2.1 (centroid f.1 f.2.1 f.2.2)) (sub f.2.2 (centroid f.1 f.2.1 f.2.2)))|
          = |triNum f.1 f.2.1 f.2.2 p - triDipole f.1 f.2.1 f.2.2 p| := by
        rw [hfn1]; ring_nf
      have htail : ∀ f' ∈ fs,
          dot (sub f'.1 (centroid f'.1 f'.2.1 f'.2.2)) (sub f'.1 (centroid f'.1 f'.2.1 f'.2.2)) ≤ εs f' ^ 2 ∧
            dot (sub f'.2.1 (centroid f'.1 f'.2.1 f'.2.2)) (sub f'.2.1 (centroid f'.1 f'.2.1 f'.2.2)) ≤ εs f' ^ 2 ∧
              dot (sub f'.2.2 (centroid f'.1 f'.2.1 f'.2.2)) (sub f'.2.2 (centroid f'.1 f'.2.1 f'.2.2)) ≤ εs f' ^ 2 :=
        fun f' hf' => h f' (List.Mem.tail f hf')
      have htail' : ∀ f' ∈ fs, 0 ≤ εs f' :=
        fun f' hf' => hεs f' (List.Mem.tail f hf')
      have ih' := ih htail' htail
      rw [hfn1]
      have hrewrite : triDipole f.1 f.2.1 f.2.2 p +
          dot (sub f.1 (centroid f.1 f.2.1 f.2.2))
            (cross (sub f.2.1 (centroid f.1 f.2.1 f.2.2)) (sub f.2.2 (centroid f.1 f.2.1 f.2.2))) +
          (fs.map fun f => triNum f.1 f.2.1 f.2.2 p).sum -
          ((triDipole f.1 f.2.1 f.2.2 p) + (fs.map fun f => triDipole f.1 f.2.1 f.2.2 p).sum)
        = (dot (sub f.1 (centroid f.1 f.2.1 f.2.2))
            (cross (sub f.2.1 (centroid f.1 f.2.1 f.2.2)) (sub f.2.2 (centroid f.1 f.2.1 f.2.2)))) +
          ((fs.map fun f => triNum f.1 f.2.1 f.2.2 p).sum -
            (fs.map fun f => triDipole f.1 f.2.1 f.2.2 p).sum) := by
        ring
      rw [hrewrite]
      calc |dot (sub f.1 (centroid f.1 f.2.1 f.2.2))
            (cross (sub f.2.1 (centroid f.1 f.2.1 f.2.2)) (sub f.2.2 (centroid f.1 f.2.1 f.2.2))) +
            ((fs.map fun f => triNum f.1 f.2.1 f.2.2 p).sum -
              (fs.map fun f => triDipole f.1 f.2.1 f.2.2 p).sum)|
          ≤ |dot (sub f.1 (centroid f.1 f.2.1 f.2.2))
              (cross (sub f.2.1 (centroid f.1 f.2.1 f.2.2)) (sub f.2.2 (centroid f.1 f.2.1 f.2.2)))| +
            |(fs.map fun f => triNum f.1 f.2.1 f.2.2 p).sum -
              (fs.map fun f => triDipole f.1 f.2.1 f.2.2 p).sum| := abs_add_le _ _
        _ ≤ εs f ^ 3 + (fs.map fun f => εs f ^ 3).sum := add_le_add (hres2 ▸ hres) ih'
        _ = List.sum ((f :: fs).map fun f => εs f ^ 3) := by
            simp [List.map_cons, List.sum_cons]

/-! ## The arc-tangent tail bound -/

/-- Remainder estimate for `atan`: `|atan x − x| ≤ |x|³ / 3`. The cubic
    Taylor tail the C solid-angle computation relies on (its
    `atan2(num, den)` for small ratios). -/
theorem abs_atan_sub_id_le_aux {x : ℝ} (hx : 0 ≤ x) :
    |Real.arctan x - x| ≤ x ^ 3 / 3 := by
  have h1 : Continuous fun u : ℝ => 1 + u ^ 2 := by fun_prop
  have h1' : ∀ u : ℝ, 1 + u ^ 2 ≠ 0 := fun u => by nlinarith [sq_nonneg u]
  have hcont : Continuous fun t : ℝ => ((1:ℝ) + t ^ 2)⁻¹ := Continuous.inv₀ h1 h1'
  have key : Real.arctan x - x = - ∫ t in (0:ℝ)..x, t ^ 2 / (1 + t ^ 2) := by
    have h0 : (∫ t in (0:ℝ)..x, ((1:ℝ) + t ^ 2)⁻¹) = Real.arctan x := by
      rw [integral_inv_one_add_sq]
      simp [Real.arctan_zero]
    have h1x : (∫ t in (0:ℝ)..x, (1:ℝ)) = x := by
      simp
    have hsub : ∫ t in (0:ℝ)..x, (((1:ℝ) + t ^ 2)⁻¹ - 1)
        = (∫ t in (0:ℝ)..x, ((1:ℝ) + t ^ 2)⁻¹) - ∫ t in (0:ℝ)..x, 1 :=
      intervalIntegral.integral_sub (Continuous.intervalIntegrable hcont 0 x)
        intervalIntegrable_const
    have hpt : (fun t : ℝ => ((1:ℝ) + t ^ 2)⁻¹ - 1)
        = (fun t : ℝ => -(t ^ 2 / (1 + t ^ 2))) := by
      funext t
      have h : (1:ℝ) + t ^ 2 ≠ 0 := h1' t
      rw [inv_eq_one_div]
      field_simp
      ring
    calc Real.arctan x - x
        = (∫ t in (0:ℝ)..x, ((1:ℝ) + t ^ 2)⁻¹) - ∫ t in (0:ℝ)..x, 1 := by
            rw [h0, h1x]
      _ = ∫ t in (0:ℝ)..x, (((1:ℝ) + t ^ 2)⁻¹ - 1) := by
            rw [hsub]
      _ = ∫ t in (0:ℝ)..x, -(t ^ 2 / (1 + t ^ 2)) := by
            rw [hpt]
      _ = - ∫ t in (0:ℝ)..x, t ^ 2 / (1 + t ^ 2) := by
            rw [← intervalIntegral.integral_neg]
  rw [key]
  have hpos : 0 ≤ ∫ t in (0:ℝ)..x, t ^ 2 / (1 + t ^ 2) := by
    apply intervalIntegral.integral_nonneg hx
    intro t _
    have ht : (0:ℝ) < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    exact div_nonneg (sq_nonneg t) (le_of_lt ht)
  rw [abs_neg, abs_of_nonneg hpos]
  calc ∫ t in (0:ℝ)..x, t ^ 2 / (1 + t ^ 2)
      ≤ ∫ t in (0:ℝ)..x, t ^ 2 := by
        apply intervalIntegral.integral_mono_on hx
          (Continuous.intervalIntegrable (Continuous.div₀ (continuous_pow 2) h1 h1') 0 x)
          (Continuous.intervalIntegrable (continuous_pow 2) 0 x)
        intro t _
        have h3 : 0 ≤ t ^ 2 := sq_nonneg t
        have h4 : (1:ℝ) ≤ 1 + t ^ 2 := by nlinarith
        have h5 : t ^ 2 / (1 + t ^ 2) ≤ t ^ 2 / 1 :=
          div_le_div_of_nonneg_left h3 zero_lt_one h4
        simpa using h5
    _ = x ^ 3 / 3 := by
        rw [integral_pow]
        norm_num

/-- `|atan x − x| ≤ |x|³ / 3` for all `x` (both signs by oddness). -/
theorem abs_atan_sub_id_le (x : ℝ) : |Real.arctan x - x| ≤ |x| ^ 3 / 3 := by
  rcases le_or_gt x 0 with hx | hx
  · have h1 : Real.arctan x - x = -(Real.arctan (-x) - -x) := by
      rw [Real.arctan_neg]
      ring
    rw [h1, abs_neg]
    have h2 := abs_atan_sub_id_le_aux (neg_nonneg.mpr hx)
    have h3 : |x| ^ 3 = (-x) ^ 3 := by
      rw [abs_of_nonpos hx]
    rw [h3]
    exact h2
  · have h2 := abs_atan_sub_id_le_aux hx.le
    rw [abs_of_pos hx]
    exact h2

/-! ## The net dipole of a closed oriented mesh is zero -/

/-- A directed edge-list of a mesh's triangles. -/
def edgeList (fs : List (V3 × V3 × V3)) : List (V3 × V3) :=
  fs.flatMap fun f => [(f.1, f.2.1), (f.2.1, f.2.2), (f.2.2, f.1)]

/-- Re-association of `V3.add`. -/
theorem add_assoc' (a b c : V3) : add (add a b) c = add a (add b c) := by
  apply V3.ext <;> simp [add] <;> ring

/-- `sumV3` over a list of `V3` (right-recursive, like `sumEdges` in Assembly). -/
def sumV3 : List V3 → V3
  | [] => ⟨0, 0, 0⟩
  | a :: l => add a (sumV3 l)

theorem sumV3_nil : sumV3 [] = ⟨0, 0, 0⟩ := rfl

theorem sumV3_cons (a : V3) (l : List V3) : sumV3 (a :: l) = add a (sumV3 l) := rfl

theorem sumV3_append (l₁ l₂ : List V3) : sumV3 (l₁ ++ l₂) = add (sumV3 l₁) (sumV3 l₂) := by
  induction l₁ with
  | nil => apply V3.ext <;> simp [sumV3_nil, add]
  | cons a l₁ ih => simp [List.cons_append, sumV3_cons, ih, ← add_assoc']

def crossEdgeSum (fs : List (V3 × V3 × V3)) : V3 :=
  sumV3 ((edgeList fs).map fun e => cross e.1 e.2)

/-- The sum of the per-face `T`s equals the cross-sum over the directed edge
    list. -/
theorem Tsum_eq_crossEdgeSum (fs : List (V3 × V3 × V3)) :
    sumV3 (fs.map (fun f => T f.1 f.2.1 f.2.2)) = crossEdgeSum fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      obtain ⟨A, B, C⟩ := f
      have h_edge : edgeList (⟨A, B, C⟩ :: fs) = (A, B) :: (B, C) :: (C, A) :: edgeList fs := by
        simp [edgeList, List.flatMap]
      have hce : crossEdgeSum (⟨A, B, C⟩ :: fs)
          = add (cross A B) (add (cross B C) (add (cross C A) (crossEdgeSum fs))) := by
        have hce2 := congrArg (fun l => sumV3 (l.map fun e => cross e.1 e.2)) h_edge
        simpa [crossEdgeSum, sumV3, List.map_cons] using hce2
      rw [List.map_cons, sumV3_cons, hce, ih]
      simp only [T]
      rw [add_assoc', add_assoc']

/-- `cross` swap negates. -/
theorem cross_swap (a b : V3) : cross a b = sub ⟨0, 0, 0⟩ (cross b a) := by
  apply V3.ext <;> simp [cross, sub] <;> ring

/-- Flipping every edge in the list negates the cross-sum (as a zero-sum
    decomposition of `sumV3`). -/
theorem sumV3_map_cross_flip (es : List (V3 × V3)) :
    sumV3 (es.map (fun e => cross e.2 e.1)) = sub ⟨0, 0, 0⟩ (sumV3 (es.map (fun e => cross e.1 e.2))) := by
  induction es with
  | nil => simp [sumV3_nil, sub]
  | cons e es ih =>
      obtain ⟨a, b⟩ := e
      simp only [List.map_cons, sumV3_cons, ih]
      rw [cross_swap b a]
      apply V3.ext <;> simp [sub, add] <;> ring

/-- **Net dipole of a closed oriented mesh is zero**: if the directed edge
    list is fixed under `flip` (every directed edge appears with the same
    multiplicity as its reverse), the sum of all area-weighted normals
    vanishes. This is the consistency fact that makes the dipole-far-field
    approximation vanish at infinity for closed surfaces. -/
theorem closed_net_dipole_zero (fs : List (V3 × V3 × V3))
    (h : edgeList fs = (edgeList fs).map fun e => (e.2, e.1)) :
    sumV3 (fs.map (fun f => T f.1 f.2.1 f.2.2)) = ⟨0, 0, 0⟩ := by
  have h2 : List.map (fun e => cross e.2 e.1) (edgeList fs)
          = List.map (fun e => cross e.1 e.2) (edgeList fs) := by
    conv_lhs => rw [h, List.map_map]
    simp [Function.comp_def]
  have h3 := sumV3_map_cross_flip (edgeList fs)
  rw [h2] at h3
  have h3' : sumV3 ((edgeList fs).map (fun e => cross e.1 e.2)) = ⟨0, 0, 0⟩ := by
    apply V3.ext
    · have hx0 := congrArg V3.x h3
      simp only [sub] at hx0
      linarith
    · have hy0 := congrArg V3.y h3
      simp only [sub] at hy0
      linarith
    · have hz0 := congrArg V3.z h3
      simp only [sub] at hz0
      linarith
  have h4 : crossEdgeSum fs = ⟨0, 0, 0⟩ := h3'
  rw [Tsum_eq_crossEdgeSum, h4]

end V3
end Vdb
