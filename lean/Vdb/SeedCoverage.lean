/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format and volume operators.

  T-BAND-SEED-COVERAGE: the seed-coverage estimate that `Vdb.NarrowBand`
  currently takes as the hypothesis `hcover`, proved here for triangular
  meshes with no weakening of the constant `2 / √3`.

  Model of the C seeding loop in `tvdb_mesh_to_level_set`
  (`src/tinyvdb_sparse_tools.c`): for every triangle the C code samples the
  barycentric grid `p(i,j) = X₀ + (i/n)(X₁-X₀) + (j/n)(X₂-X₀)`, `i+j ≤ n`,
  with `n = ceil(2·l/h)` (`l` = longest edge), i.e. sub-triangle side
  `l/n ≤ h/2`, and snaps every sample to the nearest voxel centre
  `h · round(p/h)` (`round(x) = floor(x + 1/2)`). The claim discharged here:

      every point of every triangle is within `2·h/√3` of a snapped seed.

  Proof structure (all in voxel units where convenient; `h` threaded through):

    * `variance_scalar` / `variance_vec` — the barycentric variance identity
      `Σ aᵢ · |Xᵢ - q|² = Σ_{i<j} aᵢaⱼ |Xᵢ-Xⱼ|²` for `q = Σ aᵢXᵢ`;
    * `triangle_vertex_cover` — a triangle of diameter `s` has every convex
      combination within `s/√3` of one of its vertices (Jung radius at a
      vertex; proved algebraically, no trigonometry);
    * `subdivision_cover` — the barycentric grid subdivides any triangle into
      sub-triangles of diameter `l/n ≤ h/2`, so every surface point is within
      `h/(2√3)` of a sample;
    * `snap_bound` — snapping moves a point by at most `h√3/2`;
    * `seed_coverage` — triangle inequality gives `h/(2√3) + h√3/2 = 2h/√3`.

  The result is stated for every `h > 0` and every (possibly degenerate)
  triangle with finite coordinates. It feeds `Vdb.NarrowBand.band_complete`
  by supplying its `hcover` argument for closed triangle meshes.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import Vdb.NarrowBand

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Vdb.SeedCoverage

open Finset

/-- A point of ℝ³ (reuse the NarrowBand model). -/
abbrev V3 := Vdb.P3R

/-- Componentwise vector subtraction. -/
def vsub (a b : V3) : V3 := fun k => a k - b k
/-- Componentwise vector addition. -/
def vadd (a b : V3) : V3 := fun k => a k + b k
/-- Scalar multiplication. -/
def vscale (a : V3) (c : ℝ) : V3 := fun k => a k * c

/-- Squared Euclidean norm from the (explicit) dot product. -/
def nsq (x : V3) : ℝ := ∑ k : Fin 3, x k * x k

/-- Squared distance. -/
def dsq (a b : V3) : ℝ := nsq (vsub a b)

/-- Euclidean distance (matches `Vdb.edist`). -/
noncomputable def dist (a b : V3) : ℝ := Real.sqrt (dsq a b)

/-- `dist` is `Vdb.edist`. -/
theorem dist_eq_edist (a b : V3) : dist a b = Vdb.edist a b := by
  unfold dist dsq nsq vsub Vdb.edist Vdb.distSq
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring_nf

/-- Affine combination of the three triangle vertices: `X₀ + a(X₁-X₀) + b(X₂-X₀)`. -/
def aff (X0 X1 X2 : V3) (a b : ℝ) : V3 :=
  vadd X0 (vadd (vscale (vsub X1 X0) a) (vscale (vsub X2 X0) b))

/-- The barycentric combination of three points with weights `a₀ a₁ a₂`. -/
def bary (X0 X1 X2 : V3) (a0 a1 a2 : ℝ) : V3 :=
  fun k => a0 * X0 k + a1 * X1 k + a2 * X2 k

/-! ### The variance identity (scalar, then vector) -/

/-- Scalar variance identity: for `a₀+a₁+a₂ = 1` and `q = a₀x₀+a₁x₁+a₂x₂`,
    `Σ aᵢ(xᵢ-q)² = Σ_{i<j} aᵢaⱼ(xᵢ-xⱼ)²`. -/
lemma variance_scalar (a0 a1 a2 x0 x1 x2 : ℝ) (hsum : a0 + a1 + a2 = 1) :
    a0 * (x0 - (a0*x0 + a1*x1 + a2*x2)) ^ 2 +
        a1 * (x1 - (a0*x0 + a1*x1 + a2*x2)) ^ 2 +
        a2 * (x2 - (a0*x0 + a1*x1 + a2*x2)) ^ 2 =
      a0*a1*(x0-x1)^2 + a0*a2*(x0-x2)^2 + a1*a2*(x1-x2)^2 := by
  have ha0 : a0 = 1 - a1 - a2 := by linarith
  rw [ha0]
  ring_nf

/-- Distribute three scalar multiples over three `univ` sums into one sum. -/
lemma sum_scale3 (a0 a1 a2 : ℝ) (f0 f1 f2 : Fin 3 → ℝ) :
    a0 * (∑ k, f0 k) + a1 * (∑ k, f1 k) + a2 * (∑ k, f2 k) =
      ∑ k, (a0 * f0 k + a1 * f1 k + a2 * f2 k) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- Vector variance identity: same statement, squared norm summed componentwise. -/
lemma variance_vec (a0 a1 a2 : ℝ) (hsum : a0 + a1 + a2 = 1)
    (X0 X1 X2 : V3) :
    a0 * dsq X0 (bary X0 X1 X2 a0 a1 a2) +
        a1 * dsq X1 (bary X0 X1 X2 a0 a1 a2) +
        a2 * dsq X2 (bary X0 X1 X2 a0 a1 a2) =
      a0*a1*dsq X0 X1 + a0*a2*dsq X0 X2 + a1*a2*dsq X1 X2 := by
  let q : V3 := bary X0 X1 X2 a0 a1 a2
  have hcomp : ∀ k : Fin 3,
      a0 * (X0 k - q k) ^ 2 + a1 * (X1 k - q k) ^ 2 + a2 * (X2 k - q k) ^ 2 =
        a0*a1*(X0 k - X1 k)^2 + a0*a2*(X0 k - X2 k)^2 + a1*a2*(X1 k - X2 k)^2 := by
    intro k
    unfold q bary
    exact variance_scalar a0 a1 a2 (X0 k) (X1 k) (X2 k) hsum
  calc
    a0 * dsq X0 q + a1 * dsq X1 q + a2 * dsq X2 q
        = ∑ k : Fin 3, (a0 * (X0 k - q k) ^ 2 + a1 * (X1 k - q k) ^ 2 + a2 * (X2 k - q k) ^ 2) := by
            unfold dsq nsq vsub
            rw [sum_scale3]
            apply Finset.sum_congr rfl
            intro k hk
            ring_nf
    _ = ∑ k : Fin 3, (a0*a1*(X0 k - X1 k)^2 + a0*a2*(X0 k - X2 k)^2 + a1*a2*(X1 k - X2 k)^2) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hcomp k
    _ = a0*a1*dsq X0 X1 + a0*a2*dsq X0 X2 + a1*a2*dsq X1 X2 := by
            unfold dsq nsq vsub
            rw [sum_scale3]
            apply Finset.sum_congr rfl
            intro k hk
            ring_nf

/-- Squared distance is symmetric. -/
lemma dsq_comm (a b : V3) : dsq a b = dsq b a := by
  unfold dsq nsq vsub
  apply Finset.sum_congr rfl
  intro k hk
  ring_nf

/-- Squared distance is non-negative. -/
lemma dsq_nonneg (a b : V3) : 0 ≤ dsq a b := by
  unfold dsq nsq vsub
  exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- For nonnegative weights summing to one, `a₀a₁ + a₀a₂ + a₁a₂ ≤ 1/3`. -/
lemma cross_le_third (a0 a1 a2 : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hsum : a0 + a1 + a2 = 1) : a0*a1 + a0*a2 + a1*a2 ≤ 1/3 := by
  nlinarith [sq_nonneg (a0 - a1), sq_nonneg (a0 - a2), sq_nonneg (a1 - a2)]

/-- **Triangle vertex cover (squared form).** For a triangle of diameter `s`
    (all three squared edge lengths `≤ s²`), every convex combination `q` is
    at squared distance `≤ s²/3` from at least one vertex. -/
lemma triangle_vertex_cover_sq (X0 X1 X2 : V3) (s : ℝ) (_hs : 0 ≤ s)
    (h01 : dsq X0 X1 ≤ s^2) (h02 : dsq X0 X2 ≤ s^2) (h12 : dsq X1 X2 ≤ s^2)
    (a0 a1 a2 : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hsum : a0 + a1 + a2 = 1) :
    dsq (bary X0 X1 X2 a0 a1 a2) X0 ≤ s^2/3 ∨
    dsq (bary X0 X1 X2 a0 a1 a2) X1 ≤ s^2/3 ∨
    dsq (bary X0 X1 X2 a0 a1 a2) X2 ≤ s^2/3 := by
  have hs2 : 0 ≤ s^2 := sq_nonneg s
  have hle : a0 * dsq (bary X0 X1 X2 a0 a1 a2) X0 +
             a1 * dsq (bary X0 X1 X2 a0 a1 a2) X1 +
             a2 * dsq (bary X0 X1 X2 a0 a1 a2) X2 ≤ s^2/3 := by
    calc
      a0 * dsq (bary X0 X1 X2 a0 a1 a2) X0 +
          a1 * dsq (bary X0 X1 X2 a0 a1 a2) X1 +
          a2 * dsq (bary X0 X1 X2 a0 a1 a2) X2
          = a0 * dsq X0 (bary X0 X1 X2 a0 a1 a2) +
            a1 * dsq X1 (bary X0 X1 X2 a0 a1 a2) +
            a2 * dsq X2 (bary X0 X1 X2 a0 a1 a2) := by
              rw [dsq_comm (bary X0 X1 X2 a0 a1 a2) X0,
                  dsq_comm (bary X0 X1 X2 a0 a1 a2) X1,
                  dsq_comm (bary X0 X1 X2 a0 a1 a2) X2]
      _ = a0*a1*dsq X0 X1 + a0*a2*dsq X0 X2 + a1*a2*dsq X1 X2 :=
              variance_vec a0 a1 a2 hsum X0 X1 X2
      _ ≤ a0*a1*s^2 + a0*a2*s^2 + a1*a2*s^2 := by
              have h01n : 0 ≤ a0*a1 := mul_nonneg ha0 ha1
              have h02n : 0 ≤ a0*a2 := mul_nonneg ha0 ha2
              have h12n : 0 ≤ a1*a2 := mul_nonneg ha1 ha2
              nlinarith
      _ = (a0*a1 + a0*a2 + a1*a2) * s^2 := by ring_nf
      _ ≤ (1/3 : ℝ) * s^2 :=
              mul_le_mul_of_nonneg_right (cross_le_third a0 a1 a2 ha0 ha1 ha2 hsum) hs2
      _ = s^2/3 := by ring_nf
  by_contra h
  push Not at h
  have hpos : 0 < a0 ∨ 0 < a1 ∨ 0 < a2 := by
    by_contra hn
    push Not at hn
    nlinarith
  rcases hpos with hpos | hpos | hpos
  · have hm : a0 * (s^2/3) < a0 * dsq (bary X0 X1 X2 a0 a1 a2) X0 :=
        mul_lt_mul_of_pos_left h.1 hpos
    have h1 : 0 ≤ a1 * (dsq (bary X0 X1 X2 a0 a1 a2) X1 - s^2/3) :=
        mul_nonneg ha1 (sub_nonneg.mpr (le_of_lt h.2.1))
    have h2 : 0 ≤ a2 * (dsq (bary X0 X1 X2 a0 a1 a2) X2 - s^2/3) :=
        mul_nonneg ha2 (sub_nonneg.mpr (le_of_lt h.2.2))
    nlinarith
  · have hm : a1 * (s^2/3) < a1 * dsq (bary X0 X1 X2 a0 a1 a2) X1 :=
        mul_lt_mul_of_pos_left h.2.1 hpos
    have h0 : 0 ≤ a0 * (dsq (bary X0 X1 X2 a0 a1 a2) X0 - s^2/3) :=
        mul_nonneg ha0 (sub_nonneg.mpr (le_of_lt h.1))
    have h2 : 0 ≤ a2 * (dsq (bary X0 X1 X2 a0 a1 a2) X2 - s^2/3) :=
        mul_nonneg ha2 (sub_nonneg.mpr (le_of_lt h.2.2))
    nlinarith
  · have hm : a2 * (s^2/3) < a2 * dsq (bary X0 X1 X2 a0 a1 a2) X2 :=
        mul_lt_mul_of_pos_left h.2.2 hpos
    have h0 : 0 ≤ a0 * (dsq (bary X0 X1 X2 a0 a1 a2) X0 - s^2/3) :=
        mul_nonneg ha0 (sub_nonneg.mpr (le_of_lt h.1))
    have h1 : 0 ≤ a1 * (dsq (bary X0 X1 X2 a0 a1 a2) X1 - s^2/3) :=
        mul_nonneg ha1 (sub_nonneg.mpr (le_of_lt h.2.1))
    nlinarith

/-- Square root of `s²/3` is `s/√3` for `s ≥ 0`. -/
lemma sqrt_sq_div_three (s : ℝ) (hs : 0 ≤ s) : Real.sqrt (s^2 / 3) = s / Real.sqrt 3 := by
  rw [Real.sqrt_div (sq_nonneg s) (3:ℝ), Real.sqrt_sq_eq_abs, abs_of_nonneg hs]

/-- **Triangle vertex cover (distance form).** Every convex combination of a
    triangle of diameter `s` lies within `s / √3` of one of its vertices. -/
lemma triangle_vertex_cover (X0 X1 X2 : V3) (s : ℝ) (hs : 0 ≤ s)
    (h01 : dsq X0 X1 ≤ s^2) (h02 : dsq X0 X2 ≤ s^2) (h12 : dsq X1 X2 ≤ s^2)
    (a0 a1 a2 : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hsum : a0 + a1 + a2 = 1) :
    dist (bary X0 X1 X2 a0 a1 a2) X0 ≤ s / Real.sqrt 3 ∨
    dist (bary X0 X1 X2 a0 a1 a2) X1 ≤ s / Real.sqrt 3 ∨
    dist (bary X0 X1 X2 a0 a1 a2) X2 ≤ s / Real.sqrt 3 := by
  have hs3 : 0 ≤ s / Real.sqrt 3 := div_nonneg hs (Real.sqrt_nonneg _)
  have h := triangle_vertex_cover_sq X0 X1 X2 s hs h01 h02 h12
      a0 a1 a2 ha0 ha1 ha2 hsum
  rcases h with h0 | h1 | h2
  · left
    calc dist (bary X0 X1 X2 a0 a1 a2) X0 = Real.sqrt (dsq (bary X0 X1 X2 a0 a1 a2) X0) := rfl
         _ ≤ Real.sqrt (s^2/3) := Real.sqrt_le_sqrt h0
         _ = s / Real.sqrt 3 := sqrt_sq_div_three s hs
  · right; left
    calc dist (bary X0 X1 X2 a0 a1 a2) X1 = Real.sqrt (dsq (bary X0 X1 X2 a0 a1 a2) X1) := rfl
         _ ≤ Real.sqrt (s^2/3) := Real.sqrt_le_sqrt h1
         _ = s / Real.sqrt 3 := sqrt_sq_div_three s hs
  · right; right
    calc dist (bary X0 X1 X2 a0 a1 a2) X2 = Real.sqrt (dsq (bary X0 X1 X2 a0 a1 a2) X2) := rfl
         _ ≤ Real.sqrt (s^2/3) := Real.sqrt_le_sqrt h2
         _ = s / Real.sqrt 3 := sqrt_sq_div_three s hs

/-- The barycentric grid sample with real index `u v` (the C loop uses `u = i`,
    `v = j`, integers `0 ≤ i, j`, `i + j ≤ n`). -/
noncomputable def sampleR (n : ℕ) (X0 X1 X2 : V3) (u v : ℝ) : V3 :=
  bary X0 X1 X2
    (1 - u / (n : ℝ) - v / (n : ℝ)) (u / (n : ℝ)) (v / (n : ℝ))

/-- `sampleR` equals the affine map at `(u/n, v/n)`. -/
lemma sampleR_eq_aff (n : ℕ) (X0 X1 X2 : V3) (u v : ℝ) :
    sampleR n X0 X1 X2 u v = aff X0 X1 X2 (u/(n:ℝ)) (v/(n:ℝ)) := by
  ext k
  unfold sampleR bary aff vadd vscale vsub
  ring_nf

/-- Componentwise difference of two affine-map points. -/
lemma aff_diff (X0 X1 X2 : V3) (a b c d : ℝ) (k : Fin 3) :
    aff X0 X1 X2 a b k - aff X0 X1 X2 c d k =
      (a - c) * (X1 k - X0 k) + (b - d) * (X2 k - X0 k) := by
  unfold aff vadd vscale vsub
  ring_nf

/-- If two affine-map points differ only in the `a` parameter, the squared
    distance is `dsq X0 X1 * (a-c)^2`. -/
lemma dsq_aff_a (X0 X1 X2 : V3) (a c b : ℝ) :
    dsq (aff X0 X1 X2 a b) (aff X0 X1 X2 c b) = dsq X0 X1 * (a - c)^2 := by
  unfold dsq nsq vsub
  calc
    (∑ k : Fin 3,
        (aff X0 X1 X2 a b k - aff X0 X1 X2 c b k) *
        (aff X0 X1 X2 a b k - aff X0 X1 X2 c b k))
        = ∑ k : Fin 3, ((a - c) * (X1 k - X0 k))^2 := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [aff_diff]
            ring_nf
    _ = ∑ k : Fin 3, (a - c)^2 * (X1 k - X0 k)^2 := by
            apply Finset.sum_congr rfl
            intro k hk
            ring_nf
    _ = (a - c)^2 * ∑ k : Fin 3, (X1 k - X0 k)^2 := by
            rw [Finset.mul_sum]
    _ = (a - c)^2 * dsq X1 X0 := by
            unfold dsq nsq vsub
            ring_nf
    _ = dsq X0 X1 * (a - c)^2 := by
            rw [dsq_comm]
            ring_nf

/-- If two affine-map points differ only in the `b` parameter, the squared
    distance is `dsq X0 X2 * (b-d)^2`. -/
lemma dsq_aff_b (X0 X1 X2 : V3) (b d a : ℝ) :
    dsq (aff X0 X1 X2 a b) (aff X0 X1 X2 a d) = dsq X0 X2 * (b - d)^2 := by
  unfold dsq nsq vsub
  calc
    (∑ k : Fin 3,
        (aff X0 X1 X2 a b k - aff X0 X1 X2 a d k) *
        (aff X0 X1 X2 a b k - aff X0 X1 X2 a d k))
        = ∑ k : Fin 3, ((b - d) * (X2 k - X0 k))^2 := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [aff_diff]
            ring_nf
    _ = ∑ k : Fin 3, (b - d)^2 * (X2 k - X0 k)^2 := by
            apply Finset.sum_congr rfl
            intro k hk
            ring_nf
    _ = (b - d)^2 * ∑ k : Fin 3, (X2 k - X0 k)^2 := by
            rw [Finset.mul_sum]
    _ = (b - d)^2 * dsq X2 X0 := by
            unfold dsq nsq vsub
            ring_nf
    _ = dsq X0 X2 * (b - d)^2 := by
            rw [dsq_comm]
            ring_nf

/-- Equal-and-opposite parameter changes along a grid diagonal: the squared
    distance is `dsq X1 X2 * t^2`. -/
lemma dsq_aff_ab (X0 X1 X2 : V3) (t a b : ℝ) :
    dsq (aff X0 X1 X2 (a+t) b) (aff X0 X1 X2 a (b+t)) = dsq X1 X2 * t^2 := by
  unfold dsq nsq vsub
  calc
    (∑ k : Fin 3,
        (aff X0 X1 X2 (a+t) b k - aff X0 X1 X2 a (b+t) k) *
        (aff X0 X1 X2 (a+t) b k - aff X0 X1 X2 a (b+t) k))
        = ∑ k : Fin 3, (t * (X1 k - X2 k))^2 := by
            apply Finset.sum_congr rfl
            intro k hk
            unfold aff vadd vscale vsub
            ring_nf
    _ = ∑ k : Fin 3, t^2 * (X1 k - X2 k)^2 := by
            apply Finset.sum_congr rfl
            intro k hk
            ring_nf
    _ = t^2 * ∑ k : Fin 3, (X1 k - X2 k)^2 := by
            rw [Finset.mul_sum]
    _ = dsq X1 X2 * t^2 := by
            unfold dsq nsq vsub
            ring_nf

/-- The `u`-step of the barycentric grid is `(X1-X0)/n` long. -/
lemma dsq_sample_step_u (n : ℕ) (hn : 0 < n) (X0 X1 X2 : V3) (u v : ℝ) :
    dsq (sampleR n X0 X1 X2 (u+1) v) (sampleR n X0 X1 X2 u v) =
      dsq X0 X1 / (n : ℝ)^2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [sampleR_eq_aff, sampleR_eq_aff, dsq_aff_a]
  have h : (u + 1) / (n : ℝ) - u / (n : ℝ) = 1 / (n : ℝ) := by
    field_simp [hn0]
    ring_nf
  rw [h]
  ring_nf

/-- The `v`-step of the barycentric grid is `(X2-X0)/n` long. -/
lemma dsq_sample_step_v (n : ℕ) (hn : 0 < n) (X0 X1 X2 : V3) (u v : ℝ) :
    dsq (sampleR n X0 X1 X2 u (v+1)) (sampleR n X0 X1 X2 u v) =
      dsq X0 X2 / (n : ℝ)^2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [sampleR_eq_aff, sampleR_eq_aff, dsq_aff_b]
  have h : (v + 1) / (n : ℝ) - v / (n : ℝ) = 1 / (n : ℝ) := by
    field_simp [hn0]
    ring_nf
  rw [h]
  ring_nf

/-- The `u`-down / `v`-across diagonal of a grid cell is `(X1-X2)/n` long. -/
lemma dsq_sample_diag (n : ℕ) (hn : 0 < n) (X0 X1 X2 : V3) (u v : ℝ) :
    dsq (sampleR n X0 X1 X2 (u+1) v) (sampleR n X0 X1 X2 u (v+1)) =
      dsq X1 X2 / (n : ℝ)^2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [sampleR_eq_aff, sampleR_eq_aff]
  have hu : (u + 1) / (n : ℝ) = u / (n : ℝ) + 1 / (n : ℝ) := by
    field_simp [hn0]
  have hv : (v + 1) / (n : ℝ) = v / (n : ℝ) + 1 / (n : ℝ) := by
    field_simp [hn0]
  rw [hu, hv, dsq_aff_ab]
  ring_nf

/-- The barycentric combination `(1-u-v, u, v)` is the affine map `(u,v)`. -/
lemma bary_eq_aff (X0 X1 X2 : V3) (u v : ℝ) :
    bary X0 X1 X2 (1 - u - v) u v = aff X0 X1 X2 u v := by
  ext k
  unfold bary aff vadd vscale vsub
  ring_nf

/-- Positive square root of three. -/
lemma sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
lemma sqrt3_ne : Real.sqrt 3 ≠ 0 := ne_of_gt sqrt3_pos

/-- `l/n` divided by `√3` equals `l/(n√3)`. -/
lemma div_sqrt3_eq (l : ℝ) (n : ℕ) (hn : 0 < n) :
    (l / (n : ℝ)) / Real.sqrt 3 = l / ((n : ℝ) * Real.sqrt 3) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  field_simp [hn0, sqrt3_ne]

/-- **Barycentric subdivision cover.** Let the triangle `X₀X₁X₂` have diameter
    bounded by `l` (all three `dsq ≤ l²`), and let `n ≥ 1`. For every convex
    combination `q` of the three vertices there is a barycentric grid sample
    `p(i,j) = X₀ + (i/n)(X₁-X₀) + (j/n)(X₂-X₀)` with `i+j ≤ n` and
    `dist q p(i,j) ≤ l/(n√3)`.

    This is the covering-radius fact behind the C code's spacing `l/n ≤ h/2`:
    each of the `n²` sub-triangles has diameter `≤ l/n`, and
    `triangle_vertex_cover` puts every point within `(l/n)/√3` of a vertex. -/
lemma subdivision_cover (X0 X1 X2 : V3) (l : ℝ) (hl : 0 ≤ l) (n : ℕ) (hn : 0 < n)
    (h01 : dsq X0 X1 ≤ l^2) (h02 : dsq X0 X2 ≤ l^2) (h12 : dsq X1 X2 ≤ l^2)
    (a0 a1 a2 : ℝ) (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hsum : a0 + a1 + a2 = 1) :
    ∃ i j : ℕ, i + j ≤ n ∧
      dist (bary X0 X1 X2 a0 a1 a2) (sampleR n X0 X1 X2 (i : ℝ) (j : ℝ)) ≤
        l / ((n : ℝ) * Real.sqrt 3) := by
  let q : V3 := bary X0 X1 X2 a0 a1 a2
  let u : ℝ := a1
  let v : ℝ := a2
  have hnreal_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hq_aff : q = aff X0 X1 X2 u v := by
    dsimp [q, u, v]
    rw [show a0 = 1 - a1 - a2 by linarith]
    exact bary_eq_aff X0 X1 X2 a1 a2
  let i : ℕ := Nat.floor ((n : ℝ) * u)
  let j : ℕ := Nat.floor ((n : ℝ) * v)
  let x : ℝ := (n : ℝ) * u - (i : ℝ)
  let y : ℝ := (n : ℝ) * v - (j : ℝ)
  have hnu : 0 ≤ (n : ℝ) * u := mul_nonneg hnreal_nonneg ha1
  have hnv : 0 ≤ (n : ℝ) * v := mul_nonneg hnreal_nonneg ha2
  have hi_le : (i : ℝ) ≤ (n : ℝ) * u := by
    dsimp [i]; exact Nat.floor_le hnu
  have hj_le : (j : ℝ) ≤ (n : ℝ) * v := by
    dsimp [j]; exact Nat.floor_le hnv
  have hi_lt : (n : ℝ) * u < (i : ℝ) + 1 := by
    dsimp [i]; exact Nat.lt_floor_add_one ((n : ℝ) * u)
  have hj_lt : (n : ℝ) * v < (j : ℝ) + 1 := by
    dsimp [j]; exact Nat.lt_floor_add_one ((n : ℝ) * v)
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hx1 : x < 1 := by dsimp [x]; linarith
  have hy1 : y < 1 := by dsimp [y]; linarith
  have huv : u + v ≤ 1 := by dsimp [u, v]; nlinarith
  have hijR : (i : ℝ) + (j : ℝ) ≤ (n : ℝ) := by
    have hmul : (n : ℝ) * (u + v) ≤ (n : ℝ) := by
      simpa using (mul_le_mul_of_nonneg_left huv hnreal_nonneg)
    nlinarith
  have hij : i + j ≤ n := by exact_mod_cast hijR
  have hu_eq : u = ((i : ℝ) + x) / (n : ℝ) := by
    dsimp [x]
    field_simp [hn0]
    ring_nf
  have hv_eq : v = ((j : ℝ) + y) / (n : ℝ) := by
    dsimp [y]
    field_simp [hn0]
    ring_nf
  let m : ℕ := n - (i + j)
  have hmcast : (m : ℝ) = (n : ℝ) - (i : ℝ) - (j : ℝ) := by
    dsimp [m]
    rw [Nat.cast_sub hij]
    push_cast
    ring_nf
  have hxy_le_m : x + y ≤ (m : ℝ) := by
    rw [hmcast]
    dsimp [x, y]
    have hmul : (n : ℝ) * (u + v) ≤ (n : ℝ) := by
      simpa using (mul_le_mul_of_nonneg_left huv hnreal_nonneg)
    nlinarith
  have hs_nonneg : 0 ≤ l / (n : ℝ) := by positivity
  have hs_sq : (l / (n : ℝ)) ^ 2 = l^2 / (n : ℝ)^2 := by
    field_simp [hn0]
  by_cases hm0 : m = 0
  · -- i + j = n, so x = y = 0 and q is itself a grid sample.
    have hxy_nonpos : x + y ≤ 0 := by simpa [hm0] using hxy_le_m
    have hx_eq : x = 0 := by nlinarith
    have hy_eq : y = 0 := by nlinarith
    have hu_eq_i : u = (i : ℝ) / (n : ℝ) := by rw [hu_eq, hx_eq]; ring_nf
    have hv_eq_j : v = (j : ℝ) / (n : ℝ) := by rw [hv_eq, hy_eq]; ring_nf
    refine ⟨i, j, hij, ?_⟩
    have hq : q = sampleR n X0 X1 X2 (i : ℝ) (j : ℝ) := by
      rw [hq_aff, sampleR_eq_aff, hu_eq_i, hv_eq_j]
    change dist q (sampleR n X0 X1 X2 (i : ℝ) (j : ℝ)) ≤ l / ((n : ℝ) * Real.sqrt 3)
    rw [hq]
    unfold dist dsq nsq vsub
    simp only [sub_self, mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
    positivity
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    have hm1 : 1 ≤ m := hmpos
    by_cases hxy : x + y ≤ 1
    · -- Upward sub-triangle (i,j), (i+1,j), (i,j+1).
      let P0 : V3 := sampleR n X0 X1 X2 (i : ℝ) (j : ℝ)
      let P1 : V3 := sampleR n X0 X1 X2 ((i : ℝ) + 1) (j : ℝ)
      let P2 : V3 := sampleR n X0 X1 X2 (i : ℝ) ((j : ℝ) + 1)
      have hP1idx : i + 1 + j ≤ n := by omega
      have hP2idx : i + (j + 1) ≤ n := by omega
      have hqP : q = bary P0 P1 P2 (1 - x - y) x y := by
        rw [hq_aff]
        dsimp [P0, P1, P2]
        rw [sampleR_eq_aff, sampleR_eq_aff, sampleR_eq_aff]
        ext k
        unfold bary aff vadd vscale vsub
        dsimp [x, y, u, v]
        field_simp [hn0]
        ring_nf
      have he01 : dsq P0 P1 ≤ (l / (n : ℝ)) ^ 2 := by
        rw [hs_sq, dsq_comm]
        dsimp [P0, P1]
        rw [dsq_sample_step_u n hn X0 X1 X2 (i : ℝ) (j : ℝ)]
        exact div_le_div_of_nonneg_right h01 (sq_nonneg (n : ℝ))
      have he02 : dsq P0 P2 ≤ (l / (n : ℝ)) ^ 2 := by
        rw [hs_sq, dsq_comm]
        dsimp [P0, P2]
        rw [dsq_sample_step_v n hn X0 X1 X2 (i : ℝ) (j : ℝ)]
        exact div_le_div_of_nonneg_right h02 (sq_nonneg (n : ℝ))
      have he12 : dsq P1 P2 ≤ (l / (n : ℝ)) ^ 2 := by
        rw [hs_sq]
        dsimp [P1, P2]
        rw [dsq_sample_diag n hn X0 X1 X2 (i : ℝ) (j : ℝ)]
        exact div_le_div_of_nonneg_right h12 (sq_nonneg (n : ℝ))
      have hcov := triangle_vertex_cover P0 P1 P2 (l / (n : ℝ)) hs_nonneg
          he01 he02 he12 (1 - x - y) x y (by linarith) hx0 hy0 (by ring)
      rw [← hqP] at hcov
      rcases hcov with h0 | h1 | h2
      · refine ⟨i, j, hij, ?_⟩
        change dist q (sampleR n X0 X1 X2 (i : ℝ) (j : ℝ)) ≤ l / ((n : ℝ) * Real.sqrt 3)
        dsimp [P0] at h0
        exact h0.trans_eq (div_sqrt3_eq l n hn)
      · refine ⟨i + 1, j, hP1idx, ?_⟩
        push_cast
        change dist q (sampleR n X0 X1 X2 ((i : ℝ) + 1) (j : ℝ)) ≤ l / ((n : ℝ) * Real.sqrt 3)
        dsimp [P1] at h1
        exact h1.trans_eq (div_sqrt3_eq l n hn)
      · refine ⟨i, j + 1, hP2idx, ?_⟩
        push_cast
        change dist q (sampleR n X0 X1 X2 (i : ℝ) ((j : ℝ) + 1)) ≤ l / ((n : ℝ) * Real.sqrt 3)
        dsimp [P2] at h2
        exact h2.trans_eq (div_sqrt3_eq l n hn)
    · -- Downward sub-triangle (i+1,j), (i,j+1), (i+1,j+1).
      have hgt : 1 < x + y := lt_of_not_ge hxy
      have hmgtR : (1 : ℝ) < (m : ℝ) := lt_of_lt_of_le hgt hxy_le_m
      have hmgt : 1 < m := by exact_mod_cast hmgtR
      have hm2 : 2 ≤ m := by omega
      let P0 : V3 := sampleR n X0 X1 X2 ((i : ℝ) + 1) (j : ℝ)
      let P1 : V3 := sampleR n X0 X1 X2 (i : ℝ) ((j : ℝ) + 1)
      let P2 : V3 := sampleR n X0 X1 X2 ((i : ℝ) + 1) ((j : ℝ) + 1)
      have hP0idx : i + 1 + j ≤ n := by omega
      have hP1idx : i + (j + 1) ≤ n := by omega
      have hP2idx : i + 1 + (j + 1) ≤ n := by omega
      have hqP : q = bary P0 P1 P2 (1 - y) (1 - x) (x + y - 1) := by
        rw [hq_aff]
        dsimp [P0, P1, P2]
        rw [sampleR_eq_aff, sampleR_eq_aff, sampleR_eq_aff]
        ext k
        unfold bary aff vadd vscale vsub
        dsimp [x, y, u, v]
        field_simp [hn0]
        ring_nf
      have he01 : dsq P0 P1 ≤ (l / (n : ℝ)) ^ 2 := by
        rw [hs_sq]
        dsimp [P0, P1]
        rw [dsq_sample_diag n hn X0 X1 X2 (i : ℝ) (j : ℝ)]
        exact div_le_div_of_nonneg_right h12 (sq_nonneg (n : ℝ))
      have he02 : dsq P0 P2 ≤ (l / (n : ℝ)) ^ 2 := by
        rw [hs_sq, dsq_comm]
        dsimp [P0, P2]
        rw [dsq_sample_step_v n hn X0 X1 X2 ((i : ℝ) + 1) (j : ℝ)]
        exact div_le_div_of_nonneg_right h02 (sq_nonneg (n : ℝ))
      have he12 : dsq P1 P2 ≤ (l / (n : ℝ)) ^ 2 := by
        rw [hs_sq, dsq_comm]
        dsimp [P1, P2]
        rw [dsq_sample_step_u n hn X0 X1 X2 (i : ℝ) ((j : ℝ) + 1)]
        exact div_le_div_of_nonneg_right h01 (sq_nonneg (n : ℝ))
      have hcov := triangle_vertex_cover P0 P1 P2 (l / (n : ℝ)) hs_nonneg
          he01 he02 he12 (1 - y) (1 - x) (x + y - 1)
          (by linarith [le_of_lt hy1]) (by linarith [le_of_lt hx1]) (by linarith) (by ring)
      rw [← hqP] at hcov
      rcases hcov with h0 | h1 | h2
      · refine ⟨i + 1, j, hP0idx, ?_⟩
        push_cast
        change dist q (sampleR n X0 X1 X2 ((i : ℝ) + 1) (j : ℝ)) ≤ l / ((n : ℝ) * Real.sqrt 3)
        dsimp [P0] at h0
        exact h0.trans_eq (div_sqrt3_eq l n hn)
      · refine ⟨i, j + 1, hP1idx, ?_⟩
        push_cast
        change dist q (sampleR n X0 X1 X2 (i : ℝ) ((j : ℝ) + 1)) ≤ l / ((n : ℝ) * Real.sqrt 3)
        dsimp [P1] at h1
        exact h1.trans_eq (div_sqrt3_eq l n hn)
      · refine ⟨i + 1, j + 1, hP2idx, ?_⟩
        push_cast
        change dist q (sampleR n X0 X1 X2 ((i : ℝ) + 1) ((j : ℝ) + 1)) ≤ l / ((n : ℝ) * Real.sqrt 3)
        dsimp [P2] at h2
        exact h2.trans_eq (div_sqrt3_eq l n hn)

/-- The nearest-voxel snap of a world point `X`: `round(X/h)` coordinatewise,
    matching `tool_nearest_voxel` (`floor(p/h + 1/2)`) in the C code. -/
noncomputable def snapLattice (X : V3) (h : ℝ) : Vdb.Lattice :=
  fun k => Int.floor (X k / h + (1 : ℝ) / 2)

/-- The snapped seed in world coordinates. -/
noncomputable def seedWorld (X : V3) (h : ℝ) : V3 :=
  fun k => ((snapLattice X h k : ℤ) : ℝ) * h

/-- One coordinate of snapping differs from `X` by at most `h/2`. -/
lemma snap_coord (X : V3) (h : ℝ) (hh : 0 < h) (k : Fin 3) :
    |X k - ((snapLattice X h k : ℤ) : ℝ) * h| ≤ h / 2 := by
  let c : ℤ := Int.floor (X k / h + (1 : ℝ) / 2)
  have hfl : (c : ℝ) ≤ X k / h + (1 : ℝ) / 2 := by
    dsimp [c]
    exact Int.floor_le _
  have hlt : X k / h + (1 : ℝ) / 2 < (c : ℝ) + 1 := by
    dsimp [c]
    exact Int.lt_floor_add_one _
  have hlow : -(1 / 2 : ℝ) ≤ X k / h - (c : ℝ) := by linarith
  have hhigh : X k / h - (c : ℝ) ≤ (1 / 2 : ℝ) := by linarith
  have habs : |X k / h - (c : ℝ)| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨hlow, hhigh⟩
  have heq : X k - (c : ℝ) * h = h * (X k / h - (c : ℝ)) := by
    field_simp [ne_of_gt hh]
  change |X k - (c : ℝ) * h| ≤ h / 2
  rw [heq, abs_mul, abs_of_pos hh]
  have hm := mul_le_mul_of_nonneg_left habs (le_of_lt hh)
  nlinarith

/-- Snapping moves a point by at most half the voxel diagonal, `h·√3/2`. -/
lemma snap_bound (X : V3) (h : ℝ) (hh : 0 < h) :
    dist X (seedWorld X h) ≤ h * Real.sqrt 3 / 2 := by
  unfold dist dsq nsq vsub seedWorld
  have hcoord : ∀ k : Fin 3, |X k - ((snapLattice X h k : ℤ) : ℝ) * h| ≤ h / 2 :=
    fun k => snap_coord X h hh k
  have hdsq : (∑ k : Fin 3,
        (X k - ((snapLattice X h k : ℤ) : ℝ) * h) *
        (X k - ((snapLattice X h k : ℤ) : ℝ) * h)) ≤ 3 * (h / 2)^2 := by
    calc
      (∑ k : Fin 3,
          (X k - ((snapLattice X h k : ℤ) : ℝ) * h) *
          (X k - ((snapLattice X h k : ℤ) : ℝ) * h))
          = ∑ k : Fin 3, |X k - ((snapLattice X h k : ℤ) : ℝ) * h|^2 := by
              apply Finset.sum_congr rfl
              intro k hk
              calc
                (X k - ((snapLattice X h k : ℤ) : ℝ) * h) *
                    (X k - ((snapLattice X h k : ℤ) : ℝ) * h)
                    = (X k - ((snapLattice X h k : ℤ) : ℝ) * h) ^ 2 := by ring_nf
                _ = |X k - ((snapLattice X h k : ℤ) : ℝ) * h| ^ 2 := by rw [sq_abs]
      _ ≤ ∑ k : Fin 3, (h / 2)^2 := by
              apply Finset.sum_le_sum
              intro k hk
              have hh2 : 0 ≤ h / 2 := by nlinarith [hh]
              exact sq_le_sq.mpr (by simpa [abs_of_nonneg hh2] using hcoord k)
      _ = 3 * (h / 2)^2 := by
              simp [Finset.card_univ, Fintype.card_fin]
  have hsqrt := Real.sqrt_le_sqrt hdsq
  have hsimpl : Real.sqrt (3 * (h / 2)^2) = h * Real.sqrt 3 / 2 := by
    have hh2 : 0 ≤ h / 2 := by positivity
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_sq_eq_abs, abs_of_nonneg hh2]
    ring_nf
  exact hsqrt.trans_eq hsimpl

/-- The longest edge `l` bounds every squared edge by `l²`. -/
lemma edge_dsq_le (X0 X1 X2 : V3) :
    let l := max (dist X0 X1) (max (dist X0 X2) (dist X1 X2))
    dsq X0 X1 ≤ l^2 ∧ dsq X0 X2 ≤ l^2 ∧ dsq X1 X2 ≤ l^2 := by
  dsimp
  have hd0 : 0 ≤ dist X0 X1 := by unfold dist; exact Real.sqrt_nonneg _
  have hd1 : 0 ≤ dist X0 X2 := by unfold dist; exact Real.sqrt_nonneg _
  have hd2 : 0 ≤ dist X1 X2 := by unfold dist; exact Real.sqrt_nonneg _
  have hl : 0 ≤ max (dist X0 X1) (max (dist X0 X2) (dist X1 X2)) :=
    le_trans hd0 (le_max_left _ _)
  have h01 : dist X0 X1 ≤ max (dist X0 X1) (max (dist X0 X2) (dist X1 X2)) := le_max_left _ _
  have h02 : dist X0 X2 ≤ max (dist X0 X1) (max (dist X0 X2) (dist X1 X2)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h12 : dist X1 X2 ≤ max (dist X0 X1) (max (dist X0 X2) (dist X1 X2)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have sq_of_dist (a b : V3) (h : dist a b ≤ max (dist X0 X1) (max (dist X0 X2) (dist X1 X2))) :
      dsq a b ≤ (max (dist X0 X1) (max (dist X0 X2) (dist X1 X2)))^2 := by
    let M : ℝ := max (Real.sqrt (dsq X0 X1)) (max (Real.sqrt (dsq X0 X2)) (Real.sqrt (dsq X1 X2)))
    have hM : 0 ≤ M := le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
    have hle : Real.sqrt (dsq a b) ≤ M := by
      dsimp [M]
      unfold dist at h
      exact h
    change dsq a b ≤ M ^ 2
    have hs := Real.sq_sqrt (dsq_nonneg a b)
    have hsn : 0 ≤ Real.sqrt (dsq a b) := Real.sqrt_nonneg _
    nlinarith
  exact ⟨sq_of_dist X0 X1 h01, sq_of_dist X0 X2 h02, sq_of_dist X1 X2 h12⟩

/-- **`2h/√3` decomposition** used at the last step. -/
lemma two_h_over_sqrt3 (h : ℝ) : h / (2 * Real.sqrt 3) + h * Real.sqrt 3 / 2 = 2 * h / Real.sqrt 3 := by
  have hs3sq : Real.sqrt 3 ^ 2 = 3 := by
    norm_num [Real.sq_sqrt]
  have hs3mul : Real.sqrt 3 * Real.sqrt 3 = 3 := by nlinarith [hs3sq]
  field_simp [sqrt3_ne]
  rw [hs3sq]
  ring_nf

/-- **T-BAND-SEED-COVERAGE (main theorem).** For every `h > 0` and every
    (possibly degenerate) triangle, with `n = max 1 ⌈2l/h⌉` (`l` = longest
    edge), every convex combination of the triangle is within `2h/√3` of the
    snapped barycentric seed `h · round(p(i,j)/h)` for some grid index
    `i+j ≤ n`. This is exactly the `hcover` estimate of `Vdb.NarrowBand`,
    proved rather than assumed, with the constant `2/√3` unweakened. -/
theorem triangle_seed_coverage (X0 X1 X2 : V3) (h : ℝ) (hh : 0 < h) :
    let l := max (dist X0 X1) (max (dist X0 X2) (dist X1 X2))
    let n := max 1 (Nat.ceil (2 * l / h))
    ∀ a0 a1 a2 : ℝ, 0 ≤ a0 → 0 ≤ a1 → 0 ≤ a2 → a0 + a1 + a2 = 1 →
      ∃ i j : ℕ, i + j ≤ n ∧
        let p := sampleR n X0 X1 X2 (i : ℝ) (j : ℝ)
        dist (bary X0 X1 X2 a0 a1 a2) (seedWorld p h) ≤ 2 * h / Real.sqrt 3 := by
  dsimp only
  intro a0 a1 a2 ha0 ha1 ha2 hsum
  let l := max (dist X0 X1) (max (dist X0 X2) (dist X1 X2))
  let n := max 1 (Nat.ceil (2 * l / h))
  have hd0 : 0 ≤ dist X0 X1 := by unfold dist; exact Real.sqrt_nonneg _
  have hl : 0 ≤ l := le_trans hd0 (by dsimp [l]; exact le_max_left _ _)
  have hn : 0 < n := by dsimp [n]; omega
  obtain ⟨h01, h02, h12⟩ := edge_dsq_le X0 X1 X2
  have hceil : 2 * l / h ≤ (Nat.ceil (2 * l / h) : ℝ) := Nat.le_ceil _
  have hnceil : (Nat.ceil (2 * l / h) : ℝ) ≤ (n : ℝ) := by
    dsimp [n]
    exact_mod_cast (Nat.le_max_right 1 (Nat.ceil (2 * l / h)))
  have h2lh : 2 * l / h ≤ (n : ℝ) := hceil.trans hnceil
  have h2l_le : 2 * l ≤ (n : ℝ) * h := by
    have hm := mul_le_mul_of_nonneg_right h2lh (le_of_lt hh)
    field_simp [ne_of_gt hh] at hm
    nlinarith
  have hspacing : l / (n : ℝ) ≤ h / 2 := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    field_simp [ne_of_gt hnpos, ne_of_gt hh]
    nlinarith
  obtain ⟨i, j, hij, hsub⟩ := subdivision_cover X0 X1 X2 l hl n hn
      h01 h02 h12 a0 a1 a2 ha0 ha1 ha2 hsum
  refine ⟨i, j, hij, ?_⟩
  let p := sampleR n X0 X1 X2 (i : ℝ) (j : ℝ)
  rw [← div_sqrt3_eq l n hn] at hsub
  have hhalf : (h / (2 : ℝ)) / Real.sqrt 3 = h / ((2 : ℝ) * Real.sqrt 3) :=
    div_sqrt3_eq h 2 (by norm_num)
  have hnear : dist (bary X0 X1 X2 a0 a1 a2) p ≤ h / (2 * Real.sqrt 3) := by
    exact le_trans hsub ((div_le_div_of_nonneg_right hspacing (le_of_lt sqrt3_pos)).trans_eq hhalf)
  have hsnap : dist p (seedWorld p h) ≤ h * Real.sqrt 3 / 2 := snap_bound p h hh
  have htri : dist (bary X0 X1 X2 a0 a1 a2) (seedWorld p h) ≤
      dist (bary X0 X1 X2 a0 a1 a2) p + dist p (seedWorld p h) := by
    rw [dist_eq_edist, dist_eq_edist, dist_eq_edist]
    exact Vdb.edist_triangle (bary X0 X1 X2 a0 a1 a2) (seedWorld p h) p
  exact le_trans htri (by
    calc dist (bary X0 X1 X2 a0 a1 a2) p + dist p (seedWorld p h)
        ≤ h / (2 * Real.sqrt 3) + h * Real.sqrt 3 / 2 := add_le_add hnear hsnap
        _ = 2 * h / Real.sqrt 3 := two_h_over_sqrt3 h)

/-- The (finite) seed set generated by the C loop for one triangle, in voxel
    units (`h = 1`): the snapped voxels of all barycentric samples `i+j ≤ n`. -/
noncomputable def triangleSeeds (n : ℕ) (Y0 Y1 Y2 : V3) : Finset Vdb.Lattice :=
  (((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
      (fun ij => ij.1 + ij.2 ≤ n)).image
    (fun ij => snapLattice (sampleR n Y0 Y1 Y2 (ij.1 : ℝ) (ij.2 : ℝ)) 1)

/-- **`Vdb.NarrowBand.hcover` discharged for one triangle.** In voxel units,
    every convex combination of a triangle lies within `2/√3` of a seed voxel
    generated at spacing `l/n ≤ 1/2` (`n = max 1 ⌈2l⌉`, `l` the longest edge).
    For a closed triangle mesh take the union of `triangleSeeds` over all faces;
    this supplies exactly the hypothesis `band_complete` / `band_complete_tree`
    previously assumed. -/
theorem hcover_triangle (Y0 Y1 Y2 : V3) :
    let l := max (dist Y0 Y1) (max (dist Y0 Y2) (dist Y1 Y2))
    let n := max 1 (Nat.ceil (2 * l))
    ∀ a0 a1 a2 : ℝ, 0 ≤ a0 → 0 ≤ a1 → 0 ≤ a2 → a0 + a1 + a2 = 1 →
      ∃ s ∈ triangleSeeds n Y0 Y1 Y2,
        Vdb.edist (bary Y0 Y1 Y2 a0 a1 a2) (Vdb.embed s) ≤ 2 / Real.sqrt 3 := by
  dsimp only
  intro a0 a1 a2 ha0 ha1 ha2 hsum
  let l := max (dist Y0 Y1) (max (dist Y0 Y2) (dist Y1 Y2))
  let n := max 1 (Nat.ceil (2 * l))
  have hcov := triangle_seed_coverage Y0 Y1 Y2 1 (by norm_num) a0 a1 a2
      ha0 ha1 ha2 hsum
  dsimp only at hcov
  simp only [div_one] at hcov
  rcases hcov with ⟨i, j, hij, hle⟩
  let p := sampleR n Y0 Y1 Y2 (i : ℝ) (j : ℝ)
  let s : Vdb.Lattice := snapLattice p 1
  refine ⟨s, ?_, ?_⟩
  · unfold triangleSeeds
    apply Finset.mem_image.mpr
    refine ⟨(i, j), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · exact Finset.mem_range.mpr (by omega)
    · exact hij
  · have heq : seedWorld p 1 = Vdb.embed s := by
      ext k
      unfold seedWorld Vdb.embed
      ring
    have hdist : dist (bary Y0 Y1 Y2 a0 a1 a2) (seedWorld p 1) =
        Vdb.edist (bary Y0 Y1 Y2 a0 a1 a2) (Vdb.embed s) := by
      rw [dist_eq_edist, heq]
    rw [← hdist]
    simpa using hle

end Vdb.SeedCoverage
