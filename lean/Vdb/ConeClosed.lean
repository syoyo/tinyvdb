/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **A finitely generated pointed cone in a finite-dimensional real
  space is closed** — the missing ingredient of the exact closest-point
  cone expansion (`p − q = Σ λᵢ nᵢ`, `λᵢ ≥ 0`, for a closest point `q ∈ K`
  of a half-space intersection to `p`), which `Vdb/ConeExpansion.lean`
  could only prove up to taking the closure.

  Proof (classical): a point of the closure of `C = cone{vᵢ}` is a limit of
  combinations `uₙ = Σᵢ ℓₙᵢ vᵢ` with `ℓₙ ≥ 0`. Either the weight sums
  `Λₙ = Σᵢ ℓₙᵢ` are bounded — then a subsequence of coefficient tuples
  converges in the compact box `[0, M]^ι` to `λ ≥ 0`, and the continuous
  combination map gives `y = Σᵢ λᵢ vᵢ` — or `Λₙ → ∞` along a subsequence,
  in which case the normalized coefficients `μₙ = ℓₙ / Λₙ` live in the
  compact simplex `{μ ≥ 0, Σ μ = 1}`, a subsequence converges to `μ` with
  `Σ μᵢ vᵢ = 0` and `μ ≠ 0`, contradicting pointedness.

  Instantiated with the tight face normals of a half-space intersection
  with a (nonempty) interior — the tight normals are pointed (the witness
  interior point pairs strictly negatively with every tight normal) — this
  yields the exact expansion `p − q ∈ coneTight n b q`, the full
  closest-point cone theorem for the F16 sign rule.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.ConeExpansion
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousOn
import Mathlib.Analysis.Convex.Topology

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

open Classical
open Topology Filter

namespace Vdb

open scoped RealInnerProductSpace

/-! ### The combination map and the simplex -/

/-- The combination map `λ ↦ ∑ i, λ i • v i`. -/
noncomputable def conicComb {ι : Type*} [Fintype ι] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v : ι → F) : (ι → ℝ) → F :=
  fun ℓ => ∑ i, ℓ i • v i

theorem conicComb_apply {ι : Type*} [Fintype ι] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v : ι → F) (ℓ : ι → ℝ) :
    conicComb v ℓ = ∑ i, ℓ i • v i := rfl

theorem continuous_conicComb {ι : Type*} [Fintype ι] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (v : ι → F) : Continuous (conicComb v) := by
  apply continuous_finsetSum Finset.univ
  intro i _
  exact (continuous_apply i).smul continuous_const

/-- The standard simplex of weight tuples (`λᵢ ≥ 0`, `Σ λ = 1`). -/
def simplex {ι : Type*} [Fintype ι] [DecidableEq ι] : Set (ι → ℝ) :=
  {ℓ : ι → ℝ | ∀ i, 0 ≤ ℓ i} ∩ {ℓ : ι → ℝ | ∑ i, ℓ i = 1}

theorem isClosed_simplex {ι : Type*} [Fintype ι] [DecidableEq ι] : IsClosed (simplex (ι := ι)) := by
  have h1 : IsClosed {ℓ : ι → ℝ | ∀ i, 0 ≤ ℓ i} := by
    have h : ⋂ i, {ℓ : ι → ℝ | 0 ≤ ℓ i} = {ℓ : ι → ℝ | ∀ i, 0 ≤ ℓ i} :=
      Set.iInter_ofPred _
    rw [← h]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {ℓ : ι → ℝ | ∑ i, ℓ i = 1} :=
    isClosed_eq (continuous_finsetSum Finset.univ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

theorem simplex_subset_Icc {ι : Type*} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℝ}
    (hℓ : ℓ ∈ simplex) (i : ι) :
    ℓ i ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 := hℓ.1 i
  have hle : ℓ i ≤ 1 := by
    have hsum := hℓ.2
    have hle' : ℓ i ≤ ∑ j, ℓ j :=
      Finset.single_le_sum (fun j _ => hℓ.1 j) (Finset.mem_univ i)
    rwa [hsum] at hle'
  exact ⟨h0, hle⟩

theorem isCompact_simplex {ι : Type*} [Fintype ι] [DecidableEq ι] : IsCompact (simplex (ι := ι)) := by
  have hbox : IsCompact (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcl : IsClosed (simplex (ι := ι)) := isClosed_simplex (ι := ι)
  refine hbox.of_isClosed_subset hcl ?_
  intro ℓ hℓ i _
  have hi := hℓ.1 i
  have hsum := hℓ.2
  have hle : ℓ i ≤ 1 := by
    have hle' : ℓ i ≤ ∑ j, ℓ j :=
      Finset.single_le_sum (fun j _ => hℓ.1 j) (Finset.mem_univ i)
    rwa [hsum] at hle'
  exact ⟨hi, hle⟩

/-! ### Sequences and subsequences of coefficient tuples -/

theorem closure_range_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : ℕ → ι → ℝ}
    (h0 : ∀ n i, 0 ≤ u n i) {a : ι → ℝ}
    (ha : a ∈ closure (Set.range u)) :
    ∀ i, 0 ≤ a i := by
  have hclosed : IsClosed {ℓ : ι → ℝ | ∀ i, 0 ≤ ℓ i} := by
    have h : ⋂ i, {ℓ : ι → ℝ | 0 ≤ ℓ i} = {ℓ : ι → ℝ | ∀ i, 0 ≤ ℓ i} :=
      Set.iInter_ofPred _
    rw [← h]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hsub : Set.range u ⊆ {ℓ : ι → ℝ | ∀ i, 0 ≤ ℓ i} := by
    intro ℓ hℓ
    obtain ⟨n, rfl⟩ := hℓ
    exact fun i => h0 n i
  exact (closure_minimal hsub hclosed) ha


/-! ### The fast-enough subsequence of an unbounded weight sequence -/

/-- From an unbounded weight sequence `Λ n = Σ i, ℓ n i` (`ℓ ≥ 0`) one can
    extract a strictly increasing `φ` with `k < Λ (φ k)` for every `k`. -/
theorem exists_fast_subseq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ℓ : ℕ → ι → ℝ}
    (hℓ0 : ∀ n i, 0 ≤ ℓ n i)
    (hbd : ¬ Bornology.IsBounded (Set.range ℓ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto φ atTop atTop ∧
      ∀ k : ℕ, (k : ℝ) < ∑ i, ℓ (φ k) i := by
  -- unbounded: for every real R there is an index with R < Λ n
  have hunbd : ∀ R : ℝ, ∃ n : ℕ, R < ∑ i, ℓ n i := by
    intro R
    by_contra hc
    push Not at hc
    refine hbd ?_
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|R| + 1, fun x hx => ?_⟩
    obtain ⟨n, rfl⟩ := hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hn0 : ∀ i, 0 ≤ ℓ n i := hℓ0 n
    have hnn : ‖ℓ n‖ ≤ ∑ i, ℓ n i := by
      rw [pi_norm_le_iff_of_nonneg (by exact Finset.sum_nonneg fun i _ => hn0 i)]
      intro i
      calc ‖ℓ n i‖ = ℓ n i := abs_of_nonneg (hn0 i)
        _ ≤ ∑ j, ℓ n j :=
          Finset.single_le_sum (fun j _ => hn0 j) (Finset.mem_univ i)
    have hsumR : ∑ i, ℓ n i ≤ R := hc n
    have h2 : ‖ℓ n‖ ≤ |R| + 1 := by
      have h3 : ‖ℓ n‖ ≤ R := hnn.trans hsumR
      by_cases hR : 0 ≤ R
      · rw [abs_of_nonneg hR]; nlinarith
      · have hR' : R < 0 := lt_of_not_ge hR
        rw [abs_of_neg hR']; nlinarith
    exact h2
  -- strengthened: the witness index can be pushed past any N
  have hunbd' : ∀ M : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ M < ∑ i, ℓ n i := by
    intro M N
    have hfin : ∃ C : ℝ, ∀ j : ℕ, j ≤ N → ∑ i, ℓ j i ≤ C := by
      refine ⟨(Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ N)⟩
            (fun j => ∑ i, ℓ j i), fun j hj => ?_⟩
      exact Finset.le_sup' (fun j => ∑ i, ℓ j i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    obtain ⟨C, hC⟩ := hfin
    obtain ⟨n, hn⟩ := hunbd (max M C)
    have hnN : N ≤ n := by
      by_contra hcon
      have hn' : n < N := lt_of_not_ge hcon
      have hnC : ∑ i, ℓ n i ≤ C := hC n (le_of_lt hn')
      nlinarith [hn, le_max_left M C, le_max_right M C]
    exact ⟨n, hnN, lt_of_le_of_lt (le_max_left M C) hn⟩
  -- build φ by well-founded recursion
  choose nchoose hnchoose using hunbd'
  let φ : ℕ → ℕ := fun k =>
    Nat.rec (motive := fun _ => ℕ) (nchoose 0 0)
      (fun j ih => nchoose (j + 1 : ℝ) (ih + 1)) k
  have hφ0 : φ 0 = nchoose 0 0 := rfl
  have hφsucc : ∀ k : ℕ, φ (k + 1) = nchoose (k + 1 : ℝ) (φ k + 1) := fun k => rfl
  have hφstep : ∀ k : ℕ, φ k < φ (k + 1) := fun k => by
    rw [hφsucc k]
    exact (hnchoose (k + 1 : ℝ) (φ k + 1)).1
  have hφmono : StrictMono φ := strictMono_nat_of_lt_succ hφstep
  have hφtop : Tendsto φ atTop atTop :=
    tendsto_atTop_mono (fun n => hφmono.id_le n) tendsto_id
  refine ⟨φ, hφmono, hφtop, fun k => ?_⟩
  cases k with
  | zero => rw [hφ0]; exact_mod_cast (hnchoose 0 0).2
  | succ k => rw [hφsucc k]; exact_mod_cast (hnchoose (k + 1 : ℝ) (φ k + 1)).2

/-! ### Closedness of a pointed, finitely generated cone -/

/-- **A finitely generated pointed cone is closed** (in a finite-dimensional
    real space). The proof is the classical normalization argument: a
    sequence in the cone, either its weight sums stay bounded (then a
    subsequence of coefficient tuples converges to a nonneg limit whose
    combination is the limit point) or they blow up (then the normalized
    tuples live in the compact simplex, a subsequence converges to a nonzero
    zero combination, contradicting pointedness). -/
theorem isClosed_coneGen_of_pointed {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {v : ι → F} (hpoint : ∀ ℓ : ι → ℝ, (∀ i, 0 ≤ ℓ i) →
      ∑ i, ℓ i • v i = 0 → ∀ i, ℓ i = 0) :
    IsClosed (coneGen v) := by
  rw [← closure_subset_iff_isClosed]
  intro y hy
  by_cases hy0 : y = 0
  · rw [hy0]; exact zero_mem_coneGen v
  obtain ⟨w, hw, hwy⟩ := mem_closure_iff_seq_limit.mp hy
  choose ℓ hℓ0 hℓ using hw
  have hΛ0 : ∀ n, 0 ≤ ∑ i, ℓ n i := fun n => Finset.sum_nonneg fun i _ => hℓ0 n i
  by_cases hbd : Bornology.IsBounded (Set.range ℓ)
  · /- Bounded weights: extract a convergent subsequence of tuples. -/
    obtain ⟨a, ha, φ, hφmono, hconv⟩ := tendsto_subseq_of_bounded hbd (fun n => Set.mem_range_self n)
    have hφtop : Tendsto φ atTop atTop :=
      tendsto_atTop_mono (fun n => hφmono.id_le n) tendsto_id
    have hwφ : Tendsto (w ∘ φ) atTop (𝓝 y) := hwy.comp hφtop
    have ha0 : ∀ i, 0 ≤ a i := closure_range_nonneg hℓ0 ha
    have hwφ' : Tendsto (fun n => conicComb v (ℓ (φ n))) atTop (𝓝 y) := by
      have hu : w ∘ φ = fun n => conicComb v (ℓ (φ n)) := by
        funext n
        simp [Function.comp, conicComb, hℓ (φ n)]
      rwa [hu] at hwφ
    have hconic : Tendsto (fun n => conicComb v (ℓ (φ n))) atTop (𝓝 (conicComb v a)) :=
      (continuous_conicComb v).tendsto _ |>.comp hconv
    have hunique := tendsto_nhds_unique hwφ' hconic
    exact ⟨a, ha0, hunique⟩
  · /- Unbounded weights: normalize into the simplex. -/
    obtain ⟨φ, hφmono, hφtop, hφΛ⟩ := exists_fast_subseq hℓ0 hbd
    have hΛpos : ∀ n, 0 < ∑ i, ℓ (φ n) i := fun n => lt_of_le_of_lt (Nat.cast_nonneg n) (hφΛ n)
    have hμ : ∀ n, (fun i => (∑ i, ℓ (φ n) i)⁻¹ * ℓ (φ n) i) ∈ simplex := by
      intro n
      refine ⟨fun i => mul_nonneg (inv_nonneg.mpr (hΛ0 (φ n))) (hℓ0 (φ n) i), ?_⟩
      have hne : ∑ i, ℓ (φ n) i ≠ 0 := ne_of_gt (hΛpos n)
      show ∑ i, (∑ i, ℓ (φ n) i)⁻¹ * ℓ (φ n) i = 1
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ hne
    obtain ⟨a, ha, φ', hφ'mono, hconv⟩ :=
      tendsto_subseq_of_bounded isCompact_simplex.isBounded (fun n => hμ n)
    have hconv' : Tendsto (fun n => fun i => (∑ i, ℓ (φ (φ' n)) i)⁻¹ * ℓ (φ (φ' n)) i)
        atTop (𝓝 a) := hconv
    have hassimplex : a ∈ simplex := isClosed_simplex.closure_subset ha
    have hφ'top : Tendsto φ' atTop atTop :=
      tendsto_atTop_mono (fun n => hφ'mono.id_le n) tendsto_id
    have hφφ' : Tendsto (φ ∘ φ') atTop atTop :=
      tendsto_atTop_mono (fun k => le_trans (hφ'mono.id_le k) (hφmono.id_le (φ' k))) tendsto_id
    have hwy' : Tendsto (w ∘ (φ ∘ φ')) atTop (𝓝 y) := hwy.comp hφφ'
    have hΛ' : Tendsto (fun n => ∑ i, ℓ (φ (φ' n)) i) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => (φ' n : ℝ)) atTop atTop :=
        Tendsto.comp tendsto_natCast_atTop_atTop hφ'top
      exact tendsto_atTop_mono (fun n => le_of_lt (hφΛ (φ' n))) h1
    have hbdd : ∀ᶠ n in atTop, ‖w (φ (φ' n))‖ ≤ ‖y‖ + 1 := by
      have hnorm : Tendsto (fun n => ‖w (φ (φ' n))‖) atTop (𝓝 ‖y‖) :=
        (continuous_norm.tendsto _).comp hwy'
      exact hnorm.eventually (Iic_mem_nhds (lt_add_one _))
    have h2 : Tendsto (fun n => conicComb v (fun i => (∑ i, ℓ (φ (φ' n)) i)⁻¹ * ℓ (φ (φ' n)) i))
        atTop (𝓝 0) := by
      have hcomb : ∀ n, conicComb v (fun i => (∑ i, ℓ (φ (φ' n)) i)⁻¹ * ℓ (φ (φ' n)) i)
          = (∑ i, ℓ (φ (φ' n)) i)⁻¹ • w (φ (φ' n)) := by
        intro n
        unfold conicComb
        rw [hℓ (φ (φ' n))]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul]
      have hfun : (fun n => conicComb v (fun i => (∑ i, ℓ (φ (φ' n)) i)⁻¹ * ℓ (φ (φ' n)) i))
          = fun n => (∑ i, ℓ (φ (φ' n)) i)⁻¹ • w (φ (φ' n)) := funext hcomb
      rw [hfun]
      -- the inverse-scaled sequence tends to 0 (via its norm)
      have hnorm : Tendsto (fun n => ‖(∑ i, ℓ (φ (φ' n)) i)⁻¹ • w (φ (φ' n))‖) atTop (𝓝 0) := by
        have hle : ∀ᶠ n in atTop, ‖(∑ i, ℓ (φ (φ' n)) i)⁻¹ • w (φ (φ' n))‖ ≤ (‖y‖ + 1) * (∑ i, ℓ (φ (φ' n)) i)⁻¹ := by
          filter_upwards [hbdd] with n hn
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hΛ0 (φ (φ' n)))),
            mul_comm]
          exact mul_le_mul_of_nonneg_right hn (inv_nonneg.mpr (hΛ0 (φ (φ' n))))
        have hg : Tendsto (fun n => (‖y‖ + 1) * (∑ i, ℓ (φ (φ' n)) i)⁻¹) atTop (𝓝 0) := by
          simpa using tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hΛ')
        exact squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) hle hg
      exact (tendsto_zero_iff_norm_tendsto_zero.mpr hnorm)
    have hconic : Tendsto (fun n => conicComb v (fun i => (∑ i, ℓ (φ (φ' n)) i)⁻¹ * ℓ (φ (φ' n)) i))
        atTop (𝓝 (conicComb v a)) :=
      (continuous_conicComb v).tendsto _ |>.comp hconv'
    have hunique := tendsto_nhds_unique hconic h2
    have h0 : ∑ i, a i • v i = 0 := hunique
    have hpoint0 := hpoint a hassimplex.1 h0
    have hne1 : ∑ i, a i = 1 := hassimplex.2
    have : (0:ℝ) = 1 := by
      rw [← hne1]
      rw [Finset.sum_congr rfl (g := fun _ => (0 : ℝ)) (fun i _ => hpoint0 i)]
      exact Finset.sum_const_zero.symm
    norm_num at this

/-- The tight normals of a half-space intersection with nonempty interior
    positively span no zero combination: an interior point pairs strictly
    negatively with every tight normal. -/
theorem tightNormals_pointed {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ι → F} {b : ι → ℝ} {q : F}
    (hint : ∃ r ∈ halfSpaces n b, ∀ i, ⟪n i, r⟫ < b i) :
    ∀ ℓ : {i // Tight n b q i} → ℝ, (∀ i, 0 ≤ ℓ i) →
      ∑ i, ℓ i • n (i : ι) = 0 → ∀ i, ℓ i = 0 := by
  intro ℓ hℓ0 hsum i0
  obtain ⟨r, hr, hr_int⟩ := hint
  have key : ∀ j : {i // Tight n b q i}, ⟪n j.1, r - q⟫ < 0 := by
    intro j
    have h1 : ⟪n j.1, r⟫ < b j.1 := hr_int j.1
    have h2 : ⟪n j.1, q⟫ = b j.1 := j.2
    have h3 : ⟪n j.1, r - q⟫ = ⟪n j.1, r⟫ - ⟪n j.1, q⟫ := by rw [inner_sub_right]
    rw [h3, h2]
    linarith
  have inner_sum' : ∀ s : Finset {i // Tight n b q i},
      ⟪∑ i ∈ s, ℓ i • n (i : ι), r - q⟫ = ∑ i ∈ s, ℓ i * ⟪n (i : ι), r - q⟫ := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.sum_insert has, inner_add_left, ih, real_inner_smul_left,
        Finset.sum_insert has]
  have h1 : ∑ i : {i // Tight n b q i}, ℓ i * ⟪n (i : ι), r - q⟫ = 0 := by
    rw [← inner_sum' Finset.univ, hsum]
    simp
  have h2 : ∀ i ∈ Finset.univ, ℓ i * ⟪n (i : ι), r - q⟫ ≤ 0 := by
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (hℓ0 i) (le_of_lt (key i))
  have hzero : ∀ i ∈ Finset.univ, ℓ i * ⟪n (i : ι), r - q⟫ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos h2).mp h1
  have h4 := hzero i0 (Finset.mem_univ i0)
  rcases mul_eq_zero.mp h4 with h | h
  · exact h
  · exact absurd h (ne_of_lt (key i0))

/-- **Closest-point application (exact)**: for a closest point `q ∈ K` to
    `p` of a half-space intersection whose interior is nonempty, the
    direction `p − q` is a finite nonneg combination of the tight face
    normals at `q` — the exact closest-point cone expansion `p − q = Σ λᵢ nᵢ`
    (`λᵢ ≥ 0`) for the F16 sign rule. -/
theorem farkas_closest_direction_exact {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {n : ι → F} {b : ι → ℝ} {p q : F}
    (hq : q ∈ halfSpaces n b)
    (hint : ∃ r ∈ halfSpaces n b, ∀ i, ⟪n i, r⟫ < b i)
    (hm : ‖p - q‖ = ⨅ w : (halfSpaces n b), ‖p - w‖) :
    p - q ∈ coneGen (tightNormals n b q) := by
  have hclosed : IsClosed (coneGen (tightNormals n b q)) :=
    isClosed_coneGen_of_pointed (tightNormals_pointed hint)
  have hmem := farkas_closest_direction hq hm
  change p - q ∈ closure (coneGen (tightNormals n b q)) at hmem
  rw [hclosed.closure_eq] at hmem
  exact hmem

end Vdb
