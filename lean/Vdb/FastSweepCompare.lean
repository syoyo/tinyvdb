/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  A-section: the super-solution / comparison-principle half of T-FS-FIX and
  the fixed-point system of the (eight-direction) fast sweeping schedule.

  This module is the comparison half that was documented as a wall in
  `VERIFICATION.md` (the subsolution half is `Vdb.TreeSweep.fixedPoint_subsolution`).
  It proves everything below with no new axioms and no proof holes:

  * `godunov_mono3` - the landed Godunov solve is jointly monotone on sorted
    triples, proved WITHOUT branch analysis from `godunov_spec` + the strict
    growth of the residual `g x = Σ max(x-u,0)²` on `[a, ∞)`. In particular
    this supplies the missing "monotone in the middle argument" lemma that
    the local theory in `Vdb.Godunov` did not carry.
  * `eikonalRelax_coe_eq_eikonalR` - the landed `WithTop` relaxation
    `Vdb.EikonalTop.eikonalRelax` on finite neighbour triples IS the finite
    solve `eikonalR` (sort + `godunov`), via the idempotence of the internal
    three-way sort.
  * `eikonalR_mono` / `eikonalR_spec` - the concrete relaxation is monotone
    in its three inputs and its value solves the exact discrete Eikonal
    equation.
  * `comparison_iterate` - the abstract comparison principle for the landed
    `Vdb.FastSweep.sweepStep` / `sweepIter`: monotone relaxation + a
    sub-fixed point `u` below the initial data ⟹ every iterate stays above
    `u`; hence a fixed point **reached** by the sweep dominates `u`
    (`comparison_fixedPoint_super`). This is the super-solution half of
    T-FS-FIX, conditional only on the sweep reaching its fixed point.
  * `gsPass_fixed_of_solution` / `sweepStep_fixed_of_solution` - the exact
    discrete solution is a fixed point of EVERY Gauss-Seidel visit schedule
    (in particular all eight Zhao directions) and of the simultaneous step.
  * `treeRelax_mono_of_finite` - the same comparison input for the landed
    `Vdb.TreeSweep.treeRelax`, conditional on the stencil returning finite
    triples and being monotone (both immediate for the min-neighbour stencil).

  Still NOT proved (the honest remaining wall): that the eight-direction
  Gauss-Seidel iteration actually reaches that fixed point from the
  initialization (Zhao 2005). `Vdb.FastSweep.sweepIter_big_steps_card` gives
  finite termination only to within `tol > 0`; exact convergence needs the
  semi-discrete theory. This module does not weaken any existing theorem.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.TreeSweep
import Mathlib.Tactic
import Mathlib.Data.List.Basic

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Vdb

noncomputable section

/-! ### Strict growth of the Godunov residual -/

/-- The scalar residual of the discrete Eikonal equation, as a function of
    the trial value `x` at fixed upwind values `a,b,c`. -/
def godunovResidual (a b c x : ℝ) : ℝ :=
  max (x - a) 0 ^ 2 + max (x - b) 0 ^ 2 + max (x - c) 0 ^ 2

/-- The residual is strictly increasing on `[a, ∞)`: the first (smallest-upwind)
    term already grows strictly. -/
theorem godunovResidual_strict {a b c x y : ℝ} (hax : a ≤ x) (hxy : x < y) :
    godunovResidual a b c x < godunovResidual a b c y := by
  unfold godunovResidual
  have hxa : 0 ≤ x - a := by linarith
  have hya : 0 ≤ y - a := by linarith
  have h1 : max (x - a) 0 ^ 2 < max (y - a) 0 ^ 2 := by
    rw [max_eq_left hxa, max_eq_left hya]
    nlinarith
  have hmono (u : ℝ) : max (x - u) 0 ≤ max (y - u) 0 := by
    exact max_le_max (by linarith) (le_refl 0)
  have hsq (A B : ℝ) (hAB : A ≤ B) (hA : 0 ≤ A) : A ^ 2 ≤ B ^ 2 := by
    have hprod : 0 ≤ A * (B - A) := mul_nonneg hA (sub_nonneg.mpr hAB)
    nlinarith [hprod, sq_nonneg (B - A)]
  have h2 : max (x - b) 0 ^ 2 ≤ max (y - b) 0 ^ 2 :=
    hsq _ _ (hmono b) (le_max_right _ _)
  have h3 : max (x - c) 0 ^ 2 ≤ max (y - c) 0 ^ 2 :=
    hsq _ _ (hmono c) (le_max_right _ _)
  linarith

/-- Raising any upwind value lowers the residual at every trial value. -/
theorem godunovResidual_mono_inputs {a b c a' b' c' x : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    godunovResidual a' b' c' x ≤ godunovResidual a b c x := by
  unfold godunovResidual
  have hmono (u u' : ℝ) (hu : u ≤ u') : max (x - u') 0 ≤ max (x - u) 0 := by
    exact max_le_max (by linarith) (le_refl 0)
  have hsq (A B : ℝ) (hAB : A ≤ B) (hA : 0 ≤ A) : A ^ 2 ≤ B ^ 2 := by
    have hprod : 0 ≤ A * (B - A) := mul_nonneg hA (sub_nonneg.mpr hAB)
    nlinarith [hprod, sq_nonneg (B - A)]
  have h1 : max (x - a') 0 ^ 2 ≤ max (x - a) 0 ^ 2 :=
    hsq _ _ (hmono a a' ha) (le_max_right _ _)
  have h2 : max (x - b') 0 ^ 2 ≤ max (x - b) 0 ^ 2 :=
    hsq _ _ (hmono b b' hb) (le_max_right _ _)
  have h3 : max (x - c') 0 ^ 2 ≤ max (x - c) 0 ^ 2 :=
    hsq _ _ (hmono c c' hc) (le_max_right _ _)
  linarith

/-! ### Joint monotonicity of the Godunov solve on sorted triples -/

/-- **Monotonicity in all three upwind arguments at once.** No branch case
    split is required: `godunov_spec` identifies the value as the unique root
    of the residual on `[a,∞)`, and the residual is strictly increasing there
    and decreasing in every upwind input. This supplies the middle-argument
    monotonicity that `Vdb.Godunov` did not carry. -/
theorem godunov_mono3 {a b c a' b' c' h : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hab' : a' ≤ b') (hbc' : b' ≤ c')
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hh : 0 ≤ h) :
    godunov a b c h ≤ godunov a' b' c' h := by
  set x := godunov a b c h with hxdef
  set y := godunov a' b' c' h with hydef
  have hxspec : godunovResidual a b c x = h ^ 2 := by
    unfold godunovResidual
    rw [hxdef]
    exact godunov_spec hab hbc hh
  have hyspec : godunovResidual a' b' c' y = h ^ 2 := by
    unfold godunovResidual
    rw [hydef]
    exact godunov_spec hab' hbc' hh
  have hnonneg_div (u : ℝ) : 0 ≤ h / Real.sqrt u := by
    exact div_nonneg hh (Real.sqrt_nonneg _)
  have hxa : a ≤ x := by
    rw [hxdef]
    have hlo := godunov_lo hab hbc hh
    linarith [hnonneg_div 3]
  have hya : a' ≤ y := by
    rw [hydef]
    have hlo := godunov_lo hab' hbc' hh
    linarith [hnonneg_div 3]
  by_contra hnot
  have hyx : y < x := not_le.mp hnot
  have hgx : godunovResidual a' b' c' x ≤ h ^ 2 := by
    calc godunovResidual a' b' c' x ≤ godunovResidual a b c x :=
          godunovResidual_mono_inputs ha hb hc
      _ = h ^ 2 := hxspec
  have hstrict : godunovResidual a' b' c' y < godunovResidual a' b' c' x :=
    godunovResidual_strict (a := a') (b := b') (c := c') (x := y) (y := x)
      (by linarith) hyx
  rw [hyspec] at hstrict
  linarith

/-! ### WithTop scaffolding: sorting is idempotent and commutes with coe -/

/-- The lower lattice bound of the sorted triple. -/
theorem realLo_le_realMid (a b c : ℝ) :
    min (min a b) c ≤ max (max (min a b) (min a c)) (min b c) := by
  exact le_trans (min_le_left (min a b) c)
    (le_trans (le_max_left (min a b) (min a c))
      (le_max_left (max (min a b) (min a c)) (min b c)))

/-- The upper lattice bound of the sorted triple. -/
theorem realMid_le_realHi (a b c : ℝ) :
    max (max (min a b) (min a c)) (min b c) ≤ max (max a b) c := by
  apply max_le
  · apply max_le
    · exact le_trans (le_trans (min_le_left a b) (le_max_left a b)) (le_max_left (max a b) c)
    · exact le_trans (le_trans (min_le_left a c) (le_max_left a b)) (le_max_left (max a b) c)
  · exact le_trans (le_trans (min_le_left b c) (le_max_right a b)) (le_max_left (max a b) c)

/-- Sorting a `WithTop` triple is idempotent: lo. -/
theorem eikonalLo_idem (a b c : WithTop ℝ) :
    eikonalLo (eikonalLo a b c) (eikonalMid a b c) (eikonalHi a b c) =
      eikonalLo a b c := by
  unfold eikonalLo eikonalMid eikonalHi
  have h1 : min (min a b) c ≤ max (max (min a b) (min a c)) (min b c) := by
    exact le_trans (min_le_left (min a b) c)
      (le_trans (le_max_left (min a b) (min a c))
        (le_max_left (max (min a b) (min a c)) (min b c)))
  have h2 : min (min a b) c ≤ max (max a b) c := by
    exact le_trans (min_le_left (min a b) c)
      (le_trans (le_trans (min_le_left a b) (le_max_left a b)) (le_max_left (max a b) c))
  rw [min_eq_left h1, min_eq_left h2]

/-- Sorting a `WithTop` triple is idempotent: hi. -/
theorem eikonalHi_idem (a b c : WithTop ℝ) :
    eikonalHi (eikonalLo a b c) (eikonalMid a b c) (eikonalHi a b c) =
      eikonalHi a b c := by
  unfold eikonalHi eikonalLo eikonalMid
  have h1 : min (min a b) c ≤ max (max a b) c := by
    exact le_trans (min_le_left (min a b) c)
      (le_trans (le_trans (min_le_left a b) (le_max_left a b)) (le_max_left (max a b) c))
  have h2 : max (max (min a b) (min a c)) (min b c) ≤ max (max a b) c := by
    apply max_le
    · apply max_le
      · exact le_trans (le_trans (min_le_left a b) (le_max_left a b)) (le_max_left (max a b) c)
      · exact le_trans (le_trans (min_le_left a c) (le_max_left a b)) (le_max_left (max a b) c)
    · exact le_trans (le_trans (min_le_left b c) (le_max_right a b)) (le_max_left (max a b) c)
  rw [max_eq_right (max_le h1 h2)]

/-- Sorting a `WithTop` triple is idempotent: mid. -/
theorem eikonalMid_idem (a b c : WithTop ℝ) :
    eikonalMid (eikonalLo a b c) (eikonalMid a b c) (eikonalHi a b c) =
      eikonalMid a b c := by
  unfold eikonalMid eikonalLo eikonalHi
  have hLM : min (min a b) c ≤ max (max (min a b) (min a c)) (min b c) := by
    exact le_trans (min_le_left (min a b) c)
      (le_trans (le_max_left (min a b) (min a c))
        (le_max_left (max (min a b) (min a c)) (min b c)))
  have hLH : min (min a b) c ≤ max (max a b) c := by
    exact le_trans (min_le_left (min a b) c)
      (le_trans (le_trans (min_le_left a b) (le_max_left a b)) (le_max_left (max a b) c))
  have hMH : max (max (min a b) (min a c)) (min b c) ≤ max (max a b) c := by
    apply max_le
    · apply max_le
      · exact le_trans (le_trans (min_le_left a b) (le_max_left a b)) (le_max_left (max a b) c)
      · exact le_trans (le_trans (min_le_left a c) (le_max_left a b)) (le_max_left (max a b) c)
    · exact le_trans (le_trans (min_le_left b c) (le_max_right a b)) (le_max_left (max a b) c)
  rw [min_eq_left hLM, min_eq_left hLH, min_eq_left hMH, max_self, max_eq_right hLM]

/-- `eikonalRelax` depends on its inputs only through their sorted triple. -/
theorem eikonalRelax_eq_sorted_inputs (a b c : WithTop ℝ) (h : ℝ) :
    eikonalRelax a b c h =
      eikonalRelax (eikonalLo a b c) (eikonalMid a b c) (eikonalHi a b c) h := by
  unfold eikonalRelax
  rw [eikonalLo_idem, eikonalMid_idem, eikonalHi_idem]

/-- The three sorting helpers commute with finite coercion. -/
theorem eikonalLo_coe (a b c : ℝ) :
    eikonalLo (a : WithTop ℝ) (b : WithTop ℝ) (c : WithTop ℝ) =
      (min (min a b) c : WithTop ℝ) := by
  simp [eikonalLo]

theorem eikonalMid_coe (a b c : ℝ) :
    eikonalMid (a : WithTop ℝ) (b : WithTop ℝ) (c : WithTop ℝ) =
      (max (max (min a b) (min a c)) (min b c) : WithTop ℝ) := by
  simp [eikonalMid]

theorem eikonalHi_coe (a b c : ℝ) :
    eikonalHi (a : WithTop ℝ) (b : WithTop ℝ) (c : WithTop ℝ) =
      (max (max a b) c : WithTop ℝ) := by
  simp [eikonalHi]

/-! ### The finite solve `eikonalR` and its bridge to `eikonalRelax` -/

/-- The relaxation on finite upwind values: sort the triple, then apply the
    landed Godunov solve. -/
def eikonalR (a b c h : ℝ) : ℝ :=
  let lo := min (min a b) c
  let mid := max (max (min a b) (min a c)) (min b c)
  let hi := max (max a b) c
  godunov lo mid hi h

/-- `eikonalR` is monotone in all three upwind values (the comparison principle's
    local hypothesis). -/
theorem eikonalR_mono {a b c a' b' c' h : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hh : 0 ≤ h) :
    eikonalR a b c h ≤ eikonalR a' b' c' h := by
  unfold eikonalR
  dsimp only
  apply godunov_mono3
  · exact realLo_le_realMid a b c
  · exact realMid_le_realHi a b c
  · exact realLo_le_realMid a' b' c'
  · exact realMid_le_realHi a' b' c'
  · exact min_le_min (min_le_min ha hb) hc
  · exact max_le_max (max_le_max (min_le_min ha hb) (min_le_min ha hc)) (min_le_min hb hc)
  · exact max_le_max (max_le_max ha hb) hc
  · exact hh

/-- The value returned by `eikonalR` solves the exact discrete Eikonal
    equation at the sorted triple. -/
theorem eikonalR_spec (a b c h : ℝ) (hh : 0 ≤ h) :
    let lo := min (min a b) c
    let mid := max (max (min a b) (min a c)) (min b c)
    let hi := max (max a b) c
    max (eikonalR a b c h - lo) 0 ^ 2 + max (eikonalR a b c h - mid) 0 ^ 2 +
      max (eikonalR a b c h - hi) 0 ^ 2 = h ^ 2 := by
  dsimp only
  unfold eikonalR
  dsimp only
  exact godunov_spec (realLo_le_realMid a b c) (realMid_le_realHi a b c) hh

/-! ### The `WithTop` ↔ finite bridge -/

set_option maxHeartbeats 800000 in
/-- The landed `WithTop` relaxation agrees with the finite `eikonalR` solve on
    finite upwind triples. The proof routes through the already-landed
    sorted-input reduction and `eikonalRelax_eq_godunov`, so no branch analysis
    on nested `WithTop` arithmetic is needed: the only `⊤` branches of
    `eikonalRelax` are unreachable for finite inputs. -/
theorem eikonalRelax_coe_eq_eikonalR (a b c h : ℝ) :
    eikonalRelax (some a) (some b) (some c) h = some (eikonalR a b c h) := by
  let lo := min (min a b) c
  let mid := max (max (min a b) (min a c)) (min b c)
  let hi := max (max a b) c
  have hlo : eikonalLo (some a) (some b) (some c) = (lo : WithTop ℝ) := by
    simpa [lo, WithTop.some_eq_coe] using (eikonalLo_coe a b c)
  have hmid : eikonalMid (some a) (some b) (some c) = (mid : WithTop ℝ) := by
    simpa [mid, WithTop.some_eq_coe] using (eikonalMid_coe a b c)
  have hhi : eikonalHi (some a) (some b) (some c) = (hi : WithTop ℝ) := by
    simpa [hi, WithTop.some_eq_coe] using (eikonalHi_coe a b c)
  rw [eikonalRelax_eq_sorted_inputs (some a) (some b) (some c) h]
  rw [hlo, hmid, hhi]
  rw [eikonalRelax_eq_godunov
    (realLo_le_realMid a b c) (realMid_le_realHi a b c) h]
  apply WithTop.coe_eq_coe.mpr
  simp [eikonalR]

/-! ### Abstract comparison principle for the landed sweep -/

/-- A relaxation is monotone when it preserves pointwise order of the data. -/
def MonoRelax {ι : Type*} (relax : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ d e, (∀ v, d v ≤ e v) → ∀ v, relax d v ≤ relax e v

/-- The `WithTop` analogue, for the tree relaxation of `Vdb.TreeSweep`. -/
def MonoRelaxWT {ι : Type*} (relax : (ι → WithTop ℝ) → ι → WithTop ℝ) : Prop :=
  ∀ d e, (∀ v, d v ≤ e v) → ∀ v, relax d v ≤ relax e v

/-- Monotonicity of the sweep step. -/
theorem sweepStep_mono {ι : Type*} [Fintype ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (hrelax : MonoRelax relax)
    {d e : ι → ℝ} (hde : ∀ v, d v ≤ e v) :
    ∀ v, sweepStep frozen relax d v ≤ sweepStep frozen relax e v := by
  intro v
  unfold sweepStep
  split_ifs with h
  · exact hde v
  · exact min_le_min (hde v) (hrelax d e hde v)

/-- Monotonicity of the whole iteration in the initial data. -/
theorem sweepIter_mono_data {ι : Type*} [Fintype ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (hrelax : MonoRelax relax)
    {d e : ι → ℝ} (hde : ∀ v, d v ≤ e v) :
    ∀ k v, sweepIter frozen relax d k v ≤ sweepIter frozen relax e k v := by
  intro k
  induction k with
  | zero => intro v; exact hde v
  | succ k ih =>
      intro v
      rw [sweepIter_succ, sweepIter_succ]
      exact sweepStep_mono frozen relax hrelax ih v

/-- A sub-fixed point `u ≤ T u` never falls below itself under the iteration. -/
theorem sweepIter_ge_self {ι : Type*} [Fintype ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (hrelax : MonoRelax relax)
    {u : ι → ℝ} (hu : ∀ v, u v ≤ sweepStep frozen relax u v) :
    ∀ k v, u v ≤ sweepIter frozen relax u k v := by
  intro k
  induction k with
  | zero => intro v; rfl
  | succ k ih =>
      intro v
      rw [sweepIter_succ]
      exact le_trans (hu v) (sweepStep_mono frozen relax hrelax ih v)

/-- **Abstract comparison principle.** If `u` is a sub-fixed point of the
    sweep and the initial data `d₀` dominates it, every iterate dominates `u`. -/
theorem comparison_iterate {ι : Type*} [Fintype ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (hrelax : MonoRelax relax)
    {u d₀ : ι → ℝ}
    (hu : ∀ v, u v ≤ sweepStep frozen relax u v) (hd₀ : ∀ v, u v ≤ d₀ v) :
    ∀ k v, u v ≤ sweepIter frozen relax d₀ k v := by
  intro k v
  exact le_trans (sweepIter_ge_self frozen relax hrelax hu k v)
    (sweepIter_mono_data frozen relax hrelax hd₀ k v)

/-- Properness of the sweep step: it is order-preserving in its own argument,
    and strictly decreases a node whenever the relaxation is strictly below. -/
theorem sweepStep_proper {ι : Type*} [Fintype ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (d : ι → ℝ) (v : ι)
    (hv : frozen v = false) :
    sweepStep frozen relax d v ≤ d v ∧
      (relax d v < d v → sweepStep frozen relax d v < d v) := by
  constructor
  · exact sweepStep_le frozen relax d v
  · intro hlt
    have hcond : (if frozen v then d v else min (d v) (relax d v)) =
        min (d v) (relax d v) := by simp [hv]
    rw [sweepStep, hcond, min_eq_right (le_of_lt hlt)]
    exact hlt

/-- **Super-solution half of T-FS-FIX.** A fixed point that the sweep actually
    reaches from initial data above a sub-solution `u` dominates `u`. The
    (Zhao 2005) wall is exactly showing that the eight-direction sweep reaches
    its fixed point; `Vdb.FastSweep.sweepIter_big_steps_card` gives only
    termination to within `tol > 0`. -/
theorem comparison_fixedPoint_super {ι : Type*} [Fintype ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (hrelax : MonoRelax relax)
    {u d₀ w : ι → ℝ}
    (hu : ∀ v, u v ≤ sweepStep frozen relax u v)
    (hd₀ : ∀ v, u v ≤ d₀ v)
    (hreach : ∃ k, sweepIter frozen relax d₀ k = w) :
    ∀ v, u v ≤ w v := by
  obtain ⟨k, hk⟩ := hreach
  intro v
  rw [← hk]
  exact comparison_iterate frozen relax hrelax hu hd₀ k v

/-- The concrete relaxation of the dense sweep is monotone. -/
theorem eikonalSweep_mono {ι : Type*} [Fintype ι]
    (nbr : ι → ℝ × ℝ × ℝ) (h : ℝ) (hh : 0 ≤ h) :
    MonoRelax (fun _d v => eikonalR (nbr v).1 (nbr v).2.1 (nbr v).2.2 h) := by
  intro d e hde v
  exact eikonalR_mono (le_refl _) (le_refl _) (le_refl _) hh

/-! ### The exact solution is a fixed point of every sweep direction -/

/-- One Gauss-Seidel node update (already-visited neighbours see the new
    iterate). -/
def gsStep {ι : Type*} [DecidableEq ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (v : ι) (d : ι → ℝ) : ι → ℝ :=
  if frozen v then d else Function.update d v (min (d v) (relax d v))

/-- A Gauss-Seidel pass over an arbitrary visit schedule `σ`. The eight
    Zhao directions are eight particular lists `σ`. -/
def gsPass {ι : Type*} [DecidableEq ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (σ : List ι) (d : ι → ℝ) : ι → ℝ :=
  σ.foldl (fun acc v => gsStep frozen relax v acc) d

/-- A node at which the discrete Eikonal equation holds is left unchanged. -/
theorem gsStep_fixed {ι : Type*} [DecidableEq ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (v : ι) (u : ι → ℝ)
    (hu : ∀ w, frozen w = false → u w = relax u w) :
    gsStep frozen relax v u = u := by
  funext w
  cases hf : frozen v with
  | true =>
      simp [gsStep, hf]
  | false =>
      by_cases hw : w = v
      · subst w
        simp [gsStep, hf, hu v hf]
      · simp [gsStep, hf, hw]

/-- **The fixed-point system of all eight sweep directions.** If `u` solves
    `u v = relax u v` at every non-frozen node, then EVERY visit schedule fixes
    `u` - the order (including all 8 directions) is irrelevant at a fixed point. -/
theorem gsPass_fixed_of_solution {ι : Type*} [DecidableEq ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (σ : List ι) (u : ι → ℝ)
    (hu : ∀ w, frozen w = false → u w = relax u w) :
    gsPass frozen relax σ u = u := by
  induction σ with
  | nil => rfl
  | cons v σ ih =>
      change gsPass frozen relax σ (gsStep frozen relax v u) = u
      rw [gsStep_fixed frozen relax v u hu]
      exact ih

/-- The simultaneous (Jacobi-style) step fixes the same exact solution. -/
theorem sweepStep_fixed_of_solution {ι : Type*} [Fintype ι]
    (frozen : ι → Bool) (relax : (ι → ℝ) → ι → ℝ) (u : ι → ℝ)
    (hu : ∀ w, frozen w = false → u w = relax u w) :
    (fun v => sweepStep frozen relax u v) = u := by
  funext v
  cases hf : frozen v with
  | true =>
      simp [sweepStep, hf]
  | false =>
      simp [sweepStep, hf, hu v hf]

/-- Concrete instantiation: a grid function solving the finite Eikonal fixed
    point system is fixed by the simultaneous step and by every sweep schedule. -/
theorem eikonal_solution_fixed_all_sweeps {ι : Type*} [Fintype ι] [DecidableEq ι]
    (frozen : ι → Bool) (nbr : ι → ℝ × ℝ × ℝ) (h : ℝ) (u : ι → ℝ)
    (hu : ∀ v, frozen v = false →
      u v = eikonalR (nbr v).1 (nbr v).2.1 (nbr v).2.2 h) :
    (∀ σ : List ι,
      gsPass frozen (fun _d v => eikonalR (nbr v).1 (nbr v).2.1 (nbr v).2.2 h) σ u = u) ∧
      (fun v => sweepStep frozen (fun _d v => eikonalR (nbr v).1 (nbr v).2.1 (nbr v).2.2 h) u v) = u := by
  constructor
  · intro σ
    exact gsPass_fixed_of_solution frozen _ σ u hu
  · exact sweepStep_fixed_of_solution frozen _ u hu

/-- Concrete instantiation: at every solved node the exact discrete Eikonal
    equation holds. -/
theorem eikonal_solution_spec {ι : Type*} [Fintype ι]
    (frozen : ι → Bool) (nbr : ι → ℝ × ℝ × ℝ) (h : ℝ) (hh : 0 ≤ h) (u : ι → ℝ)
    (hu : ∀ v, frozen v = false →
      u v = eikonalR (nbr v).1 (nbr v).2.1 (nbr v).2.2 h) :
    ∀ v, frozen v = false →
      let a := (nbr v).1
      let b := (nbr v).2.1
      let c := (nbr v).2.2
      let lo := min (min a b) c
      let mid := max (max (min a b) (min a c)) (min b c)
      let hi := max (max a b) c
      max (u v - lo) 0 ^ 2 + max (u v - mid) 0 ^ 2 + max (u v - hi) 0 ^ 2 = h ^ 2 := by
  intro v hv
  rw [hu v hv]
  exact eikonalR_spec (nbr v).1 (nbr v).2.1 (nbr v).2.2 h hh

/-! ### Monotonicity transfer for the tree relaxation -/

set_option maxHeartbeats 800000 in
/-- The tree relaxation is pointwise monotone whenever the stencil returns
    finite triples and is itself componentwise monotone in the data. The
    hypothesis is immediate for the C min-neighbour stencil, whose three slots
    are minima of neighbour values (hence finite whenever those neighbours
    are, and monotone in them). The comparison input is transported from the
    finite `eikonalR_mono` back to `WithTop` through the bridge above. -/
theorem treeRelax_mono_of_finite {ι : Type*}
    (nbr : ι → (ι → WithTop ℝ) → WithTop ℝ × WithTop ℝ × WithTop ℝ)
    (h : ℝ) (hh : 0 ≤ h)
    (hnbr_mono : ∀ d e v, (∀ w, d w ≤ e w) →
      ∃ a b c a' b' c' : ℝ,
        nbr v d = (some a, some b, some c) ∧
        nbr v e = (some a', some b', some c') ∧
        a ≤ a' ∧ b ≤ b' ∧ c ≤ c') :
    MonoRelaxWT (treeRelax nbr h) := by
  intro d e hde v
  obtain ⟨a, b, c, a', b', c', hd, he, hab, hbc, hcc⟩ :=
    hnbr_mono d e v hde
  have hL : treeRelax nbr h d v = (eikonalR a b c h : WithTop ℝ) := by
    simpa [treeRelax, hd, WithTop.some_eq_coe] using
      (eikonalRelax_coe_eq_eikonalR a b c h)
  have hR : treeRelax nbr h e v = (eikonalR a' b' c' h : WithTop ℝ) := by
    simpa [treeRelax, he, WithTop.some_eq_coe] using
      (eikonalRelax_coe_eq_eikonalR a' b' c' h)
  rw [hL, hR]
  exact WithTop.coe_le_coe.mpr (eikonalR_mono hab hbc hcc hh)

end
end Vdb
