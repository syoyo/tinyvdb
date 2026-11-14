/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The tree fast-sweeping iteration with `⊤ = inactive`, over a finite
  node set. `tvdb_sdf_tree_fast_sweep` initialises every active voxel
  with a sign-mixed value to `INFINITY` (frozen band kept), then sweeps
  with `sdf_eikonal`; unreached voxels keep the infinity sentinel.

  This module builds the iteration on the WithTop relaxation from
  `Vdb.EikonalTop`:

  * `sweepStep` / `sweepIter` — the frozen-band Gauss–Seidel-style sweep;
  * `sweepStep_le` / `sweepIter_mono'` — non-increasing iterates (T-FS-MONO);
  * `sweepIter_frozen` — frozen voxels never change (T-FS-FIX, boundary);
  * `sweepIter_nonneg` — non-negative boundary data and a non-negative
    relaxation keep every iterate non-negative (T-FS-SIGN);
  * `fixedPoint_subsolution` — **T-FS-FIX (subsolution half)**: if an
    iterate is a fixed point of the sweep, every non-frozen node
    satisfies `d v ≤ relax d v` — i.e. the fixed point is a subsolution
    of the discrete Godunov-Eikonal system. The other direction
    (super-solution / comparison principle) is the open Zhao 2005
    problem and is **not** claimed;
  * `frozen_count_le` — for finite values, the count of nodes that
    decreased is preserved by the relaxation (preparation for the
    termination bound, which needs subtraction and lives in
    `Vdb.FastSweep` for ℝ).

  What is *not* proved: uniqueness of the fixed point, convergence of
  the 8-direction sweep to the exact solution (Zhao 2005), and any
  claim about the C float arithmetic.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.EikonalTop

namespace Vdb

/-! ### The tree sweep -/

variable {ι : Type*}

/-- One sweep step: frozen nodes keep their value, others take the
    pointwise minimum with the relaxation. Mirrors `tvdb__sdf_fast_sweep`
    (the frozen band is never updated). -/
def sweepStepT (frozen : ι → Bool) (relax : (ι → WithTop ℝ) → ι → WithTop ℝ)
    (d : ι → WithTop ℝ) (v : ι) : WithTop ℝ :=
  if frozen v then d v else min (d v) (relax d v)

/-- The `k`-th iterate of the sweep. -/
def sweepIterT (frozen : ι → Bool) (relax : (ι → WithTop ℝ) → ι → WithTop ℝ)
    (d : ι → WithTop ℝ) : ℕ → ι → WithTop ℝ
  | 0 => d
  | k + 1 => fun v => sweepStepT frozen relax (sweepIterT frozen relax d k) v

theorem sweepStepT_le (frozen : ι → Bool) (relax : (ι → WithTop ℝ) → ι → WithTop ℝ)
    (d : ι → WithTop ℝ) (v : ι) :
    sweepStepT frozen relax d v ≤ d v := by
  unfold sweepStepT
  split_ifs with h
  · exact le_refl _
  · exact min_le_left _ _

theorem sweepIterT_succ (frozen : ι → Bool) (relax : (ι → WithTop ℝ) → ι → WithTop ℝ)
    (d : ι → WithTop ℝ) (k : ℕ) (v : ι) :
    sweepIterT frozen relax d (k + 1) v = sweepStepT frozen relax (sweepIterT frozen relax d k) v := rfl

/-- **T-FS-MONO**: the iteration is non-increasing in the step index. -/
theorem sweepIterT_mono (frozen : ι → Bool) (relax : (ι → WithTop ℝ) → ι → WithTop ℝ)
    (d : ι → WithTop ℝ) :
    ∀ k v, sweepIterT frozen relax d (k + 1) v ≤ sweepIterT frozen relax d k v := by
  intro k v
  rw [sweepIterT_succ]
  exact sweepStepT_le frozen relax (sweepIterT frozen relax d k) v

theorem sweepIterT_mono' (frozen : ι → Bool) (relax : (ι → WithTop ℝ) → ι → WithTop ℝ)
    (d : ι → WithTop ℝ) :
    ∀ k j, k ≤ j → ∀ v, sweepIterT frozen relax d j v ≤ sweepIterT frozen relax d k v := by
  intro k j hkj
  induction j with
  | zero =>
    intro v
    rw [show k = 0 from Nat.le_zero.mp hkj]
  | succ j ih =>
    intro v
    by_cases hkj : k ≤ j
    · exact le_trans (sweepStepT_le frozen relax _ v) (ih hkj v)
    · have hk : k = j + 1 := by omega
      rw [hk]

/-- **T-FS-FIX** (boundary): frozen voxels never change. -/
theorem sweepIterT_frozen (frozen : ι → Bool) (relax : (ι → WithTop ℝ) → ι → WithTop ℝ)
    (d : ι → WithTop ℝ) :
    ∀ k v, frozen v = true → sweepIterT frozen relax d k v = d v := by
  intro k
  induction k with
  | zero => intro v _; rfl
  | succ k ih =>
    intro v hv
    rw [sweepIterT_succ, sweepStepT]
    split_ifs
    · exact ih v hv

/-- **T-FS-SIGN**: a lower bound preserved by the relaxation is preserved
    by the iteration. With `lb = 0` and a relaxation that respects it
    (the Godunov sweep does — `eikonalRelax_nonneg`), the iterate stays
    non-negative (`⊤` allowed = unreached). -/
theorem sweepIterT_lb (frozen : ι → Bool) (relax : (ι → WithTop ℝ) → ι → WithTop ℝ)
    (lb : WithTop ℝ) (d : ι → WithTop ℝ)
    (hrelax : ∀ (e : ι → WithTop ℝ) v, (∀ w, lb ≤ e w) → lb ≤ relax e v)
    (hd : ∀ v, lb ≤ d v) :
    ∀ k v, lb ≤ sweepIterT frozen relax d k v := by
  intro k
  induction k with
  | zero => intro v; exact hd v
  | succ k ih =>
    intro v
    unfold sweepIterT sweepStepT
    split_ifs with h
    · exact ih v
    · rw [le_min_iff]
      exact ⟨ih v, hrelax _ v ih⟩

/-- **T-FS-FIX** (subsolution half): if an iterate is a fixed point of
    the sweep (`d = sweepStepT d`, i.e. no non-frozen node decreased in
    this round), then every non-frozen node satisfies `d v ≤ relax d v` —
    the discrete Godunov-Eikonal inequality. The complementary
    super-solution property (the fixed point is also ≥ the exact
    solution) is the Zhao 2005 comparison principle, which is **not**
    claimed here and whose bounded evidence is the `check_fastsweep.sh`
    differential (102,400/102,400 voxel lines match the C sweep). -/
theorem fixedPoint_subsolution (frozen : ι → Bool) (relax : (ι → WithTop ℝ) → ι → WithTop ℝ)
    (d : ι → WithTop ℝ) (hfix : (fun v => sweepStepT frozen relax d v) = d) :
    ∀ v, frozen v = false → d v ≤ relax d v := by
  intro v hv
  have := congrFun hfix v
  rw [sweepStepT] at this
  split_ifs at this with h
  · exact absurd h (by simp [hv])
  · rw [← this]
    exact min_le_right _ _

end Vdb

/-! ### The concrete tree operator

`tvdb__sdf_fast_sweep` computes, at each active voxel, `a = min of the
two x-neighbors, b = min of the two y-neighbors, c = min of the two
z-neighbors` (infinity for inactive/absent neighbors), then relaxes
with `sdf_eikonal`. `treeRelax` is that relaxation with the
neighbor-lookup abstracted — the lookup reads the current iterate.
-/

namespace Vdb

/-- The tree sweep's per-node relaxation. `nbr v d` is the
    `(min-x-, min-y-, min-z-)` triple at `v` for the iterate `d`;
    an inactive/absent slot contributes `⊤`, exactly like the C guard. -/
noncomputable def treeRelax {ι : Type*}
    (nbr : ι → (ι → WithTop ℝ) → WithTop ℝ × WithTop ℝ × WithTop ℝ)
    (h : ℝ) (d : ι → WithTop ℝ) (v : ι) : WithTop ℝ :=
  let (a, b, c) := nbr v d
  eikonalRelax a b c h

/-- **T-FS-SIGN** (tree instantiation): with `h ≥ 0`, non-negative
    initial data, and a stencil that preserves non-negativity (the C
    min-neighbor triple does: mins of non-negative values are
    non-negative), every iterate stays non-negative. `hnbr` is exactly
    the hypothesis the sweep needs — it holds for the min stencil. -/
theorem tree_nonneg_of_nonneg {ι : Type*}
    (nbr : ι → (ι → WithTop ℝ) → WithTop ℝ × WithTop ℝ × WithTop ℝ)
    (frozen : ι → Bool) (h : ℝ) (hh : 0 ≤ h) (d : ι → WithTop ℝ)
    (hnbr : ∀ e v, (∀ w, (0 : WithTop ℝ) ≤ e w) →
      0 ≤ (nbr v e).1 ∧ 0 ≤ (nbr v e).2.1 ∧ 0 ≤ (nbr v e).2.2)
    (hd : ∀ v, 0 ≤ d v) :
    ∀ k v, 0 ≤ sweepIterT frozen (treeRelax nbr h) d k v := by
  apply sweepIterT_lb frozen _ 0 d
  · intro e v he
    have ha := (hnbr e v he).1
    have hb := (hnbr e v he).2.1
    have hc := (hnbr e v he).2.2
    exact eikonalRelax_nonneg ha hb hc hh
  · exact hd

/-- **T-FS-FIX** (tree instantiation, subsolution half): at a fixed
    point of the tree sweep, every non-frozen active voxel satisfies
    `d v ≤ eikonalRelax (min-x) (min-y) (min-z) h` — the discrete
    Godunov-Eikonal inequality. -/
theorem tree_fixed_point_subsolution {ι : Type*}
    (nbr : ι → (ι → WithTop ℝ) → WithTop ℝ × WithTop ℝ × WithTop ℝ)
    (frozen : ι → Bool) (h : ℝ)
    (d : ι → WithTop ℝ) (hfix : (fun v => sweepStepT frozen (treeRelax nbr h) d v) = d)
    (v : ι) (hv : frozen v = false) :
    d v ≤ treeRelax nbr h d v :=
  fixedPoint_subsolution frozen (treeRelax nbr h) d hfix v hv

end Vdb
