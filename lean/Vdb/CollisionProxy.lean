/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-2: the contract a simplified mesh must satisfy to be usable as a physics
  collision proxy. The contract is a conjunction of the combinatorial
  properties proved in `PhysMesh`/`EdgeCollapse` (watertight, loop-free, within
  a face budget) and a geometric deviation bound: every surviving vertex stays
  within `ε` of its original position. This module proves how the contract
  composes across a sequence of collapses — deviation bounds add by the
  triangle inequality and the face budget is monotone — so the C driver's
  final report can be checked against a single specification.

  The algorithm itself (quadric ranking, link test, greedy order) lives in the
  C implementation and in the executable differential twin; its *contracts*,
  not its floating-point ranking, are what is proven here.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Vdb.PhysMesh
import Vdb.EdgeCollapse

set_option linter.unusedSectionVars false

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

namespace CollisionProxy

variable {ι V : Type} [DecidableEq ι]

/-- The combinatorial + budget contract of a collision proxy. -/
structure Contract (m : PhysMesh ι V) (budget : ℕ) : Prop where
  watertight : m.Watertight
  loopless : m.Loopless
  face_budget : m.faces.length ≤ budget

/-- Every surviving vertex is within `ε` of its position in the source mesh. -/
def DeviationBound (source result : PhysMesh ι Point) (ε : ℝ) : Prop :=
  ∀ i, dist (source.pos i) (result.pos i) ≤ ε

/-- Deviations compose additively. -/
theorem deviation_trans {a b c : PhysMesh ι Point} {ε₁ ε₂ : ℝ}
    (h₁ : DeviationBound a b ε₁) (h₂ : DeviationBound b c ε₂) :
    DeviationBound a c (ε₁ + ε₂) := by
  intro i
  calc
    dist (a.pos i) (c.pos i) ≤ dist (a.pos i) (b.pos i) + dist (b.pos i) (c.pos i) := dist_triangle _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add (h₁ i) (h₂ i)

theorem deviation_mono {a b : PhysMesh ι Point} {ε ε' : ℝ}
    (h : DeviationBound a b ε) (hε : ε ≤ ε') : DeviationBound a b ε' :=
  fun i => (h i).trans hε

/-- A collapse that preserves closure and spends no extra faces satisfies the
    contract with the same budget. This is the step lemma the C driver's
    repeated collapses accumulate. -/
theorem contract_of_collapse {m : PhysMesh ι V} {budget : ℕ}
    (hc : Contract m budget) (a b : ι) (v : V)
    (hw : (EdgeCollapse.collapse m a b v).Watertight)
    (hl : (EdgeCollapse.collapse m a b v).Loopless) :
    Contract (EdgeCollapse.collapse m a b v) budget :=
  ⟨hw, hl, (EdgeCollapse.collapse_faces_length_le m a b v).trans hc.face_budget⟩

/-- A tighter budget is a stronger claim; this lemma lets a caller weaken a
    proven bound to the requested one. -/
theorem contract_of_tighter {m : PhysMesh ι V} {budget budget' : ℕ}
    (hc : Contract m budget) (h : budget ≤ budget') : Contract m budget' :=
  ⟨hc.watertight, hc.loopless, hc.face_budget.trans h⟩

/-- Empty meshes are valid (vacuously watertight and loop-free) proxies. -/
theorem contract_empty (pos : ι → V) (budget : ℕ) :
    Contract ({ pos := pos, faces := [] } : PhysMesh ι V) budget :=
  ⟨PhysMesh.watertight_empty pos, PhysMesh.loopless_empty pos, Nat.zero_le _⟩

end CollisionProxy
end Vdb
