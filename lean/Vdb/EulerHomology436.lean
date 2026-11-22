/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume
  operators.

  Investigation of the algebraic-topology modules newly shipped in
  mathlib v4.36.0 (`Mathlib/AlgebraicTopology/SimplicialSet/Homology/*`,
  `Mathlib/AlgebraicTopology/SimplicialComplex/Basic`,
  `Mathlib/Algebra/Homology/EulerCharacteristic.lean`) and what they do
  and do not contribute to the two Section A walls:

    (a) general Poincaré-Lefschetz  chi(∂K) = 2 * chi(K)   (Vdb.PoincareLefschetz)
    (b) DMC-0 genus                 chi = 2 - 2g            (Vdb.DmcGenus)

  WHAT v4.36 ACTUALLY PROVIDES (verified against source):

  * SSet.chainComplex / SSet.homology / SSet.normalizedChainComplex
    (Homology/Basic, Homology/Nondegenerate), including
    SSet.isZero_homology_of_hasDimensionLT : homology vanishes in
    degree >= d when X : HasDimensionLT d;
  * SSet.Finite and SSet.hasDimensionLT_of_finite (SimplicialSet/Finite);
  * SSet.homology₀Iso : H₀ identifies with the coproduct over π₀ X
    (Homology/HomologyZero);
  * GradedObject.eulerChar / finrankSupport,
    HomologicalComplex.eulerChar / homologyEulerChar and the finite-sum
    lemmas eulerChar_eq_sum_finSet_of_finrankSupport_subset,
    homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    (Algebra/Homology/EulerCharacteristic);
  * AbstractSimplicialComplex / PreAbstractSimplicialComplex, which are
    purely COMBINATORIAL (a SetLike of nonempty Finsets with a lattice
    structure) -- only `SimplicialComplex/Basic.lean` exists; there is no
    chain complex, no Euler characteristic, and no simplicial-complex ->
    simplicial-set homology bridge anywhere in the import.

  WHAT IS STILL MISSING (and why the walls do not break):

  1. There is NO theorem `HomologicalComplex.eulerChar =
     HomologicalComplex.homologyEulerChar` (Euler-Poincaré principle)
     anywhere in mathlib.  `homologyEulerChar` is merely a definition;
     without that equality one cannot conclude `chi = Σ (-1)^i rank H_i`
     from the algebraic chain Euler characteristic.
  2. There is NO Poincaré duality / Lefschetz theorem and no
     Euler-characteristic duality theorem in mathlib 4.36 (searched
     Algebra/Homology, AlgebraicTopology, Topology).  So wall (a)'s single
     missing input `HasInteriorDuality` (chiInterior K = -chiOf K) stays open.
  3. Both walls are about CUBICAL complexes (`Vdb/Euler.lean`'s C3 cubes,
     the DMC-0 dual quad mesh), not simplicial sets/complexes.  The new
     simplicial homology does not apply to a cubical cell complex, and no
     cubical-sets-with-duality module was added.
  4. For wall (b) one would additionally need H₁ of the dual surface to
     identify with 2*g and H₂ with orientability (χ = 2 - 2g).  Neither a
     genus theorem nor an orientability-to-H₂ theorem exists here.

  Consequently this module proves only the rigorous scaffolding that the
  new modules DO supply (finite support and finite alternating-sum form of
  the homological Euler characteristic of a finite-dimensional simplicial
  set), and records the exact gap.  No existing theorem is weakened.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
module

import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.HomologyZero
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.LinearAlgebra.Dimension.Finite

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Vdb

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

/-- The simplicial homology of `X` with coefficients in the free rank-one
    ℤ-module, as an object of `ModuleCat ℤ` (so that `Module.finrank` and the
    Euler-characteristic definitions apply). -/
abbrev SSetHomologyℤ (X : SSet) (n : ℕ) : ModuleCat ℤ :=
  X.homology (ModuleCat.of ℤ ℤ) n

/-- The simplicial chain complex of `X` with ℤ coefficients, as a complex of
    ℤ-modules indexed by `ℕ` with the "up" complex shape. -/
abbrev SSetChainComplexℤ (X : SSet) : ChainComplex (ModuleCat ℤ) ℕ :=
  X.chainComplex (ModuleCat.of ℤ ℤ)

/-! ### Finite support of homology in each degree

This is the one genuinely new ingredient v4.36 gives the χ-from-homology
agenda: `SSet.isZero_homology_of_hasDimensionLT` forces the homology to
vanish above the dimension bound, so the `finsum` defining the homological
Euler characteristic collapses to a finite sum.  It does NOT yield
`chi = Σ (-1)^i rank H_i` for any of the Vdb cubical complexes, because
(a) those are cubical, not simplicial, and (b) the Euler-Poincaré equality
`eulerChar = homologyEulerChar` is not in mathlib. -/

set_option maxHeartbeats 800000 in
theorem ssHomology_finrankSupport_subset_range (X : SSet) (d : ℕ)
    [X.HasDimensionLT d] :
    GradedObject.finrankSupport (fun i : ℕ => SSetHomologyℤ X i) ⊆
      (Finset.range d : Set ℕ) := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro i hi
  have hnot : ¬ i < d := by
    intro hlt
    exact hi (by simpa [Finset.mem_range] using hlt)
  have hdi : d ≤ i := le_of_not_gt hnot
  have hz : IsZero (SSetHomologyℤ X i) :=
    X.isZero_homology_of_hasDimensionLT (ModuleCat.of ℤ ℤ) i d hdi
  haveI : Subsingleton (SSetHomologyℤ X i) := ModuleCat.isZero_iff_subsingleton.mp hz
  exact Module.finrank_zero_of_subsingleton

set_option maxHeartbeats 800000 in
theorem ssHomology_finrankSupport_finite (X : SSet) [X.Finite] :
    ∃ d : ℕ, GradedObject.finrankSupport (fun i : ℕ => SSetHomologyℤ X i) ⊆
      (Finset.range d : Set ℕ) := by
  obtain ⟨d, hd⟩ := X.hasDimensionLT_of_finite
  exact ⟨d, ssHomology_finrankSupport_subset_range X d⟩

set_option maxHeartbeats 800000 in
/-- The homological Euler characteristic of a dimension-bounded simplicial
    set is the finite alternating sum of its Betti numbers.  This is the
    strongest χ-from-homology statement the new v4.36 modules support on
    their own; it is a statement about simplicial sets, not the Vdb cubical
    complexes, and it is NOT identified with the cell-count `chiOf K`. -/
theorem ssHomologyEulerChar_eq_sum_range (X : SSet) (d : ℕ)
    [X.HasDimensionLT d] :
    HomologicalComplex.homologyEulerChar (SSetChainComplexℤ X) =
      ∑ i ∈ Finset.range d,
        ((ComplexShape.up ℕ).χ i : ℤ) * Module.finrank ℤ (SSetHomologyℤ X i) := by
  apply HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
  exact ssHomology_finrankSupport_subset_range X d

end

end Vdb
