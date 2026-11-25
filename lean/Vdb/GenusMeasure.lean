/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  Topological measures of a level set (`tvdb_level_set_euler_characteristic`,
  `tvdb_level_set_genus`). The C definition is

      genus = (#interior components) − χ(solid),   χ(surface) = 2 · χ(solid).

  This module fixes the integer-level part: it defines the component count of a
  finite cubical solid under 26-adjacency (`cubeAdj`), the genus as the C
  formula, and proves the χ relation under the named `HasInteriorDuality`
  premise (Poincaré–Lefschetz is a documented wall in mathlib 4.36, so no
  unconditional duality is claimed). Concrete χ evaluations are already in
  `Vdb.Euler`; component counts are intentionally not evaluated here because
  connectivity over the classical subtype is noncomputable.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Euler
import Vdb.PoincareLefschetz
import Vdb.Segmentation

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

noncomputable section

namespace Vdb

/-- 26-adjacency (face, edge or corner contact) of integer cube coordinates. -/
def cubeAdj (a b : C3) : Prop :=
  a ≠ b ∧ |a.1 - b.1| ≤ 1 ∧ |a.2.1 - b.2.1| ≤ 1 ∧ |a.2.2 - b.2.2| ≤ 1

theorem cubeAdj_symm (a b : C3) : cubeAdj a b ↔ cubeAdj b a := by
  constructor <;> intro h <;> rcases h with ⟨hne, hx, hy, hz⟩
  · exact ⟨Ne.symm hne, by simpa [abs_sub_comm] using hx,
      by simpa [abs_sub_comm] using hy, by simpa [abs_sub_comm] using hz⟩
  · exact ⟨Ne.symm hne, by simpa [abs_sub_comm] using hx,
      by simpa [abs_sub_comm] using hy, by simpa [abs_sub_comm] using hz⟩

/-- The components of a finite cubical solid, as subsets of the solid's
    subtype. Connectivity is `Segmentation.Conn` restricted to `cubeAdj`. -/
def cubeComponents (K : Finset C3) : Finset (Finset {x // x ∈ K}) :=
  components (fun a b : {x // x ∈ K} => cubeAdj a.1 b.1)
    (Finset.univ : Finset {x // x ∈ K})

/-- Number of connected interior components of the solid. -/
def solidComponents (K : Finset C3) : ℕ := (cubeComponents K).card

/-- The C `tvdb_level_set_genus` formula, over ℤ. -/
def solidGenus (K : Finset C3) : ℤ := (solidComponents K : ℤ) - chiOf K

theorem solidGenus_eq (K : Finset C3) : solidGenus K = (solidComponents K : ℤ) - chiOf K := rfl

/-- The χ(surface) = 2 χ(solid) identity, conditional on interior duality. -/
theorem chiSurface_eq_two_chiOf (K : Finset C3) (h : HasInteriorDuality K) :
    chiBoundary K = 2 * chiOf K :=
  chiBoundary_eq_two_chiOf_of_hasInteriorDuality K h

/-- Under duality, twice the genus is `2·components − χ(surface)`,
    matching the C arithmetic without introducing half-integers. -/
theorem two_mul_solidGenus_eq (K : Finset C3) (h : HasInteriorDuality K) :
    2 * solidGenus K = 2 * (solidComponents K : ℤ) - chiBoundary K := by
  have hchi := chiSurface_eq_two_chiOf K h
  unfold solidGenus
  linarith

/-- A one-component solid with the χ of a single cube has genus zero. -/
theorem solidGenus_eq_zero_of_one_cube (K : Finset C3)
    (hc : solidComponents K = 1) (hchi : chiOf K = 1) : solidGenus K = 0 := by
  unfold solidGenus
  rw [hc, hchi]
  norm_num

end Vdb
