/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Injectivity data for the DMC-1 quad map on crossed lattice edges.
  Under shell pinning the anchor cell of a crossed edge has an explicit
  coordinate form, and the third cell of the edge's incident-cell ring
  is the edge's own start point. These are the ingredients for showing
  that two crossed edges emitting the same quad must be equal, which is
  the last combinatorial step of the global DMC-1 Nodup criterion.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.DmcOneEuler
import Vdb.DmcOnePad
import Vdb.PadGrid
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Vdb
namespace DmcOneEuler

/-- Under shell pinning a crossed edge's anchor is the cell obtained by
    decrementing the two transverse coordinates of the edge's start. -/
theorem anchorCell_eq_pinned (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    {p : Lat} {d : Nat} (hd : d < 3) (hp : PadGrid.InLattice n p)
    (hne : s p ≠ s (PadGrid.succN p d)) :
    PadGrid.anchorCell p d = some
      (match d with
       | 0 => (p.1, p.2.1 - 1, p.2.2 - 1)
       | 1 => (p.1 - 1, p.2.1, p.2.2 - 1)
       | _ => (p.1 - 1, p.2.1 - 1, p.2.2)) := by
  have ht := PadGrid.pinned_transverse n s hpin hp hne
  interval_cases d
  · have h1 : 1 ≤ p.2.1 := (by simpa using (ht.1 rfl).1)
    have h2 : 1 ≤ p.2.2 := (by simpa using (ht.1 rfl).2.2.1)
    simp [PadGrid.anchorCell, h1, h2]
  · have h1 : 1 ≤ p.1 := (by simpa using (ht.2.1 rfl).1)
    have h2 : 1 ≤ p.2.2 := (by simpa using (ht.2.1 rfl).2.2.1)
    simp [PadGrid.anchorCell, h1, h2]
  · have h1 : 1 ≤ p.1 := (by simpa using (ht.2.2 rfl).1)
    have h2 : 1 ≤ p.2.1 := (by simpa using (ht.2.2 rfl).2.2.1)
    simp [PadGrid.anchorCell, h1, h2]

/-- The third cell of a crossed edge's incident-cell ring is the edge's
    own start point (independent of the sign flip). -/
theorem incidentCells_third (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    {p : Lat} {d : Nat} (hd : d < 3) (hp : PadGrid.InLattice n p)
    (hne : s p ≠ s (PadGrid.succN p d)) :
    (DmcOnePad.incidentCells s (p, d)).getD 2 (0, 0, 0) = p := by
  have hq := anchorCell_eq_pinned n s hpin hd hp hne
  have ht := PadGrid.pinned_transverse n s hpin hp hne
  interval_cases d <;> cases hsp : s p
  all_goals
    simp [DmcOnePad.incidentCells, hq, PadGrid.ij, PadGrid.addCell, hsp]
    all_goals ext <;> simp_all <;> omega

end DmcOneEuler
end Vdb
