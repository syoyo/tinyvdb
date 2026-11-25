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


theorem incidentCells_inj (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    {p p' : Lat} {d d' : Nat} (hd : d < 3) (hd' : d' < 3)
    (hp : PadGrid.InLattice n p) (hp' : PadGrid.InLattice n p')
    (hne : s p ≠ s (PadGrid.succN p d)) (hne' : s p' ≠ s (PadGrid.succN p' d'))
    (h : DmcOnePad.incidentCells s (p,d) = DmcOnePad.incidentCells s (p',d')) :
    (p,d) = (p',d') := by
  have hp_eq : p = p' := by
    have h3 := congrArg (fun l : List Cell => l.getD 2 (0,0,0)) h
    rw [incidentCells_third n s hpin hd hp hne] at h3
    rw [incidentCells_third n s hpin hd' hp' hne'] at h3
    exact h3
  subst p'
  have hq := anchorCell_eq_pinned n s hpin hd hp hne
  have hq' := anchorCell_eq_pinned n s hpin hd' hp hne'
  have hfirst := congrArg (fun l : List Cell => l.getD 0 (0,0,0)) h
  simp [DmcOnePad.incidentCells] at hfirst
  rw [hq, hq'] at hfirst
  have hd_eq : d = d' := by
    have ht := PadGrid.pinned_transverse n s hpin hp hne
    have ht' := PadGrid.pinned_transverse n s hpin hp hne'
    interval_cases d <;> interval_cases d'
    · rfl
    · have hb1 : 1 ≤ p.2.1 := by simpa using (ht.1 rfl).1
      have hb2 : 1 ≤ p.2.2 := by simpa using (ht.1 rfl).2.2.1
      have hb3 : 1 ≤ p.1 := by simpa using (ht'.2.1 rfl).1
      have hb4 : 1 ≤ p.2.2 := by simpa using (ht'.2.1 rfl).2.2.1
      simp [hq, hq'] at hfirst
      omega
    · have hb1 : 1 ≤ p.2.1 := by simpa using (ht.1 rfl).1
      have hb2 : 1 ≤ p.2.2 := by simpa using (ht.1 rfl).2.2.1
      have hb3 : 1 ≤ p.1 := by simpa using (ht'.2.2 rfl).1
      have hb4 : 1 ≤ p.2.1 := by simpa using (ht'.2.2 rfl).2.2.1
      simp [hq, hq'] at hfirst
      omega
    · have hb1 : 1 ≤ p.1 := by simpa using (ht.2.1 rfl).1
      have hb2 : 1 ≤ p.2.2 := by simpa using (ht.2.1 rfl).2.2.1
      have hb3 : 1 ≤ p.2.1 := by simpa using (ht'.1 rfl).1
      have hb4 : 1 ≤ p.2.2 := by simpa using (ht'.1 rfl).2.2.1
      simp [hq, hq'] at hfirst
      omega
    · rfl
    · have hb1 : 1 ≤ p.1 := by simpa using (ht.2.1 rfl).1
      have hb2 : 1 ≤ p.2.2 := by simpa using (ht.2.1 rfl).2.2.1
      have hb3 : 1 ≤ p.1 := by simpa using (ht'.2.2 rfl).1
      have hb4 : 1 ≤ p.2.1 := by simpa using (ht'.2.2 rfl).2.2.1
      simp [hq, hq'] at hfirst
      omega
    · have hb1 : 1 ≤ p.1 := by simpa using (ht.2.2 rfl).1
      have hb2 : 1 ≤ p.2.1 := by simpa using (ht.2.2 rfl).2.2.1
      have hb3 : 1 ≤ p.2.1 := by simpa using (ht'.1 rfl).1
      have hb4 : 1 ≤ p.2.2 := by simpa using (ht'.1 rfl).2.2.1
      simp [hq, hq'] at hfirst
      omega
    · have hb1 : 1 ≤ p.1 := by simpa using (ht.2.2 rfl).1
      have hb2 : 1 ≤ p.2.1 := by simpa using (ht.2.2 rfl).2.2.1
      have hb3 : 1 ≤ p.1 := by simpa using (ht'.2.1 rfl).1
      have hb4 : 1 ≤ p.2.2 := by simpa using (ht'.2.1 rfl).2.2.1
      simp [hq, hq'] at hfirst
      omega
    · rfl
  subst d'
  rfl


theorem dmcOneQuadN_inj (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    {p p' : Lat} {d d' : Nat} (hd : d < 3) (hd' : d' < 3)
    (hp : PadGrid.InLattice n p) (hp' : PadGrid.InLattice n p')
    (hne : s p ≠ s (PadGrid.succN p d)) (hne' : s p' ≠ s (PadGrid.succN p' d'))
    (hquad : dmcOneQuadN s (p, d) = dmcOneQuadN s (p', d')) :
    (p, d) = (p', d') := by
  have hbne : (s p == s (PadGrid.succN p d)) = false := by
    cases h1 : s p <;> cases h2 : s (PadGrid.succN p d) <;> simp_all
  have hbne' : (s p' == s (PadGrid.succN p' d')) = false := by
    cases h1 : s p' <;> cases h2 : s (PadGrid.succN p' d') <;> simp_all
  have hcells : DmcOnePad.incidentCells s (p,d) = DmcOnePad.incidentCells s (p',d') := by
    have h1 := congrArg (List.map Prod.fst) hquad
    simpa [dmcOneQuadN, hbne, hbne', DmcOnePad.cellPatchVertex, Function.comp_def] using h1
  exact incidentCells_inj n s hpin hd hd' hp hp' hne hne' hcells


/-- The quads of a shell-pinned field are exactly the image of the crossed
    lattice edges under the quad map. -/
theorem dmcOneQuads_eq_map_crossed (n : Nat) (s : Lat → Bool) :
    dmcOneQuads n s = (PadGrid.crossed n s).map (fun e => dmcOneQuadN s e) := by
  have map_flatMap : ∀ (l : List Lat), ∀ (f : Lat → List PadEdge),
      (l.flatMap f).map (fun e => dmcOneQuadN s e) =
      l.flatMap (fun p => (f p).map (fun e => dmcOneQuadN s e)) := by
    intro l f
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap, Function.comp_def]
  unfold dmcOneQuads PadGrid.crossed
  rw [map_flatMap]
  apply List.flatMap_congr
  intro p hp
  rw [List.map_filterMap]
  apply List.filterMap_congr
  intro d hd
  by_cases h : (decide (PadGrid.InLattice n (PadGrid.succN p d)) && (s p != s (PadGrid.succN p d))) = true
  · simp [h]
  · simp [h]


theorem dmcOneQuads_nodup (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) :
    (dmcOneQuads n s).Nodup := by
  rw [dmcOneQuads_eq_map_crossed]
  have hcross' : List.Pairwise
      (fun a b : PadEdge => a ≠ b ∧ dmcOneQuadN s a ≠ dmcOneQuadN s b)
      (PadGrid.crossed n s) := by
    apply List.Pairwise.imp_of_mem ?_ (PadGrid.nodup_crossed n s)
    intro a b ha hb hne
    refine ⟨hne, ?_⟩
    intro hq
    rcases a with ⟨p,d⟩
    rcases b with ⟨p',d'⟩
    obtain ⟨hd3, hp3, _, hneA⟩ := PadGrid.crossed_spec n s ha
    obtain ⟨hd'3, hp'3, _, hneB⟩ := PadGrid.crossed_spec n s hb
    have he : (p,d) = (p',d') := dmcOneQuadN_inj n s hpin hd3 hd'3 hp3 hp'3 hneA hneB hq
    exact hne he
  exact List.Pairwise.map (fun e => dmcOneQuadN s e) (fun a b h => h.2) hcross'

end DmcOneEuler
end Vdb
