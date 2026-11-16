/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Embedding of small sign fields into larger padded grids. A sign field
  whose `true` samples all lie on `{1,2}^3` produces, in the general-`n`
  cuberille/DMC assembly (`Vdb/PadGrid.lean`), the *same* crossed lattice
  edges, the same labeled-face quads and the same mesh membership for every
  `n ≥ 3` as for `n = 3`. Hence its vertex, undirected-edge and quad counts
  — and its Euler characteristic — do not depend on `n ≥ 3`.

  This turns the bounded `n = 3` counterexamples of `Vdb/Cuberille.lean`
  (`bounded_chi_manifold_not_chi2`) into a statement for every grid size:
  `χ = 3` already occurs, so `χ = 2` is not a general theorem.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.QuadEulerPad

set_option linter.unusedSimpArgs false

namespace Vdb

namespace PadGrid

/-- All `true` samples lie on `{1,2}^3`. -/
def Supp (s : Lat → Bool) : Prop :=
  ∀ p : Lat, s p = true →
    (1 ≤ p.1 ∧ p.1 ≤ 2) ∧ (1 ≤ p.2.1 ∧ p.2.1 ≤ 2) ∧ (1 ≤ p.2.2 ∧ p.2.2 ≤ 2)

/-- A field supported on `{1,2}^3` is shell-pinned in every grid with `n ≥ 3`. -/
theorem supp_pinned {s : Lat → Bool} (hs : Supp s) {n : Nat} (hn : 3 ≤ n) :
    ∀ p, isShell n p = true → s p = false := by
  intro p hp
  by_contra hc
  have h : s p = true := by simpa using hc
  obtain ⟨h1, h2, h3⟩ := hs p h
  simp [isShell] at hp
  omega

/-- Coordinates of a crossed edge's base point: all `≤ 2`; the successor
    stays within `[0, 3]`. -/
theorem supp_crossed_le {s : Lat → Bool} (hs : Supp s) {p : Lat} {d : Nat}
    (hd : d < 3) (hne : s p ≠ s (succN p d)) :
    p.1 ≤ 2 ∧ p.2.1 ≤ 2 ∧ p.2.2 ≤ 2 := by
  have hor : s p = true ∨ s (succN p d) = true := by
    by_contra hc
    rw [not_or] at hc
    exact hne (by rw [Bool.eq_false_iff.mpr hc.1, Bool.eq_false_iff.mpr hc.2])
  rcases hor with h | h
  · obtain ⟨⟨_, a⟩, ⟨_, b⟩, ⟨_, c⟩⟩ := hs p h
    exact ⟨a, b, c⟩
  · obtain ⟨⟨_, a⟩, ⟨_, b⟩, ⟨_, c⟩⟩ := hs _ h
    interval_cases d <;> simp [succN] at a b c ⊢ <;> omega

/-- The crossing test is independent of `n ≥ 3` for supported fields. -/
theorem crossedB_congr {s : Lat → Bool} (hs : Supp s) {n : Nat} (hn : 3 ≤ n)
    (p : Lat) (d : Nat) (hd : d < 3) :
    crossedB n s (p, d) = crossedB 3 s (p, d) := by
  by_cases hne : s p = s (succN p d)
  · simp [crossedB, hne]
  · obtain ⟨a, b, c⟩ := supp_crossed_le hs hd hne
    have hq : (succN p d).1 ≤ 3 ∧ (succN p d).2.1 ≤ 3 ∧ (succN p d).2.2 ≤ 3 := by
      interval_cases d <;> simp [succN] <;> omega
    have hp3 : InLattice 3 p := ⟨by omega, by omega, by omega⟩
    have hq3 : InLattice 3 (succN p d) := ⟨hq.1, hq.2.1, hq.2.2⟩
    have hpn : InLattice n p := ⟨by omega, by omega, by omega⟩
    have hqn : InLattice n (succN p d) := ⟨by have := hq.1; omega,
      by have := hq.2.1; omega, by have := hq.2.2; omega⟩
    simp [crossedB, hne, hp3, hq3, hpn, hqn]

/-- Crossed edges of a supported field are the same for every `n ≥ 3`. -/
theorem crossed_mem_congr {s : Lat → Bool} (hs : Supp s) {n : Nat} (hn : 3 ≤ n)
    (e : PadEdge) : e ∈ crossed n s ↔ e ∈ crossed 3 s := by
  obtain ⟨p, d⟩ := e
  constructor
  · intro h
    obtain ⟨hd, _⟩ := crossed_spec n s h
    have hb := crossedB_of_crossed n s h
    rw [crossedB_congr hs hn p d hd] at hb
    exact crossed_of_crossedB 3 s hb (List.mem_range.mpr hd)
  · intro h
    obtain ⟨hd, _⟩ := crossed_spec 3 s h
    have hb := crossedB_of_crossed 3 s h
    rw [← crossedB_congr hs hn p d hd] at hb
    exact crossed_of_crossedB n s hb (List.mem_range.mpr hd)

/-- A face whose forward step stays inside the `3`-grid has the same end cells
    in every larger grid. -/
theorem faceEnds_congr {n : Nat} (hn : 3 ≤ n) (c : Cell) (k : Nat)
    (h : cellStep 3 c k ≠ none) : faceEnds n (c, k) = faceEnds 3 (c, k) := by
  obtain ⟨x, y, z⟩ := c
  unfold faceEnds
  rcases k with _ | _ | k <;> simp only [cellStep] at h ⊢ <;> split_ifs at h ⊢ <;>
    first | omega | simp_all

/-- Quad faces of a crossed edge of a supported field join the same cells in
    every grid with `n ≥ 3`. -/
theorem labels_faceEnds_congr {n : Nat} (hn : 3 ≤ n) (p : Lat) (d : Nat) (flip : Bool)
    (hd : d < 3)
    (htr : (d = 0 → 1 ≤ p.2.1 ∧ p.2.1 ≤ 2 ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 2) ∧
      (d = 1 → 1 ≤ p.1 ∧ p.1 ≤ 2 ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 2) ∧
      (d = 2 → 1 ≤ p.1 ∧ p.1 ≤ 2 ∧ 1 ≤ p.2.1 ∧ p.2.1 ≤ 2)) :
    ∀ lf ∈ labels p d flip, faceEnds n lf.face = faceEnds 3 lf.face := by
  obtain ⟨h0, h1, h2⟩ := htr
  interval_cases d
  · obtain ⟨a, b, c, e⟩ := h0 rfl
    cases flip <;>
    · intro lf hlf
      simp [labels, anchorCell, ij, addCell, a, c] at hlf
      rcases hlf with rfl | rfl | rfl | rfl <;> apply faceEnds_congr hn <;>
        simp [cellStep, addCell] <;> omega
  · obtain ⟨a, b, c, e⟩ := h1 rfl
    cases flip <;>
    · intro lf hlf
      simp [labels, anchorCell, ij, addCell, a, c] at hlf
      rcases hlf with rfl | rfl | rfl | rfl <;> apply faceEnds_congr hn <;>
        simp [cellStep, addCell] <;> omega
  · obtain ⟨a, b, c, e⟩ := h2 rfl
    cases flip <;>
    · intro lf hlf
      simp [labels, anchorCell, ij, addCell, a, c] at hlf
      rcases hlf with rfl | rfl | rfl | rfl <;> apply faceEnds_congr hn <;>
        simp [cellStep, addCell] <;> omega

/-- Face ends agree for every crossed edge of a supported field. -/
theorem crossed_faceEnds_congr {s : Lat → Bool} (hs : Supp s) {n : Nat} (hn : 3 ≤ n)
    {e : PadEdge} (he : e ∈ crossed n s) :
    ∀ lf ∈ labels e.1 e.2 (s e.1), faceEnds n lf.face = faceEnds 3 lf.face := by
  obtain ⟨p, d⟩ := e
  obtain ⟨hd, hp, _, hne⟩ := crossed_spec n s he
  have hpin := supp_pinned hs hn
  have ht := pinned_transverse n s hpin hp hne
  obtain ⟨a, b, c⟩ := supp_crossed_le hs hd hne
  refine labels_faceEnds_congr hn p d (s p) hd ⟨?_, ?_, ?_⟩
  · intro h0; obtain ⟨u1, _, u3, _⟩ := ht.1 h0; exact ⟨u1, b, u3, c⟩
  · intro h1; obtain ⟨u1, _, u3, _⟩ := ht.2.1 h1; exact ⟨u1, a, u3, c⟩
  · intro h2; obtain ⟨u1, _, u3, _⟩ := ht.2.2 h2; exact ⟨u1, a, u3, b⟩

/-- The directed mesh of a supported field has the same edges in every grid
    with `n ≥ 3`. -/
theorem mesh_mem_congr {s : Lat → Bool} (hs : Supp s) {n : Nat} (hn : 3 ≤ n)
    (a b : Cell) :
    (a, b) ∈ (cuberilleStencil n s).mesh ↔ (a, b) ∈ (cuberilleStencil 3 s).mesh := by
  constructor
  · intro h
    obtain ⟨q, hq, lf, hlf, hdir⟩ := mem_asmSurface.mp h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
    have he3 : e ∈ crossed 3 s := (crossed_mem_congr hs hn e).mp he
    refine mem_asmSurface.mpr ⟨_, List.mem_map.mpr ⟨e, he3, rfl⟩, lf, hlf, ?_⟩
    have hf := crossed_faceEnds_congr hs hn he lf hlf
    have hd : dirEdge (faceEnds n) lf = (a, b) := hdir
    show dirEdge (faceEnds 3) lf = (a, b)
    unfold dirEdge at hd ⊢
    rw [← hf]
    exact hd
  · intro h
    obtain ⟨q, hq, lf, hlf, hdir⟩ := mem_asmSurface.mp h
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
    have hen : e ∈ crossed n s := (crossed_mem_congr hs hn e).mpr he
    refine mem_asmSurface.mpr ⟨_, List.mem_map.mpr ⟨e, hen, rfl⟩, lf, hlf, ?_⟩
    have hf := crossed_faceEnds_congr hs hn hen lf hlf
    have hd : dirEdge (faceEnds 3) lf = (a, b) := hdir
    show dirEdge (faceEnds n) lf = (a, b)
    unfold dirEdge at hd ⊢
    rw [hf]
    exact hd

/-- Vertex set agrees. -/
theorem vertices_congr {s : Lat → Bool} (hs : Supp s) {n : Nat} (hn : 3 ≤ n) :
    QuadEuler.vertices (cuberilleStencil n s).mesh
      = QuadEuler.vertices (cuberilleStencil 3 s).mesh := by
  ext a
  simp only [QuadEuler.vertices, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨x, y⟩, h, rfl⟩
    exact ⟨(x, y), (mesh_mem_congr hs hn x y).mp h, rfl⟩
  · rintro ⟨⟨x, y⟩, h, rfl⟩
    exact ⟨(x, y), (mesh_mem_congr hs hn x y).mpr h, rfl⟩

/-- Undirected edge set agrees. -/
theorem undirected_congr {s : Lat → Bool} (hs : Supp s) {n : Nat} (hn : 3 ≤ n) :
    QuadEuler.undirected (cuberilleStencil n s).mesh
      = QuadEuler.undirected (cuberilleStencil 3 s).mesh := by
  ext t
  simp only [QuadEuler.undirected, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨x, y⟩, h, rfl⟩
    exact ⟨(x, y), (mesh_mem_congr hs hn x y).mp h, rfl⟩
  · rintro ⟨⟨x, y⟩, h, rfl⟩
    exact ⟨(x, y), (mesh_mem_congr hs hn x y).mpr h, rfl⟩

/-- The number of crossed lattice edges (quads) agrees. -/
theorem crossed_length_congr {s : Lat → Bool} (hs : Supp s) {n : Nat} (hn : 3 ≤ n) :
    (crossed n s).length = (crossed 3 s).length := by
  rw [← List.toFinset_card_of_nodup (nodup_crossed n s),
    ← List.toFinset_card_of_nodup (nodup_crossed 3 s)]
  congr 1
  ext e
  simp only [List.mem_toFinset]
  exact crossed_mem_congr hs hn e

/-! ### The body-diagonal pair: `χ = 3` in every grid with `n ≥ 3` -/

/-- Two `true` samples on a body diagonal of the central cube — the field
    `k = 24` of the bounded model in `Vdb/Cuberille.lean`. -/
def twoSign (p : Lat) : Bool := decide (p = (1, 2, 2) ∨ p = (2, 1, 1))

theorem twoSign_supp : Supp twoSign := by
  intro p hp
  have h : p = (1, 2, 2) ∨ p = (2, 1, 1) := by simpa [twoSign] using hp
  rcases h with rfl | rfl <;> simp

/-- At `n = 3`: `V = 15`, `E = 24`, `F = 12` and the directed mesh has no
    repeated edge (so it is edge-manifold). -/
theorem twoSign_counts_three :
    (QuadEuler.vertices (cuberilleStencil 3 twoSign).mesh).card = 15 ∧
    (QuadEuler.undirected (cuberilleStencil 3 twoSign).mesh).card = 24 ∧
    (crossed 3 twoSign).length = 12 ∧
    (cuberilleStencil 3 twoSign).mesh.Nodup := by native_decide

/-- **The `χ = 3` counterexample exists for every grid size `n ≥ 3`**: for the
    body-diagonal pair field, `V = 15`, `E = 24`, `F = 12` in every padded
    grid with `n ≥ 3`, so `χ = V − E + F = 3 ≠ 2`, with `E = 2 F`.
    Two closed surfaces touching in one dual vertex are edge-manifold but not
    a sphere. -/
theorem chi_three_general (n : Nat) (hn : 3 ≤ n) :
    (QuadEuler.vertices (cuberilleStencil n twoSign).mesh).card = 15 ∧
    (QuadEuler.undirected (cuberilleStencil n twoSign).mesh).card = 24 ∧
    (crossed n twoSign).length = 12 ∧
    ((QuadEuler.vertices (cuberilleStencil n twoSign).mesh).card : Int)
      - (QuadEuler.undirected (cuberilleStencil n twoSign).mesh).card
      + (crossed n twoSign).length = 3 := by
  obtain ⟨hV, hE, hF, _⟩ := twoSign_counts_three
  rw [vertices_congr twoSign_supp hn, undirected_congr twoSign_supp hn,
    crossed_length_congr twoSign_supp hn, hV, hE, hF]
  norm_num

end PadGrid

end Vdb
