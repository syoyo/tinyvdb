/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Side facts for the general-`n` padded-grid cuberille / DMC assembly
  (`Vdb/PadGrid.lean`, `Vdb/PadGridBoundary.lean`) that turn the generic
  edge count of `Vdb/QuadEuler.lean` into a statement about the assembled
  mesh: under shell pinning every crossed lattice edge emits a full quad of
  four labeled faces, and every used face joins two distinct cells (the
  shell-facing dummy faces `(c, c)` are never used).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.PadGridBoundary
import Vdb.QuadEuler

set_option linter.unusedSimpArgs false

namespace Vdb

namespace PadGrid

/-- What membership in `crossed` says about the edge. -/
theorem crossed_spec (n : Nat) (s : Lat → Bool) {p : Lat} {d : Nat}
    (h : (p, d) ∈ crossed n s) :
    d < 3 ∧ InLattice n p ∧ InLattice n (succN p d) ∧ s p ≠ s (succN p d) := by
  obtain ⟨p', hp, h'⟩ := List.mem_flatMap.mp h
  obtain ⟨d', hd', hd⟩ := List.mem_filterMap.mp h'
  have hd3 : d' < 3 := List.mem_range.mp hd'
  by_cases hcond : (decide (InLattice n (succN p' d')) && s p' != s (succN p' d')) = true
  · simp only [hcond, ite_true] at hd
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hd)
    obtain ⟨hc1, hc2⟩ := (Bool.and_eq_true _ _).mp hcond
    exact ⟨hd3, mem_latAll.mp hp, of_decide_eq_true hc1, bne_iff_ne.mp hc2⟩
  · simp only [hcond, ite_false] at hd
    cases hd

/-- A sign change cannot sit between two shell points. -/
theorem not_both_shell (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) {p q : Lat} (hne : s p ≠ s q) :
    ¬ (isShell n p = true ∧ isShell n q = true) := by
  rintro ⟨a, b⟩
  exact hne (by rw [hpin p a, hpin q b])

/-- Under shell pinning a crossed edge's two transverse coordinates are
    strictly inside the grid. -/
theorem pinned_transverse (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) {p : Lat} {d : Nat}
    (hp : InLattice n p) (hne : s p ≠ s (succN p d)) :
    (d = 0 → 1 ≤ p.2.1 ∧ p.2.1 < n ∧ 1 ≤ p.2.2 ∧ p.2.2 < n) ∧
    (d = 1 → 1 ≤ p.1 ∧ p.1 < n ∧ 1 ≤ p.2.2 ∧ p.2.2 < n) ∧
    (d = 2 → 1 ≤ p.1 ∧ p.1 < n ∧ 1 ≤ p.2.1 ∧ p.2.1 < n) := by
  have hns := not_both_shell n s hpin hne
  obtain ⟨hp1, hp2, hp3⟩ := hp
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc <;>
      refine hns ⟨shell_of_or n _ ?_, shell_of_or n _ ?_⟩ <;>
      (try simp [succN]) <;> omega
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc <;>
      refine hns ⟨shell_of_or n _ ?_, shell_of_or n _ ?_⟩ <;>
      (try simp [succN]) <;> omega
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hc <;>
      refine hns ⟨shell_of_or n _ ?_, shell_of_or n _ ?_⟩ <;>
      (try simp [succN]) <;> omega

/-- A face whose forward step stays in the grid joins two distinct cells. -/
theorem faceEnds_ne (n : Nat) (c : Cell) (k : Nat) (hk : cellStep n c k ≠ none) :
    (faceEnds n (c, k)).1 ≠ (faceEnds n (c, k)).2 := by
  obtain ⟨x, y, z⟩ := c
  unfold faceEnds
  rcases k with _ | _ | k <;> simp only [cellStep] at hk ⊢ <;> split_ifs at hk ⊢ <;>
    simp_all

/-- Under shell pinning a crossed edge emits a four-face quad whose faces all
    join two distinct cells. -/
theorem labels_ok (n : Nat) (p : Lat) (d : Nat) (flip : Bool) (hd : d < 3)
    (htr : (d = 0 → 1 ≤ p.2.1 ∧ p.2.1 < n ∧ 1 ≤ p.2.2 ∧ p.2.2 < n) ∧
      (d = 1 → 1 ≤ p.1 ∧ p.1 < n ∧ 1 ≤ p.2.2 ∧ p.2.2 < n) ∧
      (d = 2 → 1 ≤ p.1 ∧ p.1 < n ∧ 1 ≤ p.2.1 ∧ p.2.1 < n)) :
    (labels p d flip).length = 4 ∧
      ∀ lf ∈ labels p d flip, (faceEnds n lf.face).1 ≠ (faceEnds n lf.face).2 := by
  obtain ⟨h0, h1, h2⟩ := htr
  interval_cases d
  · obtain ⟨a, b, c, e⟩ := h0 rfl
    cases flip <;>
    · refine ⟨by simp [labels, anchorCell, ij, addCell, a, c], ?_⟩
      intro lf hlf
      simp [labels, anchorCell, ij, addCell, a, c] at hlf
      rcases hlf with rfl | rfl | rfl | rfl <;> apply faceEnds_ne <;>
        simp [cellStep, addCell] <;> omega
  · obtain ⟨a, b, c, e⟩ := h1 rfl
    cases flip <;>
    · refine ⟨by simp [labels, anchorCell, ij, addCell, a, c], ?_⟩
      intro lf hlf
      simp [labels, anchorCell, ij, addCell, a, c] at hlf
      rcases hlf with rfl | rfl | rfl | rfl <;> apply faceEnds_ne <;>
        simp [cellStep, addCell] <;> omega
  · obtain ⟨a, b, c, e⟩ := h2 rfl
    cases flip <;>
    · refine ⟨by simp [labels, anchorCell, ij, addCell, a, c], ?_⟩
      intro lf hlf
      simp [labels, anchorCell, ij, addCell, a, c] at hlf
      rcases hlf with rfl | rfl | rfl | rfl <;> apply faceEnds_ne <;>
        simp [cellStep, addCell] <;> omega

/-- Every crossed edge of a shell-pinned field emits a good quad. -/
theorem crossed_labels_ok (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) {e : PadEdge}
    (he : e ∈ crossed n s) :
    (labels e.1 e.2 (s e.1)).length = 4 ∧
      ∀ lf ∈ labels e.1 e.2 (s e.1),
        (faceEnds n lf.face).1 ≠ (faceEnds n lf.face).2 := by
  obtain ⟨p, d⟩ := e
  obtain ⟨hd, hp, _, hne⟩ := crossed_spec n s he
  exact labels_ok n p d (s p) hd (pinned_transverse n s hpin hp hne)

/-- The directed mesh has exactly four directed edges per crossed lattice
    edge (one quad each). -/
theorem mesh_length (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    (cuberilleStencil n s).mesh.length = 4 * (crossed n s).length := by
  have key : ∀ l : List PadEdge, (∀ e ∈ l, e ∈ crossed n s) →
      (asmSurface (faceEnds n)
        (l.map fun e => labels e.1 e.2 (s e.1))).length = 4 * l.length := by
    intro l
    induction l with
    | nil => intro _; simp [asmSurface]
    | cons e l ih =>
      intro h
      have he := (crossed_labels_ok n s hpin (h e (by simp))).1
      have := ih (fun x hx => h x (by simp [hx]))
      simp only [asmSurface, List.map_cons, List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons] at this ⊢
      omega
  exact key (crossed n s) (fun _ h => h)

/-- No mesh edge is a loop. -/
theorem mesh_loopless (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    ∀ a b, (a, b) ∈ (cuberilleStencil n s).mesh → a ≠ b := by
  intro a b hab
  obtain ⟨q, hq, lf, hlf, hdir⟩ := mem_asmSurface.mp hab
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  have hne := (crossed_labels_ok n s hpin he).2 lf hlf
  unfold dirEdge at hdir
  split_ifs at hdir
  · have h1 : (faceEnds n lf.face).1 = a := congrArg Prod.fst hdir
    have h2 : (faceEnds n lf.face).2 = b := congrArg Prod.snd hdir
    intro hc
    exact hne (by rw [h1, h2, hc])
  · have h1 : (faceEnds n lf.face).2 = a := congrArg Prod.fst hdir
    have h2 : (faceEnds n lf.face).1 = b := congrArg Prod.snd hdir
    intro hc
    exact hne (by rw [h1, h2, hc])

/-- **General-`n` edge count** (for every grid size `n`): a shell-pinned sign
    field whose assembled directed mesh uses each directed dual edge at most
    once has exactly `2 F` undirected dual edges, `F` the number of crossed
    lattice edges (one quad each). The no-repeat hypothesis cannot be dropped:
    the bounded model (`Cuberille.badEdgeCount`) has fields where an edge is
    used with multiplicity `4`. -/
theorem meshEdges_card_general (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hnd : (cuberilleStencil n s).mesh.Nodup) :
    (QuadEuler.undirected (cuberilleStencil n s).mesh).card = 2 * (crossed n s).length :=
  QuadEuler.undirected_card_eq_two_mul _ _ hnd (edgeClosed_general n s hpin)
    (mesh_loopless n s hpin) (mesh_length n s hpin)

/-- **General-`n` Euler characteristic of a manifold-edge cuberille mesh**:
    `χ = V - E + F = V - F`. This is *not* `2`: the vertex count `V`
    (dual cells with an outgoing edge) varies with the sign field, and
    `χ = 3` already occurs (two surfaces touching in a dual vertex, see
    `Cuberille.bounded_chi_manifold_not_chi2`). -/
theorem euler_general (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hnd : (cuberilleStencil n s).mesh.Nodup) :
    ((QuadEuler.vertices (cuberilleStencil n s).mesh).card : Int)
        - (QuadEuler.undirected (cuberilleStencil n s).mesh).card + (crossed n s).length
      = (QuadEuler.vertices (cuberilleStencil n s).mesh).card - (crossed n s).length :=
  QuadEuler.euler_eq_vertices_sub_faces _ _ hnd (edgeClosed_general n s hpin)
    (mesh_loopless n s hpin) (mesh_length n s hpin)

/-! ### Non-vacuity: a concrete instance of the hypotheses -/

/-- One `true` sample at `(1,1,1)`, everything else outside. -/
def singleSign (p : Lat) : Bool := decide (p = (1, 1, 1))

theorem singleSign_pinned (n : Nat) (hn : 3 ≤ n) :
    ∀ p, isShell n p = true → singleSign p = false := by
  intro p hp
  by_contra hc
  have h : p = (1, 1, 1) := by simpa [singleSign] using hc
  subst h
  simp [isShell] at hp
  omega

/-- The single-point field at `n = 3` has a duplicate-free directed mesh, so
    the general theorems apply to it (the hypothesis `hnd` is satisfiable). -/
theorem single_mesh_nodup :
    (cuberilleStencil 3 singleSign).mesh.Nodup := by native_decide

/-- Its counts: `V = 8`, `E = 12`, `F = 6`, hence `χ = 2` (the cube surface). -/
theorem single_counts :
    (QuadEuler.vertices (cuberilleStencil 3 singleSign).mesh).card = 8 ∧
    (QuadEuler.undirected (cuberilleStencil 3 singleSign).mesh).card = 12 ∧
    (crossed 3 singleSign).length = 6 := by native_decide

/-- `euler_general` instantiated: `χ = 8 - 6 = 2` for the single-point field. -/
theorem single_euler :
    ((QuadEuler.vertices (cuberilleStencil 3 singleSign).mesh).card : Int)
        - (QuadEuler.undirected (cuberilleStencil 3 singleSign).mesh).card
        + (crossed 3 singleSign).length = 2 := by
  rw [euler_general 3 singleSign (singleSign_pinned 3 le_rfl) single_mesh_nodup]
  obtain ⟨h1, _, h3⟩ := single_counts
  rw [h1, h3]
  norm_num

end PadGrid

end Vdb
