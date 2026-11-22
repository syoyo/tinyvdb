/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **General-`n` Euler characteristic of the DMC-1 mesh — conditional on
  the (open) edge-manifold/watertight theorem.**

  The assembled DMC-1 mesh (quads per crossed lattice edge, the
  patch-vertex correspondence of `Vdb/DmcOnePad.lean` for the bounded
  `n = 3` grid) is defined here for **arbitrary `n`**. Under shell
  pinning every crossed edge's transverse coordinates lie strictly
  inside the grid (`pinned_transverse`, reused from
  `Vdb/QuadEulerPad.lean`), so the four incident cells exist and are
  distinct; each cell contributes the patch vertex of its own MC soup
  (`patchesUsing`, at most one per edge). Hence every crossed lattice
  edge emits a full quad with four pairwise-distinct corners
  (`quad_ok`).

  What this module proves: with the hypothesis that the mesh is
  `EdgeClosed` — the exact content of the open wall (the general
  padded-grid DMC-1 manifold theorem) — the directed edge list has
  `2·|E| = 4·F` and the mesh's Euler characteristic is `χ = V − F`, for
  **every** grid size `n`, mirroring the general-`n` DMC-0 theorems
  (`Vdb/QuadEulerPad.lean`). The bounded `n = 3` (`Vdb/DmcOnePad.lean`)
  and `n = 4`-sample (`Vdb/DmcOnePad4.lean`) results are machine-checked
  evidence that the hypothesis holds there.

  What is **not** claimed: `EdgeClosed` for arbitrary `n` (the wall —
  the `Fin 2` torus cannot host the theorem, and a full padded-grid
  patch-stitching argument is multi-week); the DMC duality
  (`T-DMC1-DUAL`) beyond the bounded dual-component identity
  (`Vdb/DmcOneDual.lean`); any `χ = 2` statement (false in general on
  this family).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.DmcOne
import Vdb.DmcOnePad
import Vdb.McTable
import Vdb.PadGrid
import Vdb.QuadEuler
import Vdb.QuadEulerPad
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

namespace Vdb
namespace DmcOneEuler

abbrev Lat := Nat × Nat × Nat
abbrev Cell := Nat × Nat × Nat
abbrev PadEdge := Lat × Nat
abbrev V := DmcOnePad.V

/-! ### The general-`n` assembly -/

/-- The DMC-1 quad of a crossed lattice edge at arbitrary `n`: the four
    incident cells' patch vertices, cyclic (same order as the bounded
    model). -/
def dmcOneQuadN (s : Lat → Bool) (e : PadEdge) : List V :=
  if s e.1 == s (PadGrid.succN e.1 e.2) then [] else
    (DmcOnePad.incidentCells s e).map (fun c => DmcOnePad.cellPatchVertex s c e.1 e.2)

/-- The quads of a sign field on the `n^3`-cell padded grid (`n ≥ 1`). -/
def dmcOneQuads (n : Nat) (s : Lat → Bool) : List (List V) :=
  (PadGrid.latAll n).flatMap fun p =>
    (List.range 3).filterMap fun d =>
      if decide (PadGrid.InLattice n (PadGrid.succN p d)) && (s p != s (PadGrid.succN p d))
      then some (dmcOneQuadN s (p, d))
      else none

/-- The directed edge list of the assembled DMC-1 mesh. -/
def dmcOneMeshEdges (n : Nat) (s : Lat → Bool) : List (V × V) :=
  (dmcOneQuads n s).flatMap DmcOnePad.quadDirectedEdges

/-! ### Shell pinning forces the incident cells -/

/-- Under shell pinning, a crossed edge's transverse anchor cell exists. -/
theorem anchorCell_of_pinned (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (p : Lat) (d : Nat) (hd : d < 3) (hp : PadGrid.InLattice n p)
    (hne : s p ≠ s (PadGrid.succN p d)) :
    ∃ q : Cell, PadGrid.anchorCell p d = some q := by
  obtain ⟨h0, h1, h2⟩ := PadGrid.pinned_transverse n s hpin hp hne
  interval_cases d
  · obtain ⟨a, b, c, e⟩ := h0 rfl
    exact ⟨(p.1, p.2.1 - 1, p.2.2 - 1), by simp [PadGrid.anchorCell, a, c]⟩
  · obtain ⟨a, b, c, e⟩ := h1 rfl
    exact ⟨(p.1 - 1, p.2.1, p.2.2 - 1), by simp [PadGrid.anchorCell, a, c]⟩
  · obtain ⟨a, b, c, e⟩ := h2 rfl
    exact ⟨(p.1 - 1, p.2.1 - 1, p.2.2), by simp [PadGrid.anchorCell, a, c]⟩

/-- Under shell pinning the incident cells of a crossed edge are exactly
    four distinct cells. -/
theorem incidentCells_nodup (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (p : Lat) (d : Nat) (hd : d < 3) (hp : PadGrid.InLattice n p)
    (hne : s p ≠ s (PadGrid.succN p d)) :
    (DmcOnePad.incidentCells s (p, d)).Nodup ∧
      (DmcOnePad.incidentCells s (p, d)).length = 4 := by
  obtain ⟨q, hq⟩ := anchorCell_of_pinned n s hpin p d hd hp hne
  rcases q with ⟨x, y, z⟩
  rw [DmcOnePad.incidentCells, hq]
  obtain ⟨h0, h1, h2⟩ := PadGrid.pinned_transverse n s hpin hp hne
  interval_cases d
  · obtain ⟨a, b, c, e⟩ := h0 rfl
    cases hs : s p with
    | false => simp [PadGrid.ij, a, c, PadGrid.addCell, hs, List.nodup_cons, List.mem_cons]
    | true => simp [PadGrid.ij, a, c, PadGrid.addCell, hs, List.nodup_cons, List.mem_cons]
  · obtain ⟨a, b, c, e⟩ := h1 rfl
    cases hs : s p with
    | false => simp [PadGrid.ij, a, c, PadGrid.addCell, hs, List.nodup_cons, List.mem_cons]
    | true => simp [PadGrid.ij, a, c, PadGrid.addCell, hs, List.nodup_cons, List.mem_cons]
  · obtain ⟨a, b, c, e⟩ := h2 rfl
    cases hs : s p with
    | false => simp [PadGrid.ij, a, c, PadGrid.addCell, hs, List.nodup_cons, List.mem_cons]
    | true => simp [PadGrid.ij, a, c, PadGrid.addCell, hs, List.nodup_cons, List.mem_cons]

/-- `List.Nodup` survives an injective map into vertices. -/
theorem nodup_map_of_nodup_of_list (l : List Cell) (h : l.Nodup) (f : Cell → V)
    (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    obtain ⟨hx, hrest⟩ := h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hrest (fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))⟩
    intro hx'
    rw [List.mem_map] at hx'
    obtain ⟨b, hb, hfeq⟩ := hx'
    have hxeq : x = b := hinj x List.mem_cons_self b (List.mem_cons_of_mem x hb) hfeq.symm
    rw [← hxeq] at hb
    exact hx hb
/-- **Quad well-formedness**: under shell pinning, every crossed lattice
    edge emits a quad with exactly four pairwise-distinct corners. -/
theorem quad_ok (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (p : Lat) (d : Nat) (hd : d < 3) (hp : PadGrid.InLattice n p)
    (hne : s p ≠ s (PadGrid.succN p d)) :
    (dmcOneQuadN s (p, d)).length = 4 ∧ (dmcOneQuadN s (p, d)).Nodup := by
  obtain ⟨hnodup, hlen⟩ := incidentCells_nodup n s hpin p d hd hp hne
  unfold dmcOneQuadN
  rw [ite_eq_right (by rw [beq_iff_eq]; exact hne)]
  refine ⟨by rw [List.length_map, hlen], ?_⟩
  exact nodup_map_of_nodup_of_list _ hnodup (fun c => DmcOnePad.cellPatchVertex s c p d)
    (fun a ha b hb hab => congrArg Prod.fst hab)

/-- Every edge of a four-corner quad with distinct corners joins distinct
    vertices. -/
theorem quad_edges_ne {x y z dd a b : V} (hq : ([x, y, z, dd] : List V).Nodup)
    (h : (a, b) ∈ DmcOnePad.quadDirectedEdges [x, y, z, dd]) : a ≠ b := by
  have hxy : x ≠ y := by
    have hx : x ∉ [y, z, dd] := (List.nodup_cons.mp hq).1
    intro e; subst e; exact hx (by simp)
  have h2 : (y :: z :: [dd]).Nodup := (List.nodup_cons.mp hq).2
  have hy1 : y ≠ z := by
    have hy : y ∉ [z, dd] := (List.nodup_cons.mp h2).1
    intro e; subst e; exact hy (by simp)
  have hy2 : y ≠ dd := by
    have hy : y ∉ [z, dd] := (List.nodup_cons.mp h2).1
    intro e; subst e; exact hy (by simp)
  have h3 : (z :: [dd]).Nodup := (List.nodup_cons.mp h2).2
  have hz1 : z ≠ dd := by
    have hz : z ∉ [dd] := (List.nodup_cons.mp h3).1
    intro e; subst e; exact hz (by simp)
  have hx2 : x ≠ z := by
    have hx : x ∉ [y, z, dd] := (List.nodup_cons.mp hq).1
    intro e; subst e; exact hx (by simp)
  have hx3 : x ≠ dd := by
    have hx : x ∉ [y, z, dd] := (List.nodup_cons.mp hq).1
    intro e; subst e; exact hx (by simp)
  have hlist : DmcOnePad.quadDirectedEdges [x, y, z, dd] = [(x, y), (y, z), (z, dd), (dd, x)] := rfl
  rw [hlist] at h
  simp only [List.mem_cons, List.not_mem_nil] at h
  obtain h | h | h | h | h := h
  · obtain ⟨rfl, rfl⟩ := h; exact hxy
  · obtain ⟨rfl, rfl⟩ := h; exact hy1
  · obtain ⟨rfl, rfl⟩ := h; exact hz1
  · obtain ⟨rfl, rfl⟩ := h; exact fun hc => hx3 hc.symm
  · exact absurd h (by simp)


/-- Mesh edges of a shell-pinned field connect distinct vertices (no
    loops). -/
theorem mesh_loopless (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) {a b : V}
    (hmem : (a, b) ∈ dmcOneMeshEdges n s) : a ≠ b := by
  unfold dmcOneMeshEdges at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨q, hqmem, hedgemem⟩ := hmem
  unfold dmcOneQuads at hqmem
  rw [List.mem_flatMap] at hqmem
  obtain ⟨p, hpmem, hdmem⟩ := hqmem
  rw [List.mem_filterMap] at hdmem
  obtain ⟨d, hdmem', hqeq⟩ := hdmem
  have hd3 : d < 3 := List.mem_range.mp hdmem'
  by_cases hcond : (decide (PadGrid.InLattice n (PadGrid.succN p d)) &&
      (s p != s (PadGrid.succN p d))) = true
  · have hp3 : PadGrid.InLattice n p := PadGrid.mem_latAll.mp hpmem
    have hne : s p ≠ s (PadGrid.succN p d) := by
      have hc := (Bool.and_eq_true _ _).mp hcond
      simpa [bne_iff_ne] using hc.2
    obtain ⟨hlen, hnodup⟩ := quad_ok n s hpin p d hd3 hp3 hne
    have hqE : dmcOneQuadN s (p, d) = q := by
      have h1 := hqeq
      rw [ite_eq_left hcond] at h1
      exact Option.some.inj h1
    subst q
    unfold dmcOneQuadN at hedgemem hlen hnodup
    rw [ite_eq_right (by rw [beq_iff_eq]; exact hne)] at hedgemem hlen hnodup
    rw [List.length_map] at hlen
    cases hc : DmcOnePad.incidentCells s (p, d) with
    | nil => rw [hc] at hlen; simp at hlen
    | cons a' rest =>
      cases rest with
      | nil => rw [hc] at hlen; simp at hlen
      | cons b' rest2 =>
        cases rest2 with
        | nil => rw [hc] at hlen; simp at hlen
        | cons c' rest3 =>
          cases rest3 with
          | nil => rw [hc] at hlen; simp at hlen
          | cons dd' rest4 =>
            cases rest4 with
            | nil =>
              rw [hc, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
                List.map_nil] at hedgemem hnodup
              exact quad_edges_ne hnodup hedgemem
            | cons e' _ =>
              rw [hc] at hlen
              simp only [List.length_cons] at hlen
              omega
  · rw [ite_eq_right (by simpa using hcond)] at hqeq
    simp at hqeq

/-- The number of directed edges of a quad equals its corner count. -/
theorem quadDirectedEdges_length (q : List V) :
    (DmcOnePad.quadDirectedEdges q).length = q.length := by
  simp [DmcOnePad.quadDirectedEdges]
  omega

/-- Length of the flattened list of directed edges of a list of quads, when
    every quad has four corners. -/
theorem length_flatMap_quadDirectedEdges (qs : List (List V))
    (h : ∀ q ∈ qs, q.length = 4) :
    (qs.flatMap DmcOnePad.quadDirectedEdges).length = 4 * qs.length := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have hq : q.length = 4 := h q List.mem_cons_self
    have htail : ∀ x ∈ qs, x.length = 4 := fun x hx => h x (List.mem_cons_of_mem q hx)
    rw [List.flatMap_cons, List.length_append, quadDirectedEdges_length, hq, ih htail,
      List.length_cons]
    omega

/-- `dmcOneQuads` and the cuberille's `crossed` enumerate exactly the same
    number of (point, direction) pairs. -/
theorem dmcOneQuads_length (n : Nat) (s : Lat → Bool) :
    (dmcOneQuads n s).length = (PadGrid.crossed n s).length := by
  have key : ∀ p : Lat,
      ((List.range 3).filterMap
        (fun d => if decide (PadGrid.InLattice n (PadGrid.succN p d)) && (s p != s (PadGrid.succN p d))
           then some (dmcOneQuadN s (p, d)) else none)).length
      = ((List.range 3).filterMap
        (fun d => if decide (PadGrid.InLattice n (PadGrid.succN p d)) && (s p != s (PadGrid.succN p d))
           then some (p, d) else none)).length := by
    intro p
    rw [List.length_filterMap_eq_countP, List.length_filterMap_eq_countP]
    apply List.countP_congr
    intro d _
    by_cases h : (decide (PadGrid.InLattice n (PadGrid.succN p d)) && (s p != s (PadGrid.succN p d))) = true
    · rw [ite_eq_left h, ite_eq_left h]; rfl
    · rw [ite_eq_right (by simpa using h), ite_eq_right (by simpa using h)]; rfl
  unfold dmcOneQuads PadGrid.crossed
  rw [List.length_flatMap, List.length_flatMap, List.map_congr_left (fun p _ => key p)]

/-- Every emitted quad of a shell-pinned field has exactly four corners. -/
theorem dmcOneQuad_length (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    {q : List V} (hq : q ∈ dmcOneQuads n s) : q.length = 4 := by
  unfold dmcOneQuads at hq
  rw [List.mem_flatMap] at hq
  obtain ⟨p, hpmem, hdmem⟩ := hq
  rw [List.mem_filterMap] at hdmem
  obtain ⟨d, hdmem', hqeq⟩ := hdmem
  have hd3 : d < 3 := List.mem_range.mp hdmem'
  by_cases hcond : (decide (PadGrid.InLattice n (PadGrid.succN p d)) &&
      (s p != s (PadGrid.succN p d))) = true
  · have hp3 : PadGrid.InLattice n p := PadGrid.mem_latAll.mp hpmem
    have hne : s p ≠ s (PadGrid.succN p d) := by
      have hc := (Bool.and_eq_true _ _).mp hcond
      simpa [bne_iff_ne] using hc.2
    obtain ⟨hlen, _⟩ := quad_ok n s hpin p d hd3 hp3 hne
    have hqE : dmcOneQuadN s (p, d) = q := by
      have h1 := hqeq
      rw [ite_eq_left hcond] at h1
      exact Option.some.inj h1
    rw [← hqE]
    exact hlen
  · rw [ite_eq_right (by simpa using hcond)] at hqeq
    simp at hqeq

/-- The directed mesh edge list has exactly four edges per crossed lattice
    edge: `|mesh| = 4 · |crossed|`. -/
theorem mesh_length (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false) :
    (dmcOneMeshEdges n s).length = 4 * (PadGrid.crossed n s).length := by
  unfold dmcOneMeshEdges
  rw [length_flatMap_quadDirectedEdges (dmcOneQuads n s)
    (fun q hq => dmcOneQuad_length n s hpin hq), dmcOneQuads_length]

/-- **General-`n` DMC-1 edge count** (shell-pinned; the no-repeat hypothesis
    cannot be dropped — the bounded model has multiplicity pathologies):
    every crossed lattice edge emits one quad of four distinct corners, so
    `2·|E| = 4·F` provided the mesh is duplicate-free and watertight. -/
theorem meshEdges_card_dmc1 (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (hcl : EdgeClosed (dmcOneMeshEdges n s))
    (hnd : (dmcOneMeshEdges n s).Nodup) :
    (QuadEuler.undirected (dmcOneMeshEdges n s)).card = 2 * (PadGrid.crossed n s).length :=
  QuadEuler.undirected_card_eq_two_mul _ _ hnd hcl (fun _a _b h => mesh_loopless n s hpin h)
    (mesh_length n s hpin)

/-- **General-`n` Euler characteristic of a manifold-edge DMC-1 mesh**
    (shell pinned, no repeated directed edge, watertight): `χ = V − F`.
    The `EdgeClosed` hypothesis is the exact content of the open wall. -/
theorem euler_general_dmc1 (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, PadGrid.isShell n p = true → s p = false)
    (hcl : EdgeClosed (dmcOneMeshEdges n s))
    (hnd : (dmcOneMeshEdges n s).Nodup) :
    ((QuadEuler.vertices (dmcOneMeshEdges n s)).card : Int)
        - (QuadEuler.undirected (dmcOneMeshEdges n s)).card + (PadGrid.crossed n s).length
      = (QuadEuler.vertices (dmcOneMeshEdges n s)).card - (PadGrid.crossed n s).length :=
  QuadEuler.euler_eq_vertices_sub_faces _ _ hnd hcl (fun _a _b h => mesh_loopless n s hpin h)
    (mesh_length n s hpin)
