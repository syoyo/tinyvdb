/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The **dual-vertex pinch** behind the `χ = 3` behaviour of the
  general-`n` cuberille / DMC mesh (`Vdb/QuadEulerPad.lean`).

  The four body diagonals of the `{1,2}^3` sample cube of the padded
  `n ≥ 3` grid carry sign fields with exactly two interior `true` samples
  (the antipodal pair). For every such field, in every grid with `3 ≤ n`:

  * the assembled quad mesh is **edge-manifold** (a repeated directed dual
    edge never occurs) and **closed** (`balanced_general`), as with one
    bump;
  * its vertex set is the union of the two bump meshes' vertex sets, its
    undirected edge set is the (disjoint) union of the two bump meshes'
    edge sets, and the two vertex sets meet in exactly the **central
    cell** `(1,1,1)` — the dual vertex where the two closed surfaces
    touch;
  * hence `V = 8 + 8 − 1 = 15`, `E = 12 + 12 = 24`, `F = 6 + 6 = 12` and
    `χ = V − E + F = 2 + 2 − 1 = 3`.

  So the four `χ = 3` witnesses of the bounded Fin-4 landscape
  (`Cuberille.bounded_chi_manifold_not_chi2`, `k ∈ {24, 36, 66, 129}`,
  decoded bit-by-bit: 24 = bits 3,4; 36 = bits 2,5; 66 = bits 1,6;
  129 = bits 0,7 — exactly the four body diagonals) are **two closed
  edge-manifold surfaces pinched at one dual vertex**: each component is
  an ordinary cube-surface bump (`χ = 2`) and gluing at a single shared
  vertex drops `χ` by one.

  What this module does **not** claim: a general genus/connectivity
  theorem for arbitrary checkerboard-free fields (it would need the
  orientability and component machinery for the dual mesh; the general
  `χ = 2 − 2g + …` content of `χ` stays open), and no claim is made for
  fields outside `{1,2}^3`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.QuadEulerPad
import Vdb.QuadEulerEmbed

set_option linter.unusedSimpArgs false

namespace Vdb

namespace PadGrid

/-- A single-point bump field at `p`. -/
def bump (p : Lat) : Lat → Bool := fun q => decide (q = p)

/-- The `i`-th body diagonal of the `{1,2}^3` cube, `i < 4` (out-of-range
    `i` decodes to the fourth diagonal). `antidiagPt i b` is its first
    (`b = false`) or second (`b = true`) interior point. -/
def antidiagPt (i : Nat) (b : Bool) : Lat :=
  match i with
  | 0 => if b then (2, 2, 2) else (1, 1, 1)
  | 1 => if b then (2, 2, 1) else (1, 1, 2)
  | 2 => if b then (2, 1, 2) else (1, 2, 1)
  | _ => if b then (2, 1, 1) else (1, 2, 2)

/-- The antipodal pair field of the `i`-th body diagonal. -/
def antidiag (i : Nat) (q : Lat) : Bool :=
  match i with
  | 0 => decide (q = (1, 1, 1) ∨ q = (2, 2, 2))
  | 1 => decide (q = (1, 1, 2) ∨ q = (2, 2, 1))
  | 2 => decide (q = (1, 2, 1) ∨ q = (2, 1, 2))
  | _ => decide (q = (1, 2, 2) ∨ q = (2, 1, 1))

/-! ### Support and shell pinning -/

theorem bump_supp (p : Lat)
    (hb : (1 ≤ p.1 ∧ p.1 ≤ 2) ∧ (1 ≤ p.2.1 ∧ p.2.1 ≤ 2) ∧ (1 ≤ p.2.2 ∧ p.2.2 ≤ 2)) :
    Supp (bump p) := by
  intro q hq
  have hq' : q = p := by simpa [bump] using hq
  exact hq' ▸ hb

theorem antidiag_supp (i : Nat) (hi : i < 4) : Supp (antidiag i) := by
  intro q hq
  interval_cases i <;> simp only [antidiag] at hq <;>
    obtain h | h := of_decide_eq_true hq <;> subst h <;> decide

theorem antidiagPt_bounds (i : Nat) (hi : i < 4) (b : Bool) :
    (1 ≤ (antidiagPt i b).1 ∧ (antidiagPt i b).1 ≤ 2) ∧
    (1 ≤ (antidiagPt i b).2.1 ∧ (antidiagPt i b).2.1 ≤ 2) ∧
    (1 ≤ (antidiagPt i b).2.2 ∧ (antidiagPt i b).2.2 ≤ 2) := by
  interval_cases i <;> cases b <;> simp [antidiagPt]

/-! ### The abstract glue: χ drops by one per identified vertex shared by
    two otherwise disjoint closed surfaces -/

/-- **Vertex/edge counting for an identified-vertex glue**: if two meshes
    share no undirected edge and their vertex sets meet in exactly one
    vertex (a dual-vertex pinch), their Euler characteristics add minus
    one. -/
theorem euler_glue {ι : Type*} [DecidableEq ι] {s₁ s₂ : Finset ι}
    {e₁ e₂ : Finset (Sym2 ι)} (hdisj : Disjoint e₁ e₂) (hvint : (s₁ ∩ s₂).card = 1)
    (F₁ F₂ : Nat) :
    ((s₁ ∪ s₂).card : Int) - ((e₁ ∪ e₂).card : Int) + ((F₁ : Int) + F₂)
      = (((s₁.card : Int) - e₁.card + F₁)
          + ((s₂.card : Int) - e₂.card + F₂) - 1) := by
  have hV : ((s₁ ∪ s₂).card : Int) = s₁.card + s₂.card - 1 := by
    have h := Finset.card_union_add_card_inter s₁ s₂
    rw [hvint] at h
    omega
  have hE : ((e₁ ∪ e₂).card : Int) = e₁.card + e₂.card := by
    have hd := Finset.disjoint_iff_inter_eq_empty.mp hdisj
    have h := Finset.card_union_add_card_inter e₁ e₂
    rw [hd, Finset.card_empty] at h
    omega
  rw [hV, hE]
  ring

/-! ### The antipodal pair: counts and decomposition at `n = 3` -/

/-- The decomposition of an antipodal pair at `n = 3`, machine-checked:
    the undirected edge sets of the two bumps are disjoint and their union
    is the pair's edge set; the vertex sets union to the pair's vertex set
    and meet in the central cell `(1,1,1)`. -/
theorem antidiag_pair_facts_three (i : Nat) (hi : i < 4) :
    QuadEuler.undirected (cuberilleStencil 3 (antidiag i)).mesh
      = QuadEuler.undirected (cuberilleStencil 3 (bump (antidiagPt i false))).mesh
        ∪ QuadEuler.undirected (cuberilleStencil 3 (bump (antidiagPt i true))).mesh ∧
    (QuadEuler.undirected (cuberilleStencil 3 (bump (antidiagPt i false))).mesh
        ∩ QuadEuler.undirected (cuberilleStencil 3 (bump (antidiagPt i true))).mesh).card = 0 ∧
    QuadEuler.vertices (cuberilleStencil 3 (antidiag i)).mesh
      = QuadEuler.vertices (cuberilleStencil 3 (bump (antidiagPt i false))).mesh
        ∪ QuadEuler.vertices (cuberilleStencil 3 (bump (antidiagPt i true))).mesh ∧
    QuadEuler.vertices (cuberilleStencil 3 (bump (antidiagPt i false))).mesh
        ∩ QuadEuler.vertices (cuberilleStencil 3 (bump (antidiagPt i true))).mesh
      = {(1, 1, 1)} ∧
    (crossed 3 (antidiag i)).length = 12 ∧
    (crossed 3 (bump (antidiagPt i false))).length = 6 ∧
    (crossed 3 (bump (antidiagPt i true))).length = 6 ∧
    (cuberilleStencil 3 (antidiag i)).mesh.Nodup ∧
    (cuberilleStencil 3 (bump (antidiagPt i false))).mesh.Nodup ∧
    (cuberilleStencil 3 (bump (antidiagPt i true))).mesh.Nodup := by
  interval_cases i <;> native_decide

/-- The decomposition holds in every padded grid with `n ≥ 3` (the
    `{1,2}^3`-supported fields have `n`-invariant mesh Finsets). -/
theorem antidiag_decomposition (n : Nat) (hn : 3 ≤ n) (i : Nat) (hi : i < 4) :
    QuadEuler.undirected (cuberilleStencil n (antidiag i)).mesh
      = QuadEuler.undirected (cuberilleStencil n (bump (antidiagPt i false))).mesh
        ∪ QuadEuler.undirected (cuberilleStencil n (bump (antidiagPt i true))).mesh ∧
    Disjoint (QuadEuler.undirected (cuberilleStencil n (bump (antidiagPt i false))).mesh)
      (QuadEuler.undirected (cuberilleStencil n (bump (antidiagPt i true))).mesh) ∧
    QuadEuler.vertices (cuberilleStencil n (antidiag i)).mesh
      = QuadEuler.vertices (cuberilleStencil n (bump (antidiagPt i false))).mesh
        ∪ QuadEuler.vertices (cuberilleStencil n (bump (antidiagPt i true))).mesh ∧
    ((QuadEuler.vertices (cuberilleStencil n (bump (antidiagPt i false))).mesh
        ∩ QuadEuler.vertices (cuberilleStencil n (bump (antidiagPt i true))).mesh).card = 1) := by
  obtain ⟨hE3u, hD0, hV3u, hI, _, _, _, _, _, _⟩ := antidiag_pair_facts_three i hi
  have hD : Disjoint
      (QuadEuler.undirected (cuberilleStencil 3 (bump (antidiagPt i false))).mesh)
      (QuadEuler.undirected (cuberilleStencil 3 (bump (antidiagPt i true))).mesh) := by
    rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.card_eq_zero]
    exact hD0
  rw [undirected_congr (antidiag_supp i hi) hn,
    undirected_congr (bump_supp _ (antidiagPt_bounds i hi false)) hn,
    undirected_congr (bump_supp _ (antidiagPt_bounds i hi true)) hn,
    vertices_congr (antidiag_supp i hi) hn,
    vertices_congr (bump_supp _ (antidiagPt_bounds i hi false)) hn,
    vertices_congr (bump_supp _ (antidiagPt_bounds i hi true)) hn]
  refine ⟨hE3u, hD, hV3u, ?_⟩
  rw [hI]
  decide

/-- Crossed-edge (quad) counts add across the pinch, in every grid with
    `n ≥ 3`. -/
theorem antidiag_crossed_add (n : Nat) (hn : 3 ≤ n) (i : Nat) (hi : i < 4) :
    (crossed n (antidiag i)).length
      = (crossed n (bump (antidiagPt i false))).length
        + (crossed n (bump (antidiagPt i true))).length := by
  rw [crossed_length_congr (antidiag_supp i hi) hn,
    crossed_length_congr (bump_supp _ (antidiagPt_bounds i hi false)) hn,
    crossed_length_congr (bump_supp _ (antidiagPt_bounds i hi true)) hn]
  obtain ⟨_, _, _, _, hF, hF0, hF1, _, _, _⟩ := antidiag_pair_facts_three i hi
  omega

/-! ### The one-bump Euler characteristic, for every `n ≥ 3` -/

/-- Counts of a bump field at `n = 3`, for every single interior point of
    `{1,2}^3`. -/
theorem bump_counts_three (p : Lat)
    (hb : (1 ≤ p.1 ∧ p.1 ≤ 2) ∧ (1 ≤ p.2.1 ∧ p.2.1 ≤ 2) ∧ (1 ≤ p.2.2 ∧ p.2.2 ≤ 2)) :
    (QuadEuler.vertices (cuberilleStencil 3 (bump p)).mesh).card = 8 ∧
    (QuadEuler.undirected (cuberilleStencil 3 (bump p)).mesh).card = 12 ∧
    (crossed 3 (bump p)).length = 6 := by
  obtain ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, ⟨h3, h3'⟩⟩ := hb
  obtain ⟨x, y, z⟩ := p
  interval_cases x <;> interval_cases y <;> interval_cases z <;> native_decide

/-- **A single bump is a sphere**: `χ = 2` for every `n ≥ 3` (the
    `supp`-supported fields have `n`-invariant counts). -/
theorem bump_euler_general (p : Lat)
    (hb : (1 ≤ p.1 ∧ p.1 ≤ 2) ∧ (1 ≤ p.2.1 ∧ p.2.1 ≤ 2) ∧ (1 ≤ p.2.2 ∧ p.2.2 ≤ 2))
    (hn : 3 ≤ n) :
    ((QuadEuler.vertices (cuberilleStencil n (bump p)).mesh).card : Int)
      - (QuadEuler.undirected (cuberilleStencil n (bump p)).mesh).card
      + (crossed n (bump p)).length = 2 := by
  have hVp : QuadEuler.vertices (cuberilleStencil n (bump p)).mesh
      = QuadEuler.vertices (cuberilleStencil 3 (bump p)).mesh := vertices_congr (bump_supp p hb) hn
  have hEp : QuadEuler.undirected (cuberilleStencil n (bump p)).mesh
      = QuadEuler.undirected (cuberilleStencil 3 (bump p)).mesh := undirected_congr (bump_supp p hb) hn
  have hFp : (crossed n (bump p)).length = (crossed 3 (bump p)).length :=
    crossed_length_congr (bump_supp p hb) hn
  rw [hVp, hEp, hFp]
  obtain ⟨hV, hE, hF⟩ := bump_counts_three p hb
  rw [hV, hE, hF]
  norm_num

/-! ### The antipodal pair: `χ = 3` for every `n ≥ 3`, via the pinch -/

/-- Counts of an antipodal pair at `n = 3` (any single interior point of
    `{1,2}^3` pairs). -/
theorem antidiag_counts_three (i : Nat) (hi : i < 4) :
    (QuadEuler.vertices (cuberilleStencil 3 (antidiag i)).mesh).card = 15 ∧
    (QuadEuler.undirected (cuberilleStencil 3 (antidiag i)).mesh).card = 24 ∧
    (crossed 3 (antidiag i)).length = 12 := by
  interval_cases i <;> native_decide

/-- **The `χ = 3` field counts for every `n ≥ 3`**: `V = 15`, `E = 24`,
    `F = 12`. Generalises `QuadEulerEmbed.chi_three_general` to all four
    body diagonals. -/
theorem antidiag_counts_general (n : Nat) (hn : 3 ≤ n) (i : Nat) (hi : i < 4) :
    (QuadEuler.vertices (cuberilleStencil n (antidiag i)).mesh).card = 15 ∧
    (QuadEuler.undirected (cuberilleStencil n (antidiag i)).mesh).card = 24 ∧
    (crossed n (antidiag i)).length = 12 := by
  rw [vertices_congr (antidiag_supp i hi) hn,
    undirected_congr (antidiag_supp i hi) hn,
    crossed_length_congr (antidiag_supp i hi) hn]
  exact antidiag_counts_three i hi

/-- **The `χ = 3` mechanism (every `n ≥ 3`)**: for an antipodal body-diagonal
    pair, the Euler characteristic of the assembled mesh is computed by the
    glue lemma from the two bump Euler characteristics — two closed
    edge-manifold surfaces (`χ = 2` each) sharing exactly the central dual
    vertex `(1,1,1)`, so `χ = 2 + 2 − 1 = 3`. -/
theorem antidiag_euler_via_glue (n : Nat) (hn : 3 ≤ n) (i : Nat) (hi : i < 4) :
    ((QuadEuler.vertices (cuberilleStencil n (antidiag i)).mesh).card : Int)
      - (QuadEuler.undirected (cuberilleStencil n (antidiag i)).mesh).card
      + (crossed n (antidiag i)).length = 3 := by
  obtain ⟨hE, hD, hV, hI⟩ := antidiag_decomposition n hn i hi
  have hsum := antidiag_crossed_add n hn i hi
  have hχ0 := bump_euler_general (antidiagPt i false) (antidiagPt_bounds i hi false) hn
  have hχ1 := bump_euler_general (antidiagPt i true) (antidiagPt_bounds i hi true) hn
  rw [hV, hE, hsum]
  have g := euler_glue hD hI
    (crossed n (bump (antidiagPt i false))).length
    (crossed n (bump (antidiagPt i true))).length
  omega

/-- **All four body-diagonal pairs have `χ = 3` in every padded grid with
    `n ≥ 3`** — the `k ∈ {24, 36, 66, 129}` edge-manifold, non-`χ = 2`
    witnesses of the bounded landscape, embedded. Each mesh is closed
    (`balanced_general`) and edge-manifold at `n = 3` (native check in
    `antidiag_pair_facts_three`), a pinched pair of bump surfaces. -/
theorem antidiag_chi_three (n : Nat) (hn : 3 ≤ n) (i : Nat) (hi : i < 4) :
    ((QuadEuler.vertices (cuberilleStencil n (antidiag i)).mesh).card : Int)
      - (QuadEuler.undirected (cuberilleStencil n (antidiag i)).mesh).card
      + (crossed n (antidiag i)).length = 3 :=
  antidiag_euler_via_glue n hn i hi

/-- The `twoSign` field of `Vdb/QuadEulerEmbed.lean` is the fourth body
    diagonal. -/
theorem twoSign_eq_antidiag : twoSign = antidiag 3 := rfl

/-- The `χ = 3` counterexample of `QuadEulerEmbed.chi_three_general`,
    re-derived here through the pinch: it is two cube-surface bumps
    touching at the central dual vertex. -/
theorem chi_three_pinch (n : Nat) (hn : 3 ≤ n) :
    ((QuadEuler.vertices (cuberilleStencil n twoSign).mesh).card : Int)
      - (QuadEuler.undirected (cuberilleStencil n twoSign).mesh).card
      + (crossed n twoSign).length = 3 := by
  rw [twoSign_eq_antidiag]
  exact antidiag_chi_three n hn 3 (by omega)

/-- The pair meshes are duplicate-free (edge-manifold) at `n = 3`; the
    hypothesis of `euler_general` is satisfiable for every pair. -/
theorem antidiag_mesh_nodup_three (i : Nat) (hi : i < 4) :
    (cuberilleStencil 3 (antidiag i)).mesh.Nodup ∧
    (cuberilleStencil 3 (bump (antidiagPt i false))).mesh.Nodup ∧
    (cuberilleStencil 3 (bump (antidiagPt i true))).mesh.Nodup := by
  obtain ⟨_, _, _, _, _, _, _, h0, h1, h2⟩ := antidiag_pair_facts_three i hi
  exact ⟨h0, h1, h2⟩

end PadGrid

end Vdb
