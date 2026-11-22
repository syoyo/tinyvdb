/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume
  operators.

  A general Poincaré–Lefschetz statement for the cubical complexes of
  `Vdb/Euler.lean`. The two concrete instances (`chiBoundary_block2_eq_two_chi`,
  `chiBoundary_shell3_eq_two_chi`) are deliberately NOT reproduced here; this
  module isolates the general structural content and the exact missing step.

  Landed:

  * `boundaryFaces_subset_cellsOf`, `boundaryEdges_subset_cellsOf`,
    `boundaryVertices_subset_cellsOf` — the boundary is a subcomplex of the
    solid (at each cell dimension);
  * `interiorVertices`, `interiorEdges`, `interiorFaces`, `chiInterior` — the
    off-boundary ("open") cells of a solid, including the top-dimensional
    cubes;
  * `mem_cubeFaces_iff_mem_adjacentCubes`, `cubeFaces_card`,
    `boundaryFaces_card_add_six` — the codimension-one double count
    `|∂faces| + 6·|K| = 2·|faces(K)|`, plus its rearrangement
    `6·|K| = |∂faces| + 2·|shared faces|`;
  * `chiOf_eq_chiBoundary_add_chiInterior` — the exact inclusion–exclusion
    decomposition `χ(S) = χ(∂S) + χ(S \ ∂S)`, proved from `Finset` card
    subtraction at each dimension;
  * `HasInteriorDuality` — the single missing input, `χ(S \ ∂S) = −χ(S)`;
  * `interiorDuality_iff_chiBoundary` — with the decomposition in hand, the
    Poincaré–Lefschetz relation `χ(∂S) = 2·χ(S)` is *equivalent* to that input,
    and the equivalence is fully proved (no axioms beyond the standard trio).

  Honest wall: `HasInteriorDuality` is not proved for a general finite cube set.
  For a compact odd-dimensional manifold with boundary it is exactly Poincaré /
  Euler–Maclaurin duality; mathlib 4.35 has simplicial complexes and homological
  Euler characteristics but no cubical-complex duality theorem, so the general
  implication cannot be closed inside this slice. The equivalence above shows
  that the duality hypothesis is not merely sufficient but *necessary* for the
  χ-level statement.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Euler

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace Vdb

/-! ### The boundary is a subcomplex of the solid -/

theorem boundaryFaces_subset_cellsOf (K : Finset C3) :
    boundaryFaces K ⊆ (cellsOf K).2.2 := by
  intro f hf
  simp only [boundaryFaces, Finset.mem_filter] at hf
  simpa [cellsOf] using hf.1

theorem boundaryEdges_subset_cellsOf (K : Finset C3) :
    (boundaryCells K).2.1 ⊆ (cellsOf K).2.1 := by
  intro e he
  simp only [boundaryCells, Finset.mem_biUnion] at he
  rcases he with ⟨f, hf, hef⟩
  simp only [cellsOf, Finset.mem_biUnion]
  exact ⟨f, (by simpa [cellsOf] using boundaryFaces_subset_cellsOf K hf), hef⟩

theorem boundaryVertices_subset_cellsOf (K : Finset C3) :
    (boundaryCells K).1 ⊆ (cellsOf K).1 := by
  intro v hv
  simp only [boundaryCells, Finset.mem_biUnion] at hv
  rcases hv with ⟨e, he, hve⟩
  have he' : e ∈ (boundaryCells K).2.1 := by
    simpa [boundaryCells] using he
  simp only [cellsOf, Finset.mem_biUnion]
  exact ⟨e, (by simpa [cellsOf] using boundaryEdges_subset_cellsOf K he'), hve⟩

/-! ### Face double counting (codimension-one incidence) -/

/-- A face of the cube at `c` iff `c` is one of the face's two adjacent cubes. -/
theorem mem_cubeFaces_iff_mem_adjacentCubes (c : C3) (f : Face3) :
    f ∈ cubeFaces c ↔ c ∈ adjacentCubes f := by
  rcases f with ⟨b, i⟩
  constructor
  · intro hf
    fin_cases i <;>
      simp [cubeFaces, adjacentCubes, addC3, subC3, axisVec, Prod.ext_iff] at hf ⊢ <;> omega
  · intro hc
    simp only [adjacentCubes, Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | hc
    · fin_cases i <;> simp [cubeFaces]
    · fin_cases i <;>
        simp [cubeFaces, addC3, subC3, axisVec, Prod.ext_iff] at hc ⊢ <;> omega

theorem cubeFaces_card (c : C3) : (cubeFaces c).card = 6 := by
  simp [cubeFaces, addC3, axisVec, Prod.ext_iff]

theorem adjacentCubes_card (f : Face3) : (adjacentCubes f).card = 2 := by
  rw [adjacentCubes]
  apply Finset.card_pair_eq_two_iff.mpr
  rcases f with ⟨b, i⟩
  fin_cases i
  · simp [subC3, axisVec]
    intro h
    have h' := congrArg Prod.fst h
    simp at h'
    omega
  · simp [subC3, axisVec]
    intro h
    have h' := congrArg (fun p : C3 => p.2.1) h
    simp at h'
    omega
  · simp [subC3, axisVec]
    intro h
    have h' := congrArg (fun p : C3 => p.2.2) h
    simp at h'
    omega

theorem adjCubes_inter_card_le_two (f : Face3) (K : Finset C3) :
    ((adjacentCubes f) ∩ K).card ≤ 2 := by
  exact le_trans (Finset.card_le_card (Finset.inter_subset_left)) (by rw [adjacentCubes_card])

theorem one_le_adjCubes_inter_card {f : Face3} {c : C3} (hc : c ∈ K)
    (hf : f ∈ cubeFaces c) : 1 ≤ ((adjacentCubes f) ∩ K).card := by
  apply Finset.card_pos.mpr
  exact ⟨c, Finset.mem_inter.mpr ⟨(mem_cubeFaces_iff_mem_adjacentCubes c f).mp hf, hc⟩⟩

/-- **Face double counting.** Each of the six faces of each cube is either a
    boundary face (adjacent to one cube) or a shared face (adjacent to two), so

        `|∂F| + 6·|K| = 2·|faces(K)|`.

    This is the codimension-one instance of the incidence count that any
    duality proof must consume; unlike the χ decomposition it is not a
    definition unfolding. -/
theorem boundaryFaces_card_add_six (K : Finset C3) :
    ((boundaryFaces K).card : Int) + 6 * (K.card : Int) =
      2 * ((cellsOf K).2.2.card : Int) := by
  classical
  let F : Finset Face3 := (cellsOf K).2.2
  let Q : Finset (C3 × Face3) := K.product F
  let n : Face3 → Nat := fun f => ((adjacentCubes f) ∩ K).card
  have hsub (c : C3) (hc : c ∈ K) : cubeFaces c ⊆ F := by
    intro f hf
    dsimp [F, cellsOf]
    exact Finset.mem_biUnion.mpr ⟨c, hc, hf⟩
  have hswap : (∑ p ∈ Q, (if p.2 ∈ cubeFaces p.1 then (1 : Nat) else 0)) =
      ∑ c ∈ K, (cubeFaces c).card := by
    dsimp [Q]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro c hc
    calc
      (∑ f ∈ F, if f ∈ cubeFaces c then (1 : Nat) else 0) =
          (F.filter fun f => f ∈ cubeFaces c).card := by
        rw [← Finset.sum_filter]
        simp
      _ = (cubeFaces c).card := by
        congr 1
        ext f
        constructor
        · intro hf
          exact (Finset.mem_filter.mp hf).2
        · intro hf
          exact Finset.mem_filter.mpr ⟨hsub c hc hf, hf⟩
  have hswap2 : (∑ p ∈ Q, (if p.2 ∈ cubeFaces p.1 then (1 : Nat) else 0)) =
      ∑ f ∈ F, ((adjacentCubes f) ∩ K).card := by
    dsimp [Q]
    rw [Finset.sum_product]
    calc
      (∑ c ∈ K, ∑ f ∈ F, if f ∈ cubeFaces c then (1 : Nat) else 0) =
          ∑ f ∈ F, ∑ c ∈ K, if f ∈ cubeFaces c then (1 : Nat) else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ f ∈ F, ((adjacentCubes f) ∩ K).card := by
        apply Finset.sum_congr rfl
        intro f hf
        calc
          (∑ c ∈ K, if f ∈ cubeFaces c then (1 : Nat) else 0) =
              (K.filter fun c => f ∈ cubeFaces c).card := by
            rw [← Finset.sum_filter]
            simp
          _ = ((adjacentCubes f) ∩ K).card := by
            congr 1
            ext c
            simp [mem_cubeFaces_iff_mem_adjacentCubes, and_comm]
  have hsumc : (∑ c ∈ K, (cubeFaces c).card) = 6 * K.card := by
    simp [cubeFaces_card]
    omega
  have hn_ge (f : Face3) (hf : f ∈ F) : 1 ≤ n f := by
    dsimp [F] at hf
    simp only [cellsOf, Finset.mem_biUnion] at hf
    rcases hf with ⟨c, hcK, hfc⟩
    exact one_le_adjCubes_inter_card hcK hfc
  have hn_one_or_two (f : Face3) (hf : f ∈ F) : n f = 1 ∨ n f = 2 := by
    have hlo := hn_ge f hf
    have hhi := adjCubes_inter_card_le_two f K
    dsimp [n] at hlo hhi ⊢
    omega
  have hfilter : F.filter (fun f => n f = 1) = boundaryFaces K := by
    dsimp [F, boundaryFaces, n, cellsOf]
  have hsum_split : (∑ f ∈ F, (n f : Int)) =
      ((boundaryFaces K).card : Int) + 2 * ((F.filter fun f => ¬ n f = 1).card : Int) := by
    have hs := Finset.sum_filter_add_sum_filter_not F (fun f => n f = 1) (fun f => (n f : Int))
    have hfirst : (∑ f ∈ F with n f = 1, (n f : Int)) = (boundaryFaces K).card := by
      calc
        (∑ f ∈ F with n f = 1, (n f : Int)) = ∑ f ∈ F with n f = 1, (1 : Int) := by
          apply Finset.sum_congr rfl
          intro f hf
          simp [(Finset.mem_filter.mp hf).2]
        _ = ((F.filter fun f => n f = 1).card : Int) := by
          simp
        _ = (boundaryFaces K).card := by
          rw [hfilter]
    have hsecond : (∑ f ∈ F with ¬ n f = 1, (n f : Int)) =
        2 * ((F.filter fun f => ¬ n f = 1).card : Int) := by
      calc
        (∑ f ∈ F with ¬ n f = 1, (n f : Int)) = ∑ f ∈ F with ¬ n f = 1, (2 : Int) := by
          apply Finset.sum_congr rfl
          intro f hf
          have hfF : f ∈ F := (Finset.mem_filter.mp hf).1
          have hnnot : ¬ n f = 1 := (Finset.mem_filter.mp hf).2
          rcases hn_one_or_two f hfF with h | h
          · exact False.elim (hnnot h)
          · simp [h]
        _ = 2 * ((F.filter fun f => ¬ n f = 1).card : Int) := by
          simp [mul_comm]
    rw [hfirst, hsecond] at hs
    linarith
  have htot' : 6 * (K.card : Int) =
      (boundaryFaces K).card + 2 * ((F.filter fun f => ¬ n f = 1).card : Int) := by
    have h' : (∑ f ∈ F, ((adjacentCubes f) ∩ K).card) = 6 * K.card :=
      hswap2.symm.trans (hswap.trans hsumc)
    have h1 : (6 * K.card : Int) = ∑ f ∈ F, (n f : Int) := by
      dsimp [n]
      exact_mod_cast h'.symm
    linarith [h1, hsum_split]
  have hfcard : (F.card : Int) =
      (boundaryFaces K).card + ((F.filter fun f => ¬ n f = 1).card : Int) := by
    have hc := Finset.card_filter_add_card_filter_not (s := F) (p := fun f => n f = 1)
    rw [hfilter] at hc
    exact_mod_cast hc.symm
  dsimp [F] at hfcard ⊢
  linarith

/-! ### The open cells of a solid, and the χ decomposition -/

/-- Vertices of the solid that are not vertices of its boundary. -/
def interiorVertices (K : Finset C3) : Finset C3 :=
  (cellsOf K).1 \ (boundaryCells K).1

/-- Edges of the solid that are not edges of its boundary. -/
def interiorEdges (K : Finset C3) : Finset Edge3 :=
  (cellsOf K).2.1 \ (boundaryCells K).2.1

/-- Faces of the solid that are not faces of its boundary (the shared faces). -/
def interiorFaces (K : Finset C3) : Finset Face3 :=
  (cellsOf K).2.2 \ (boundaryCells K).2.2

/-- The Euler contribution of the cells of `K` off its boundary. All cubes are
    top-dimensional, hence always off the 2-dimensional boundary. -/
def chiInterior (K : Finset C3) : Int :=
  ((interiorVertices K).card : Int) - ((interiorEdges K).card : Int) +
    ((interiorFaces K).card : Int) - (K.card : Int)

theorem card_cellsOf_vertices (K : Finset C3) :
    (((cellsOf K).1).card : Int) =
      ((boundaryCells K).1).card + (interiorVertices K).card := by
  have h := Finset.card_sdiff_add_card_eq_card (boundaryVertices_subset_cellsOf K)
  dsimp [interiorVertices]
  omega

theorem card_cellsOf_edges (K : Finset C3) :
    (((cellsOf K).2.1).card : Int) =
      ((boundaryCells K).2.1).card + (interiorEdges K).card := by
  have h := Finset.card_sdiff_add_card_eq_card (boundaryEdges_subset_cellsOf K)
  dsimp [interiorEdges]
  omega

theorem card_cellsOf_faces (K : Finset C3) :
    (((cellsOf K).2.2).card : Int) =
      ((boundaryCells K).2.2).card + (interiorFaces K).card := by
  have h := Finset.card_sdiff_add_card_eq_card (boundaryFaces_subset_cellsOf K)
  dsimp [interiorFaces]
  change ((cellsOf K).2.2.card : Int) =
    (boundaryFaces K).card + ((cellsOf K).2.2 \ boundaryFaces K).card
  omega

/-- The double-counting identity of `boundaryFaces_card_add_six`, rearranged:
    `6·|K| = |∂faces| + 2·|shared faces|`. -/
theorem six_mul_card_eq_boundaryFaces_add_two_mul_interiorFaces (K : Finset C3) :
    6 * K.card = (boundaryFaces K).card + 2 * (interiorFaces K).card := by
  have h := boundaryFaces_card_add_six K
  have hf := card_cellsOf_faces K
  change ((cellsOf K).2.2.card : Int) =
    (boundaryFaces K).card + (interiorFaces K).card at hf
  have hi : 6 * (K.card : Int) =
      (boundaryFaces K).card + 2 * (interiorFaces K).card := by
    linarith
  exact_mod_cast hi

/-- **Inclusion–exclusion boundary decomposition.** For every finite cube set,
    `χ(S) = χ(∂S) + χ(S \ ∂S)` at the level of cell counts. -/
theorem chiOf_eq_chiBoundary_add_chiInterior (K : Finset C3) :
    chiOf K = chiBoundary K + chiInterior K := by
  have hv := card_cellsOf_vertices K
  have he := card_cellsOf_edges K
  have hf := card_cellsOf_faces K
  dsimp [chiOf, chiBoundary, chiInterior]
  rw [hv, he, hf]
  ring

/-! ### The isolated duality step and everything downstream -/

/-- The missing input: the open cells of `S` contribute the negative of the
    solid's χ. Equivalent (by `interiorDuality_iff_chiBoundary`) to the
    Poincaré–Lefschetz relation `χ(∂S) = 2·χ(S)`. -/
def HasInteriorDuality (K : Finset C3) : Prop :=
  chiInterior K = -chiOf K

/-- **Reduction.** `χ(∂S) = 2·χ(S)` holds if and only if the interior-duality
    identity holds. The forward implication shows the duality hypothesis is
    necessary, not just sufficient. -/
theorem interiorDuality_iff_chiBoundary (K : Finset C3) :
    chiInterior K = -chiOf K ↔ chiBoundary K = 2 * chiOf K := by
  have hdecomp := chiOf_eq_chiBoundary_add_chiInterior K
  constructor <;> intro h <;> linarith

/-- Conditional general Poincaré–Lefschetz theorem. -/
theorem chiBoundary_eq_two_chiOf_of_hasInteriorDuality (K : Finset C3)
    (h : HasInteriorDuality K) : chiBoundary K = 2 * chiOf K :=
  (interiorDuality_iff_chiBoundary K).mp h

/-- The dual reduction: from the χ relation to interior duality. -/
theorem hasInteriorDuality_of_chiBoundary_eq_two_chiOf (K : Finset C3)
    (h : chiBoundary K = 2 * chiOf K) : HasInteriorDuality K :=
  (interiorDuality_iff_chiBoundary K).mpr h

end Vdb
