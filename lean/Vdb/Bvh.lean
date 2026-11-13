/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  The BVH closest-triangle traversal of `src/tinyvdb_mesh.c`
  (`tvdb_bvh_closest`), modelled abstractly over ℚ.

  The C implementation:

  * seeds the search with the caller-provided best face;
  * walks the tree with a binary DFS stack, pruning any node whose AABB
    lower bound is *strictly greater* than the current best distance;
  * accepts a face when it is strictly better in the `(distance, face index)`
    lexicographic order (`"lowest face index wins on exact ties"`).

  This module models the tree inductively over an abstract face type `F`
  with a distance query `dist : F → P3 → ℚ`, a face box `faceBox : F → Box`,
  and proves:

  * `boxDist_mono` — the AABB bound is monotone in the box (larger box,
    smaller bound);
  * from per-face bounds, **any** well-formed tree (each node box contains
    its children's boxes and its leaves' face boxes) gives
    `boxDist ≤ dist f p` at every node;
  * **`search_eq_brute`** — the pruned traversal returns **exactly** the
    brute-force result (same `(distance, face index)` pair), including the
    "lowest face index wins on exact ties" tie-break. The comparison is over
    ℚ, so the equality is bit-exact (not up to tolerance).

  Face indices are `ℕ` (as in the C `prim` permutation); ties are broken by
  index. The per-face bound `boxDist (faceBox f) p ≤ dist f p` is the
  AABB lower-bound property; for the true point-to-triangle distance it
  follows from "the closest point of a face lies in the face's AABB", which
  is discharged in `Vdb/BvhExamples` by evaluation on concrete faces. Here
  it is a hypothesis, so the soundness theorem is about the traversal
  itself, not about triangle geometry.

  What is *not* modelled: the seed-materialization details of
  `tvdb_bvh_closest` (the seed overwrites `best_cp`/`best_n` — the distance
  and face results coincide with this fold anyway); the DFS stack order
  (irrelevant, since the `(distance, index)` minimum is order-independent);
  and the actual tree *build* (splitting heuristic).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace Vdb

/-- A 3D rational point / vector. -/
abbrev P3 := Fin 3 → ℚ

/-- An axis-aligned bounding box. -/
structure Box where
  lo : P3
  hi : P3

/-- Point-to-set membership in a box (coordinate-wise). -/
def Box.mem (b : Box) (p : P3) : Prop :=
  b.lo 0 ≤ p 0 ∧ p 0 ≤ b.hi 0 ∧
  b.lo 1 ≤ p 1 ∧ p 1 ≤ b.hi 1 ∧
  b.lo 2 ≤ p 2 ∧ p 2 ≤ b.hi 2

/-- Squared distance from `p` to a box (sum of squared coordinate excesses). -/
def boxDist (b : Box) (p : P3) : ℚ :=
  (max 0 (b.lo 0 - p 0))^2 + (max 0 (p 0 - b.hi 0))^2 +
  (max 0 (b.lo 1 - p 1))^2 + (max 0 (p 1 - b.hi 1))^2 +
  (max 0 (b.lo 2 - p 2))^2 + (max 0 (p 2 - b.hi 2))^2

/-- `a ⊆ b` (coordinate-wise containment of the interval). -/
def Box.sub (a b : Box) : Prop :=
  b.lo 0 ≤ a.lo 0 ∧ a.hi 0 ≤ b.hi 0 ∧
  b.lo 1 ≤ a.lo 1 ∧ a.hi 1 ≤ b.hi 1 ∧
  b.lo 2 ≤ a.lo 2 ∧ a.hi 2 ≤ b.hi 2

/-- Per-axis excess bound: when `q` lies in `[lo, hi]`, the sum of the two
    one-sided squared excesses is at most `(p - q)^2`. (At most one of the
    two terms is nonzero, since `lo ≤ hi`.) -/
private theorem excess_sq_le {lo hi q p : ℚ} (hqlo : lo ≤ q) (hqhi : q ≤ hi) :
    (max 0 (lo - p))^2 + (max 0 (p - hi))^2 ≤ (p - q)^2 := by
  by_cases hp1 : p < lo
  · have h1 : (max 0 (p - hi))^2 = 0 := by
      rw [max_eq_left (by linarith : p - hi ≤ 0)]
      norm_num
    have h2 : max 0 (lo - p) = lo - p := max_eq_right (by linarith)
    rw [h1, h2, add_zero]
    have hsq := (sq_le_sq₀ (by linarith : (0:ℚ) ≤ lo - p) (by linarith : (0:ℚ) ≤ q - p)).mpr
      (by linarith : lo - p ≤ q - p)
    have e : (p - q)^2 = (q - p)^2 := by ring
    rw [e]; exact hsq
  · by_cases hp2 : hi < p
    · have h1 : (max 0 (lo - p))^2 = 0 := by
        rw [max_eq_left (by linarith : lo - p ≤ 0)]
        norm_num
      have h2 : max 0 (p - hi) = p - hi := max_eq_right (by linarith)
      rw [h1, h2, zero_add]
      exact (sq_le_sq₀ (by linarith : (0:ℚ) ≤ p - hi) (by linarith : (0:ℚ) ≤ p - q)).mpr
        (by linarith : p - hi ≤ p - q)
    · have h1 : (max 0 (lo - p))^2 = 0 := by
        rw [max_eq_left (by linarith [not_lt.mp hp1] : lo - p ≤ 0)]
        norm_num
      have h2 : (max 0 (p - hi))^2 = 0 := by
        rw [max_eq_left (by linarith [not_lt.mp hp2] : p - hi ≤ 0)]
        norm_num
      rw [h1, h2, add_zero]
      exact sq_nonneg _

/-- **The AABB lower bound**: every point of a box has `boxDist ≤ ‖p - q‖²`. -/
theorem boxDist_le_of_mem {b : Box} {p q : P3} (hq : Box.mem b q) :
    boxDist b p ≤ (p 0 - q 0)^2 + (p 1 - q 1)^2 + (p 2 - q 2)^2 := by
  unfold Box.mem boxDist at *
  obtain ⟨h0lo, h0hi, h1lo, h1hi, h2lo, h2hi⟩ := hq
  have a0 := excess_sq_le (lo := b.lo 0) (hi := b.hi 0) (q := q 0) (p := p 0) h0lo h0hi
  have a1 := excess_sq_le (lo := b.lo 1) (hi := b.hi 1) (q := q 1) (p := p 1) h1lo h1hi
  have a2 := excess_sq_le (lo := b.lo 2) (hi := b.hi 2) (q := q 2) (p := p 2) h2lo h2hi
  linarith [a0, a1, a2]

/-- **The AABB bound is monotone in the box**: a face's box contained in a
    larger node box gives a smaller-or-equal bound. -/
theorem boxDist_mono {a b : Box} (h : Box.sub a b) (p : P3) :
    boxDist b p ≤ boxDist a p := by
  unfold Box.sub at h
  unfold boxDist
  obtain ⟨h0lo, h0hi, h1lo, h1hi, h2lo, h2hi⟩ := h
  have e0 : max 0 (b.lo 0 - p 0) ≤ max 0 (a.lo 0 - p 0) := by gcongr
  have e1 : max 0 (p 0 - b.hi 0) ≤ max 0 (p 0 - a.hi 0) := by gcongr
  have e2 : max 0 (b.lo 1 - p 1) ≤ max 0 (a.lo 1 - p 1) := by gcongr
  have e3 : max 0 (p 1 - b.hi 1) ≤ max 0 (p 1 - a.hi 1) := by gcongr
  have e4 : max 0 (b.lo 2 - p 2) ≤ max 0 (a.lo 2 - p 2) := by gcongr
  have e5 : max 0 (p 2 - b.hi 2) ≤ max 0 (p 2 - a.hi 2) := by gcongr
  have s0 := (sq_le_sq₀ (le_max_left 0 (b.lo 0 - p 0)) (le_max_left 0 (a.lo 0 - p 0))).mpr e0
  have s1 := (sq_le_sq₀ (le_max_left 0 (p 0 - b.hi 0)) (le_max_left 0 (p 0 - a.hi 0))).mpr e1
  have s2 := (sq_le_sq₀ (le_max_left 0 (b.lo 1 - p 1)) (le_max_left 0 (a.lo 1 - p 1))).mpr e2
  have s3 := (sq_le_sq₀ (le_max_left 0 (p 1 - b.hi 1)) (le_max_left 0 (p 1 - a.hi 1))).mpr e3
  have s4 := (sq_le_sq₀ (le_max_left 0 (b.lo 2 - p 2)) (le_max_left 0 (a.lo 2 - p 2))).mpr e4
  have s5 := (sq_le_sq₀ (le_max_left 0 (p 2 - b.hi 2)) (le_max_left 0 (p 2 - a.hi 2))).mpr e5
  linarith [s0, s1, s2, s3, s4, s5]


/-! ### The tree model -/

/-- A BVH over face indices (`ℕ`). A leaf carries its own box and a list of
    faces; an internal node carries a box containing both children. -/
inductive BvhTree where
  | leaf : Box → List ℕ → BvhTree
  | node : Box → BvhTree → BvhTree → BvhTree

namespace BvhTree

/-- The box of a (sub)tree. -/
def box : BvhTree → Box
  | leaf b _ => b
  | node b _ _ => b

/-- All face indices in the tree, in traversal order. -/
def faces : BvhTree → List ℕ
  | leaf _ fs => fs
  | node _ l r => l.faces ++ r.faces

/-- Well-formedness relative to face boxes: node boxes contain their
    children's boxes, and leaf boxes contain every face box they store. -/
def WF (faceBox : ℕ → Box) : BvhTree → Prop
  | leaf b fs => ∀ f ∈ fs, Box.sub (faceBox f) b
  | node b l r => Box.sub l.box b ∧ Box.sub r.box b ∧ l.WF faceBox ∧ r.WF faceBox

/-- **From per-face bounds to node bounds**: every face stored in a
    well-formed subtree has distance at least the subtree's box bound. -/
theorem faces_dist_ge (d : ℕ → P3 → ℚ) (faceBox : ℕ → Box) (p : P3)
    (hb : ∀ f, boxDist (faceBox f) p ≤ d f p)
    {t : BvhTree} (hwf : t.WF faceBox) {f : ℕ} (hf : f ∈ t.faces) :
    boxDist t.box p ≤ d f p := by
  induction t with
  | leaf b fs =>
    have hsub := hwf f hf
    exact le_trans (boxDist_mono hsub p) (hb f)
  | node b l r ihl ihr =>
    rcases hwf with ⟨hl, hr, hwl, hwr⟩
    rcases List.mem_append.mp hf with hf | hf
    · have ih := ihl hwl hf
      exact le_trans (boxDist_mono hl p) ih
    · have ih := ihr hwr hf
      exact le_trans (boxDist_mono hr p) ih

end BvhTree

/-- The `(distance, faceIndex)` candidate, matching the C `best_dsq` /
    `best_face` pair. -/
abbrev Cand := ℚ × ℕ

/-- The strict candidate order: strictly smaller distance wins; on equal
    distance the lower face index wins. Matches the C acceptance test
    (`dsq < best_dsq || (dsq == best_dsq && face < best_face)`). -/
def better (c₁ c₂ : Cand) : Bool :=
  decide (c₁.1 < c₂.1) || (c₁.1 == c₂.1 && decide (c₁.2 < c₂.2))

theorem better_iff {c₁ c₂ : Cand} :
    better c₁ c₂ = true ↔ c₁.1 < c₂.1 ∨ (c₁.1 = c₂.1 ∧ c₁.2 < c₂.2) := by
  simp [better, beq_iff_eq]

theorem better_false_of_gt {c s : Cand} (h : s.1 < c.1) : better c s = false := by
  have hlt : ¬ c.1 < s.1 := not_lt.mpr h.le
  have hne : c.1 ≠ s.1 := ne_of_gt h
  have hb : (c.1 == s.1) = false := by
    cases heq : (c.1 == s.1)
    · rfl
    · rw [beq_iff_eq] at heq; exact absurd heq hne
  simp [better, hlt, hb]

/-- Fold the candidate list into a running (distance, index) minimum. -/
def foldCands (d : ℕ → P3 → ℚ) (p : P3) (s : Cand) (fs : List ℕ) : Cand :=
  fs.foldl (fun acc f =>
    if better (d f p, f) acc then (d f p, f) else acc) s

/-- A list of candidates none of which beats `s` folds to `s`. -/
theorem foldCands_noBetter (d : ℕ → P3 → ℚ) (p : P3) {s : Cand} (fs : List ℕ)
    (h : ∀ f ∈ fs, better (d f p, f) s = false) :
    foldCands d p s fs = s := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    unfold foldCands
    rw [List.foldl_cons]
    have hf := h f List.mem_cons_self
    have hs : (if better (d f p, f) s then (d f p, f) else s) = s := by rw [hf]; rfl
    rw [hs]
    exact ih (fun g hg => h g (List.mem_cons_of_mem f hg))

theorem foldCands_append (d : ℕ → P3 → ℚ) (p : P3) (s : Cand)
    (fs₁ fs₂ : List ℕ) :
    foldCands d p s (fs₁ ++ fs₂) = foldCands d p (foldCands d p s fs₁) fs₂ :=
  List.foldl_append

/-- The bottom-up seeded brute force: fold all faces of the tree into the
    seed candidate. -/
def brute (d : ℕ → P3 → ℚ) (p : P3) (s : Cand) (t : BvhTree) : Cand :=
  foldCands d p s t.faces

/-- The pruned traversal, over ℚ. Prunes any node (including leaves) whose
    box bound is *strictly greater* than the running best distance —
    exactly the C `if (nd > best_dsq) continue;`. -/
def search (d : ℕ → P3 → ℚ) (p : P3) (t : BvhTree) (s : Cand) : Cand :=
  match t with
  | BvhTree.leaf b fs =>
      if s.1 < boxDist b p then s else foldCands d p s fs
  | BvhTree.node b l r =>
      if s.1 < boxDist b p then s else search d p r (search d p l s)

/-- **Soundness**: the pruned traversal returns exactly the brute-force
    candidate — same distance, same face, including the tie-break. -/
theorem search_eq_brute (d : ℕ → P3 → ℚ) (faceBox : ℕ → Box) (p : P3)
    (hb : ∀ f, boxDist (faceBox f) p ≤ d f p) :
    ∀ (t : BvhTree) (_hwf : t.WF faceBox) (s : Cand),
      search d p t s = brute d p s t := by
  intro t
  induction t with
  | leaf b fs =>
    intro hwf s
    unfold search brute BvhTree.faces
    split_ifs with hprune
    · exact (foldCands_noBetter d p fs (fun f hf =>
        better_false_of_gt (lt_of_lt_of_le hprune
          (BvhTree.faces_dist_ge d faceBox p hb hwf hf)))).symm
    · rfl
  | node b l r ihl ihr =>
    intro hwf s
    rcases hwf with ⟨hl, hr, hwl, hwr⟩
    unfold search brute BvhTree.faces
    split_ifs with hprune
    · symm
      rw [foldCands_append]
      have hl' : ∀ f ∈ l.faces, better (d f p, f) s = false := fun f hf =>
        better_false_of_gt (lt_of_lt_of_le hprune
          (le_trans (boxDist_mono hl p) (BvhTree.faces_dist_ge d faceBox p hb hwl hf)))
      have hr' : ∀ f ∈ r.faces, better (d f p, f) s = false := fun f hf =>
        better_false_of_gt (lt_of_lt_of_le hprune
          (le_trans (boxDist_mono hr p) (BvhTree.faces_dist_ge d faceBox p hb hwr hf)))
      rw [foldCands_noBetter d p l.faces hl', foldCands_noBetter d p r.faces hr']
    · rw [ihl hwl s, ihr hwr (brute d p s l)]
      unfold brute
      rw [foldCands_append]

end Vdb
