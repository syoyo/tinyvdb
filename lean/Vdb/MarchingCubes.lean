/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  The marching-cubes sign rule. Cubes are classified by the signs of their
  eight corner values; edges of opposite sign are crossed by the surface, and
  ambiguous (checkerboard) faces are resolved by a *consistent* rule: connect
  the negative diagonal exactly when the face's mean value is negative.

  The mean depends only on the unordered four corner values, so both cubes
  sharing a face decide the same way (the rule is invariant under the dihedral
  symmetries of the face, including the reversal the neighbouring cube walks).
  This is the "consistent face rule" chosen over the asymptotic decider in
  `plan-lean.md` (F10).

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

set_option linter.unusedSimpArgs false

namespace Vdb

/-- A corner value is inside when it is negative (the level-set sign
    convention used by the volume operators). -/
def isInside (q : ℚ) : Bool := decide (q < 0)

@[simp] theorem isInside_iff {q : ℚ} : isInside q = true ↔ q < 0 := by
  simp [isInside]

@[simp] theorem isInside_false_iff {q : ℚ} : isInside q = false ↔ ¬ q < 0 := by
  simp [isInside]

/-- A cube face's four corner values in cyclic order. The diagonals are
    `(a, c)` and `(b, d)`. -/
structure Face where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

/-- The consistent face rule: connect the negative diagonal exactly when the
    face's mean value is negative. The mean depends only on the unordered set
    of the four values, so both cubes sharing a face decide the same way. -/
def Face.negConnected (f : Face) : Bool :=
  decide (f.a + f.b + f.c + f.d < 0)

/-- An ambiguous (checkerboard) face: opposite corners agree and the two
    diagonals carry opposite signs. -/
def Face.Ambiguous (f : Face) : Prop :=
  isInside f.a = isInside f.c ∧ isInside f.b = isInside f.d ∧
    isInside f.a ≠ isInside f.b

/-- The decision only depends on the four values (it is a function). -/
theorem Face.negConnected_eq_sum (f : Face) :
    f.negConnected = decide (f.a + f.b + f.c + f.d < 0) := rfl

/-- Cyclic rotation of the face's corner order. -/
def Face.rot (f : Face) : Face := ⟨f.b, f.c, f.d, f.a⟩

/-- Reversal of the corner order (the order the neighbouring cube sees when
    traversing the shared face the other way). -/
def Face.rev (f : Face) : Face := ⟨f.d, f.c, f.b, f.a⟩

/-- Reflection fixing the `(a, c)` diagonal. -/
def Face.refl (f : Face) : Face := ⟨f.a, f.d, f.c, f.b⟩

/-- The rule is invariant under a cyclic rotation of the face. -/
theorem Face.negConnected_rot (f : Face) :
    f.rot.negConnected = f.negConnected := by
  unfold Face.negConnected Face.rot
  have h : f.b + f.c + f.d + f.a = f.a + f.b + f.c + f.d := by ring
  rw [h]

/-- The rule is invariant under reversal (the neighbour's orientation). -/
theorem Face.negConnected_rev (f : Face) :
    f.rev.negConnected = f.negConnected := by
  unfold Face.negConnected Face.rev
  have h : f.d + f.c + f.b + f.a = f.a + f.b + f.c + f.d := by ring
  rw [h]

/-- The rule is invariant under the diagonal reflection. -/
theorem Face.negConnected_refl (f : Face) :
    f.refl.negConnected = f.negConnected := by
  unfold Face.negConnected Face.refl
  have h : f.a + f.d + f.c + f.b = f.a + f.b + f.c + f.d := by ring
  rw [h]

/-- **Consistency**: any two cubes sharing a face agree on which diagonal is
    connected, whatever corner order each of them walks the face in. -/
theorem Face.negConnected_all_symmetries (f : Face) :
    f.negConnected = f.rot.negConnected ∧
      f.negConnected = f.rev.negConnected ∧
      f.negConnected = f.refl.negConnected ∧
      f.negConnected = f.rot.rev.negConnected ∧
      f.negConnected = f.rot.refl.negConnected ∧
      f.negConnected = f.rev.refl.negConnected := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Face.negConnected_rot]
  · rw [Face.negConnected_rev]
  · rw [Face.negConnected_refl]
  · rw [Face.negConnected_rev, Face.negConnected_rot]
  · rw [Face.negConnected_refl, Face.negConnected_rot]
  · rw [Face.negConnected_refl, Face.negConnected_rev]

/-- Flipping the field (inside/outside swap) flips the rule, provided the
    face mean is not zero. -/
def Face.neg (f : Face) : Face := ⟨-f.a, -f.b, -f.c, -f.d⟩

theorem Face.negConnected_neg (f : Face)
    (hs : f.a + f.b + f.c + f.d ≠ 0) :
    f.neg.negConnected = !f.negConnected := by
  unfold Face.negConnected Face.neg
  have hs' : -f.a + -f.b + -f.c + -f.d = -(f.a + f.b + f.c + f.d) := by ring
  rw [hs']
  by_cases h : f.a + f.b + f.c + f.d < 0
  · have h2 : ¬ -(f.a + f.b + f.c + f.d) < 0 := by
      rw [neg_lt_zero]
      exact not_lt.mpr (le_of_lt h)
    rw [decide_eq_true_eq.mpr h, decide_eq_false_iff_not.mpr h2]
    rfl
  · have h2 : -(f.a + f.b + f.c + f.d) < 0 := by
      rw [neg_lt_zero]
      exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hs)
    rw [decide_eq_false_iff_not.mpr h, decide_eq_true_eq.mpr h2]
    rfl

/-- An all-inside face is not ambiguous. -/
theorem Face.not_ambiguous_all_neg (f : Face)
    (ha : f.a < 0) (hb : f.b < 0) (_hc : f.c < 0) (_hd : f.d < 0) :
    ¬ f.Ambiguous := by
  rintro ⟨hac, hbd, hab⟩
  have h1 : isInside f.a = true := isInside_iff.mpr ha
  have h2 : isInside f.b = true := isInside_iff.mpr hb
  exact hab (by rw [h1, h2])

/-- An all-outside face is not ambiguous. -/
theorem Face.not_ambiguous_all_pos (f : Face)
    (ha : 0 < f.a) (hb : 0 < f.b) (_hc : 0 < f.c) (_hd : 0 < f.d) :
    ¬ f.Ambiguous := by
  rintro ⟨hac, hbd, hab⟩
  have h1 : isInside f.a = false := isInside_false_iff.mpr (not_lt.mpr (le_of_lt ha))
  have h2 : isInside f.b = false := isInside_false_iff.mpr (not_lt.mpr (le_of_lt hb))
  exact hab (by rw [h1, h2])

/-- Whether the surface crosses an edge (the two endpoint signs differ). -/
def edgeCrosses (u v : ℚ) : Bool := isInside u != isInside v

/-- The edge test is symmetric, so neighbouring cubes agree when they walk a
    shared edge in opposite directions. -/
theorem edgeCrosses_comm (u v : ℚ) : edgeCrosses u v = edgeCrosses v u := by
  unfold edgeCrosses
  cases isInside u <;> cases isInside v <;> rfl

theorem Face.ambiguous_diagonals (f : Face) (h : f.Ambiguous)
    (ha : f.a ≠ 0) (hb : f.b ≠ 0) (hc : f.c ≠ 0) (hd : f.d ≠ 0) :
    (f.a < 0 ∧ f.c < 0 ∧ 0 < f.b ∧ 0 < f.d) ∨
      (0 < f.a ∧ 0 < f.c ∧ f.b < 0 ∧ f.d < 0) := by
  obtain ⟨hac, hbd, hab⟩ := h
  cases hin : isInside f.a
  · have ha' : 0 < f.a := by
      have : ¬ f.a < 0 := isInside_false_iff.mp hin
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm ha)
    have hc' : 0 < f.c := by
      have hc0 : isInside f.c = false := by rw [← hac]; exact hin
      have : ¬ f.c < 0 := isInside_false_iff.mp hc0
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hc)
    have hb' : f.b < 0 := by
      have hb1 : isInside f.b = true := by
        cases h2 : isInside f.b
        · exact absurd (by rw [hin, h2]) hab
        · rfl
      exact isInside_iff.mp hb1
    have hd' : f.d < 0 := by
      have hd1 : isInside f.d = true := by rw [← hbd]; exact isInside_iff.mpr hb'
      exact isInside_iff.mp hd1
    exact Or.inr ⟨ha', hc', hb', hd'⟩
  · have ha' : f.a < 0 := isInside_iff.mp hin
    have hc' : f.c < 0 := by
      have hc1 : isInside f.c = true := by rw [← hac]; exact hin
      exact isInside_iff.mp hc1
    have hb' : 0 < f.b := by
      have hb0 : isInside f.b = false := by
        cases h2 : isInside f.b
        · rfl
        · exact absurd (by rw [hin, h2]) hab
      have : ¬ f.b < 0 := isInside_false_iff.mp hb0
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hb)
    have hd' : 0 < f.d := by
      have hd0 : isInside f.d = false := by rw [← hbd]; exact isInside_false_iff.mpr (not_lt.mpr (le_of_lt hb'))
      have : ¬ f.d < 0 := isInside_false_iff.mp hd0
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hd)
    exact Or.inl ⟨ha', hc', hb', hd'⟩


/-! ### Edge crossings and cube classification -/

/-- Linear interpolation between two corner values. -/
def lerp (a b t : ℚ) : ℚ := a + t * (b - a)

/-- The parameter where a linear edge crosses zero, measured from `a`. -/
def edgeParam (a b : ℚ) : ℚ := a / (a - b)

theorem lerp_zero {a b : ℚ} (h : a ≠ b) : lerp a b (edgeParam a b) = 0 := by
  unfold lerp edgeParam
  field_simp
  ring

/-- The zero crossing is independent of which endpoint the edge is walked
    from: neighbouring cubes place the same vertex. -/
theorem edgeParam_symm {a b : ℚ} (h : a ≠ b) :
    edgeParam b a = 1 - edgeParam a b := by
  unfold edgeParam
  field_simp
  ring

theorem lerp_symm (a b t : ℚ) : lerp a b t = lerp b a (1 - t) := by
  unfold lerp
  ring

/-- On an edge whose endpoints straddle zero, the crossing parameter lies
    strictly between the endpoints. -/
theorem edgeParam_mem_Ioo {a b : ℚ} (ha : a < 0) (hb : 0 < b) :
    0 < edgeParam a b ∧ edgeParam a b < 1 := by
  unfold edgeParam
  have hd : a - b < 0 := by linarith
  constructor
  · rw [div_pos_iff]
    right
    exact ⟨ha, hd⟩
  · rw [div_lt_iff_of_neg hd]
    linarith

/-- A cube's eight corner values (bit 0 = x, bit 1 = y, bit 2 = z). -/
structure Cube where
  c : Fin 8 → ℚ

/-- The twelve cube edges, as unordered corner pairs. -/
def Cube.edges (_q : Cube) : List (Fin 8 × Fin 8) :=
  [(0, 1), (1, 3), (3, 2), (2, 0),
   (4, 5), (5, 7), (7, 6), (6, 4),
   (0, 4), (1, 5), (2, 6), (3, 7)]

/-- Does the surface cross this edge? -/
def Cube.crosses (q : Cube) (e : Fin 8 × Fin 8) : Bool :=
  edgeCrosses (q.c e.1) (q.c e.2)

/-- The edges of the cube crossed by the surface: the marching-cubes input. -/
def Cube.crossedEdges (q : Cube) : List (Fin 8 × Fin 8) :=
  q.edges.filter (q.crosses ·)

theorem Cube.length_crossedEdges_le (q : Cube) : q.crossedEdges.length ≤ 12 := by
  unfold Cube.crossedEdges
  exact le_trans (List.length_filter_le _ _) (by unfold Cube.edges; simp)

/-- A cube with all corners inside has no crossed edges (nothing to mesh). -/
theorem Cube.crossedEdges_nil_of_all_neg (q : Cube) (h : ∀ k, q.c k < 0) :
    q.crossedEdges = [] := by
  unfold Cube.crossedEdges
  apply List.filter_eq_nil_iff.mpr
  rintro ⟨i, j⟩ _
  unfold Cube.crosses edgeCrosses
  rw [isInside_iff.mpr (h i), isInside_iff.mpr (h j)]
  simp

/-- A cube with all corners outside has no crossed edges either. -/
theorem Cube.crossedEdges_nil_of_all_pos (q : Cube) (h : ∀ k, 0 < q.c k) :
    q.crossedEdges = [] := by
  unfold Cube.crossedEdges
  apply List.filter_eq_nil_iff.mpr
  rintro ⟨i, j⟩ _
  unfold Cube.crosses edgeCrosses
  rw [isInside_false_iff.mpr (not_lt.mpr (le_of_lt (h i))),
    isInside_false_iff.mpr (not_lt.mpr (le_of_lt (h j)))]
  simp

/-- Every crossing reported by the cube classification is a genuine sign
    change on that edge. -/
theorem Cube.mem_crossedEdges_iff {q : Cube} {e : Fin 8 × Fin 8} :
    e ∈ q.crossedEdges ↔ e ∈ q.edges ∧ q.crosses e = true := by
  unfold Cube.crossedEdges
  simp [List.mem_filter]


/-! ### Face boundary crossings and the dual face quad -/

/-- A face's four boundary edges, in cyclic order. -/
def Face.edges (f : Face) : List (ℚ × ℚ) :=
  [(f.a, f.b), (f.b, f.c), (f.c, f.d), (f.d, f.a)]

/-- An edge as an unordered pair of endpoint values. -/
def uedge (u v : ℚ) : Finset ℚ := {u, v}

/-- The boundary edges as a set of unordered pairs. -/
def Face.edgeSetU (f : Face) : Finset (Finset ℚ) :=
  {uedge f.a f.b, uedge f.b f.c, uedge f.c f.d, uedge f.d f.a}

/-- The boundary edges crossed by the surface. -/
def Face.crossedEdges (f : Face) : List (ℚ × ℚ) :=
  f.edges.filter (fun e => edgeCrosses e.1 e.2)

theorem uedge_comm (u v : ℚ) : uedge u v = uedge v u := by
  unfold uedge
  exact Finset.pair_comm u v

/-- Reversing the face keeps the same four boundary edges (as a set). -/
theorem Face.mem_edgeSetU_rev {f : Face} {e : Finset ℚ} :
    e ∈ f.rev.edgeSetU ↔ e ∈ f.edgeSetU := by
  obtain ⟨a, b, c, d⟩ := f
  simp only [Face.edgeSetU, Face.rev, Finset.mem_insert, Finset.mem_singleton]
  constructor <;> rintro (h | h | h | h) <;> subst h <;> simp [uedge_comm]

theorem Face.edgeSetU_rev (f : Face) : f.rev.edgeSetU = f.edgeSetU :=
  Finset.ext (fun _e => Face.mem_edgeSetU_rev)

/-- An ambiguous face has all four boundary edges crossed. -/
theorem Face.ambiguous_iff_crossed (f : Face) :
    f.Ambiguous ↔ ∀ e ∈ f.edges, edgeCrosses e.1 e.2 = true := by
  obtain ⟨a, b, c, d⟩ := f
  unfold Face.Ambiguous Face.edges
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, edgeCrosses]
  cases ha : isInside a <;> cases hb : isInside b <;>
    cases hc : isInside c <;> cases hd : isInside d <;>
    simp [ha, hb, hc, hd]

/-- The number of crossed boundary edges of a face is even (a cyclic sign
    sequence changes sign an even number of times). -/
theorem Face.length_crossedEdges_even (f : Face) : Even f.crossedEdges.length := by
  obtain ⟨a, b, c, d⟩ := f
  unfold Face.crossedEdges Face.edges
  cases ha : isInside a <;> cases hb : isInside b <;>
    cases hc : isInside c <;> cases hd : isInside d <;>
    simp [edgeCrosses, ha, hb, hc, hd] <;> decide

/-- An ambiguous face has exactly four crossed boundary edges. -/
theorem Face.length_crossedEdges_of_ambiguous {f : Face} (h : f.Ambiguous) :
    f.crossedEdges.length = 4 := by
  have hall := (Face.ambiguous_iff_crossed f).mp h
  unfold Face.crossedEdges
  rw [List.filter_eq_self.mpr ?_]
  · unfold Face.edges
    simp
  · intro e he
    exact hall e he

/-- A non-ambiguous face has zero or two crossed boundary edges. -/
theorem Face.length_crossedEdges_of_not_ambiguous {f : Face} (h : ¬ f.Ambiguous) :
    f.crossedEdges.length = 0 ∨ f.crossedEdges.length = 2 := by
  have heven := Face.length_crossedEdges_even f
  have hle : f.crossedEdges.length ≤ 4 := by
    unfold Face.crossedEdges
    exact le_trans (List.length_filter_le _ _) (by unfold Face.edges; simp)
  have hnotall : ¬ ∀ x ∈ f.edges, edgeCrosses x.1 x.2 = true := by
    intro hall
    exact h ((Face.ambiguous_iff_crossed f).mpr hall)
  have hne : f.crossedEdges.length ≠ 4 := by
    intro h4
    have hs : (f.edges.filter (fun e => edgeCrosses e.1 e.2)).Sublist f.edges :=
      List.filter_sublist
    have hlen : (f.edges.filter (fun e => edgeCrosses e.1 e.2)).length = f.edges.length := by
      unfold Face.crossedEdges at h4
      unfold Face.edges at h4 ⊢
      simpa using h4
    exact hnotall (List.filter_eq_self.mp (hs.eq_of_length hlen))
  have hlt : f.crossedEdges.length < 4 := lt_of_le_of_ne hle hne
  obtain ⟨k, hk⟩ := heven
  omega

/-- A face's dual quad: the four boundary edges (as unordered pairs) plus the
    rule's diagonal choice. Two cubes sharing a face must build the same
    quad, i.e. the same edges and the same diagonal. -/
structure FaceQuad where
  edges : Finset (Finset ℚ)
  negativeDiagonalJoined : Bool

def Face.quad (f : Face) : FaceQuad :=
  ⟨f.edgeSetU, f.negConnected⟩

theorem Face.quad_edges_rev (f : Face) : f.rev.quad.edges = f.quad.edges :=
  Face.edgeSetU_rev f

theorem Face.quad_rule_rev (f : Face) :
    f.rev.quad.negativeDiagonalJoined = f.quad.negativeDiagonalJoined :=
  Face.negConnected_rev f

/-- **Face quad consistency**: the face quad is the same when the face is
    seen from the neighbouring cube (reversed corner order). -/
theorem Face.quad_rev (f : Face) : f.rev.quad = f.quad := by
  simp only [Face.quad]
  rw [Face.edgeSetU_rev, Face.negConnected_rev]

end Vdb
