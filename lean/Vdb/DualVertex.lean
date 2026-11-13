/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  DMC (dual marching cubes) vertex placement over exact rational geometry.

  Each cube has eight corner positions (0/1 per axis) and one dual vertex,
  placed at the average of the crossing points of its crossed edges. Every
  crossing is a convex combination of its two edge endpoints at the linear
  zero (`edgeParam`), so the dual vertex is a convex combination of cube
  corners and lies inside the unit cube.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.MarchingCubes

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Vdb

/-- Rational points in the unit cube (corner positions and interpolated
    vertices are exact; no floating point is involved). -/
abbrev Q3 := Fin 3 → ℚ

/-- The corner position of corner `k` (bit 0 = x, bit 1 = y, bit 2 = z). -/
def cornerPos (k : Fin 8) : Q3
  | 0 => ((k.val % 2 : Nat) : ℚ)
  | 1 => (((k.val / 2) % 2 : Nat) : ℚ)
  | _ => (((k.val / 4) % 2 : Nat) : ℚ)

theorem cornerPos_zero_or_one (k : Fin 8) (i : Fin 3) :
    cornerPos k i = 0 ∨ cornerPos k i = 1 := by
  fin_cases k <;> fin_cases i <;> simp [cornerPos]

theorem cornerPos_mem (k : Fin 8) (i : Fin 3) :
    0 ≤ cornerPos k i ∧ cornerPos k i ≤ 1 := by
  rcases cornerPos_zero_or_one k i with h | h <;> rw [h] <;> norm_num

/-- Linear interpolation between two points. -/
def lerpQ (a b : Q3) (t : ℚ) : Q3 := (1 - t) • a + t • b

theorem lerpQ_apply (a b : Q3) (t : ℚ) (i : Fin 3) :
    lerpQ a b t i = (1 - t) * a i + t * b i := by
  simp [lerpQ]

/-- The crossing point of a cube edge, at the linear zero of the edge. -/
def crossing (v : Fin 8 → ℚ) (i j : Fin 8) : Q3 :=
  lerpQ (cornerPos i) (cornerPos j) (edgeParam (v i) (v j))

/-- The crossing is the convex combination of its endpoints at the edge
    parameter. -/
theorem crossing_eq (v : Fin 8 → ℚ) (i j : Fin 8) :
    crossing v i j =
      (1 - edgeParam (v i) (v j)) • cornerPos i + edgeParam (v i) (v j) • cornerPos j :=
  rfl

theorem crossing_apply (v : Fin 8 → ℚ) (i j : Fin 8) (k : Fin 3) :
    crossing v i j k =
      (1 - edgeParam (v i) (v j)) * cornerPos i k + edgeParam (v i) (v j) * cornerPos j k :=
  lerpQ_apply _ _ _ _

/-- A crossing on an edge with a parameter in `[0,1]` stays in the cube. -/
theorem crossing_mem {v : Fin 8 → ℚ} {i j : Fin 8}
    (h0 : 0 ≤ edgeParam (v i) (v j)) (h1 : edgeParam (v i) (v j) ≤ 1) (k : Fin 3) :
    0 ≤ crossing v i j k ∧ crossing v i j k ≤ 1 := by
  rw [crossing_apply]
  obtain ⟨hA0, hA1⟩ := cornerPos_mem i k
  obtain ⟨hB0, hB1⟩ := cornerPos_mem j k
  constructor <;> nlinarith

/-- The average of a nonempty list of cube points. -/
def avgQ (l : List Q3) : Q3 := fun i => (l.map (fun p => p i)).sum / (l.length : ℚ)

theorem sum_map_bounds {l : List Q3} (h : ∀ p ∈ l, ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Fin 3) :
    0 ≤ (l.map (fun p => p i)).sum ∧ (l.map (fun p => p i)).sum ≤ (l.length : ℚ) := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    have hp := h p (by simp) i
    have hps : ∀ q ∈ ps, ∀ i, 0 ≤ q i ∧ q i ≤ 1 := fun q hq i => h q (by simp [hq]) i
    have ih' := ih hps
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> linarith

theorem avgQ_mem {l : List Q3} (hne : l ≠ [])
    (h : ∀ p ∈ l, ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Fin 3) :
    0 ≤ avgQ l i ∧ avgQ l i ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := sum_map_bounds h i
  have hlen : (0 : ℚ) < l.length := by
    have hpos : 0 < l.length := by
      cases l with
      | nil => exact absurd rfl hne
      | cons p ps => simp
    exact_mod_cast hpos
  unfold avgQ
  constructor
  · exact div_nonneg hlo (le_of_lt hlen)
  · rw [div_le_one hlen]
    exact hhi

/-- The dual vertex of a cube: the average of the crossing points of the
    given (nonempty) edge list. -/
def dualVertex (v : Fin 8 → ℚ) (edges : List (Fin 8 × Fin 8)) : Q3 :=
  avgQ (edges.map (fun e => crossing v e.1 e.2))

/-- **Dual vertex placement**: if every listed edge has its crossing parameter
    in `[0,1]` (true for the crossed edges of a sign change), the dual vertex
    lies inside the unit cube. -/
theorem dualVertex_mem_cube {v : Fin 8 → ℚ} {edges : List (Fin 8 × Fin 8)}
    (hne : edges ≠ [])
    (h : ∀ e ∈ edges, 0 ≤ edgeParam (v e.1) (v e.2) ∧ edgeParam (v e.1) (v e.2) ≤ 1)
    (k : Fin 3) : 0 ≤ dualVertex v edges k ∧ dualVertex v edges k ≤ 1 := by
  apply avgQ_mem
  · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil edges hne
    exact List.ne_nil_of_mem (List.mem_map.mpr ⟨e, he, rfl⟩)
  · intro p hp
    obtain ⟨e, he, hpe⟩ := List.mem_map.mp hp
    subst hpe
    exact crossing_mem (h e he).1 (h e he).2

end Vdb

namespace Vdb

/-- The parameter bounds when the edge is walked from the positive to the
    negative endpoint. -/
theorem edgeParam_mem_Ioo' {a b : ℚ} (ha : 0 < a) (hb : b < 0) :
    0 < edgeParam a b ∧ edgeParam a b < 1 := by
  unfold edgeParam
  have hd : 0 < a - b := by linarith
  constructor
  · exact div_pos ha hd
  · rw [div_lt_one hd]
    linarith

/-- The crossed edges of the cube, computed from its corner values. -/
def Cube.dualEdges (q : Cube) : List (Fin 8 × Fin 8) :=
  q.edges.filter (fun e => edgeCrosses (q.c e.1) (q.c e.2))

theorem Cube.dualEdges_eq_crossedEdges (q : Cube) :
    q.dualEdges = q.crossedEdges := rfl

/-- The cube's dual vertex: the average of the crossings of its crossed
    edges. -/
def Cube.dualVertex (q : Cube) (_hne : q.dualEdges ≠ []) : Q3 :=
  Vdb.dualVertex q.c q.dualEdges

/-- **Dual vertex inside the cube**: when every crossed edge really changes
    sign, the dual vertex lies in the unit cube (i.e. in the convex hull of
    the cube's corner positions). -/
theorem Cube.dualVertex_mem_cube (q : Cube) (hne : q.dualEdges ≠ [])
    (hsgn : ∀ e ∈ q.dualEdges,
      (q.c e.1 < 0 ∧ 0 < q.c e.2) ∨ (q.c e.2 < 0 ∧ 0 < q.c e.1))
    (k : Fin 3) : 0 ≤ Vdb.Cube.dualVertex q hne k ∧ Vdb.Cube.dualVertex q hne k ≤ 1 := by
  refine Vdb.dualVertex_mem_cube (v := q.c) (edges := q.dualEdges) hne ?_ k
  intro e he
  rcases hsgn e he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have ht := edgeParam_mem_Ioo ha hb
    exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  · have ht := edgeParam_mem_Ioo' hb ha
    exact ⟨le_of_lt ht.1, le_of_lt ht.2⟩


/-! ### Existence of the dual vertex (mixed cubes) -/

def Cube.signs (q : Cube) : Fin 8 → Bool := fun k => isInside (q.c k)

theorem cube_signs_connected :
    ∀ (s : Fin 8 → Bool), (∀ e : Fin 8 × Fin 8, e ∈ cubeEdges → s e.1 = s e.2) →
      ∀ k, s k = s 0 := by
  decide

theorem Cube.dualEdges_ne_nil_of_mixed (q : Cube) {i j : Fin 8}
    (hij : isInside (q.c i) ≠ isInside (q.c j)) : q.dualEdges ≠ [] := by
  intro hnil
  have hall : ∀ e ∈ q.edges, q.crosses e = false := by
    unfold Cube.dualEdges at hnil
    intro e he
    have hc : q.crosses e ≠ true := List.filter_eq_nil_iff.mp hnil e he
    unfold Cube.crosses at hc ⊢
    cases hb : edgeCrosses (q.c e.1) (q.c e.2) <;> simp_all
  have hsign : ∀ e ∈ q.edges, isInside (q.c e.1) = isInside (q.c e.2) := by
    intro e he
    have hc := hall e he
    unfold Cube.crosses edgeCrosses at hc
    cases ha : isInside (q.c e.1) <;> cases hb : isInside (q.c e.2) <;> simp_all
  have hconn : ∀ k, q.signs k = q.signs 0 :=
    cube_signs_connected q.signs (fun e he => hsign e (by simpa [Cube.edges] using he))
  exact hij (by
    have hi := hconn i
    have hj := hconn j
    simp only [Cube.signs] at hi hj
    rw [hi, hj])



/-- A crossed edge with nonzero endpoints has one negative and one positive
    endpoint (in some order). -/
theorem edgeCrosses_signs {u v : ℚ} (h : edgeCrosses u v = true)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (u < 0 ∧ 0 < v) ∨ (v < 0 ∧ 0 < u) := by
  have key : ∀ {a b : ℚ}, a ≠ 0 → b ≠ 0 → isInside a ≠ isInside b →
      (a < 0 ∧ 0 < b) ∨ (b < 0 ∧ 0 < a) := by
    intro a b ha hb hne
    cases hi : isInside a
    · have hb' : isInside b = true := by
        cases hb2 : isInside b
        · exact absurd (by rw [hi, hb2]) hne
        · rfl
      have h1 : ¬ a < 0 := isInside_false_iff.mp hi
      have h2 : b < 0 := isInside_iff.mp hb'
      exact Or.inr ⟨h2, lt_of_le_of_ne (not_lt.mp h1) (Ne.symm ha)⟩
    · have ha' : a < 0 := isInside_iff.mp hi
      have hb' : isInside b = false := by
        cases hb2 : isInside b
        · rfl
        · exact absurd (by rw [hi, hb2]) hne
      have h2 : ¬ b < 0 := isInside_false_iff.mp hb'
      exact Or.inl ⟨ha', lt_of_le_of_ne (not_lt.mp h2) (Ne.symm hb)⟩
  unfold edgeCrosses at h
  by_cases he : isInside u = isInside v
  · rw [he] at h
    simp at h
  · exact key hu hv he

/-- **Every mixed cube has a dual vertex inside it**: a cube with both an
    inside and an outside corner has a crossed edge, and the crossings of its
    crossed (nonzero) edges give the in-cube average. -/
theorem Cube.dualVertex_mem_cube_of_mixed (q : Cube) {i j : Fin 8}
    (hij : isInside (q.c i) ≠ isInside (q.c j))
    (hnz : ∀ e ∈ q.dualEdges, q.c e.1 ≠ 0 ∧ q.c e.2 ≠ 0)
    (k : Fin 3) :
    0 ≤ Vdb.Cube.dualVertex q (q.dualEdges_ne_nil_of_mixed hij) k ∧
      Vdb.Cube.dualVertex q (q.dualEdges_ne_nil_of_mixed hij) k ≤ 1 := by
  refine q.dualVertex_mem_cube _ ?_ k
  intro e he
  have hc : edgeCrosses (q.c e.1) (q.c e.2) = true := by
    unfold Cube.dualEdges at he
    exact (List.mem_filter.mp he).2
  exact edgeCrosses_signs hc (hnz e he).1 (hnz e he).2

end Vdb
