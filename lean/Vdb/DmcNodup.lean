/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  Classification of the shell-pinned sign fields whose general-`n`
  cuberille / DMC mesh (`Vdb/PadGrid.lean`) repeats no directed dual edge —
  the hypothesis of `Vdb/QuadEulerPad.lean`'s `euler_general`.

  The key identity: the four lattice edges bounding a cell face (its *ring*,
  the last four of the six candidates) are used by exactly the crossed ring
  edges, each in exactly one direction, so the two directional use counts add
  up to the number of crossed ring edges; balance makes them equal. A face is
  therefore used `crossed / 2` times per direction, and used twice exactly
  when all four ring edges cross — the checkerboard (ambiguous) face.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.QuadEulerPad

set_option linter.unusedSimpArgs false

namespace Vdb

namespace PadGrid

/-- The four lattice edges bounding the cell face `f` (its perimeter ring). -/
def ring (f : Face) : List PadEdge :=
  let c := f.1
  match f.2 with
  | 0 => [((c.1 + 1, c.2.1, c.2.2), 1), ((c.1 + 1, c.2.1, c.2.2), 2),
          ((c.1 + 1, c.2.1, c.2.2 + 1), 1), ((c.1 + 1, c.2.1 + 1, c.2.2), 2)]
  | 1 => [((c.1, c.2.1 + 1, c.2.2), 0), ((c.1, c.2.1 + 1, c.2.2), 2),
          ((c.1, c.2.1 + 1, c.2.2 + 1), 0), ((c.1 + 1, c.2.1 + 1, c.2.2), 2)]
  | 2 => [((c.1, c.2.1, c.2.2 + 1), 0), ((c.1, c.2.1, c.2.2 + 1), 1),
          ((c.1, c.2.1 + 1, c.2.2 + 1), 0), ((c.1 + 1, c.2.1, c.2.2 + 1), 1)]
  | _ => []

/-- The number of ring edges of `f` that cross the sign field. -/
def ringCrossed (n : Nat) (s : Lat → Bool) (f : Face) : Nat :=
  ((ring f).filter (crossedB n s)).length

/-- A crossed edge of a pinned field has in-grid transverse coordinates, so
    the anchor gates of the contribution lemmas are open. -/
theorem crossedB_gate {n : Nat} {s : Lat → Bool}
    (hpin : ∀ p, isShell n p = true → s p = false) {p : Lat} {d : Nat}
    (hd : d < 3) (h : crossedB n s (p, d) = true) :
    (d = 0 → 1 ≤ p.2.1 ∧ 1 ≤ p.2.2) ∧ (d = 1 → 1 ≤ p.1 ∧ 1 ≤ p.2.2) ∧
      (d = 2 → 1 ≤ p.1 ∧ 1 ≤ p.2.1) := by
  have hm := crossed_of_crossedB n s h (List.mem_range.mpr hd)
  obtain ⟨_, hp, _, hne⟩ := crossed_spec n s hm
  have ht := pinned_transverse n s hpin hp hne
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · obtain ⟨a, _, c, _⟩ := ht.1 h0; exact ⟨a, c⟩
  · obtain ⟨a, _, c, _⟩ := ht.2.1 h1; exact ⟨a, c⟩
  · obtain ⟨a, _, c, _⟩ := ht.2.2 h2; exact ⟨a, c⟩

theorem localCount_sum_x (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) (X Y Z : Nat) :
    localCount n s ((X, Y, Z), 0) true + localCount n s ((X, Y, Z), 0) false
      = ringCrossed n s ((X, Y, Z), 0) := by
  have hc : candidates ((X, Y, Z), 0) =
      [((X + 1, Y - 1, Z), 2), ((X + 1, Y, Z - 1), 1),
       ((X + 1, Y, Z), 1), ((X + 1, Y, Z), 2),
       ((X + 1, Y, Z + 1), 1), ((X + 1, Y + 1, Z), 2)] := rfl
  have g2 : crossedB n s ((X + 1, Y, Z), 1) = true → decide (1 ≤ Z) = true := fun h =>
    decide_eq_true_eq.mpr ((crossedB_gate hpin (by omega) h).2.1 rfl).2
  have g3 : crossedB n s ((X + 1, Y, Z), 2) = true → decide (1 ≤ Y) = true := fun h =>
    decide_eq_true_eq.mpr ((crossedB_gate hpin (by omega) h).2.2 rfl).2
  unfold localCount ringCrossed
  rw [hc]
  simp only [ring, List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_x, e2_contributes_false_x]
  simp only [contrib_x2, contrib_x3, contrib_x4, contrib_x5]
  generalize crossedB n s ((X + 1, Y, Z), 1) = a1 at *
  generalize crossedB n s ((X + 1, Y, Z), 2) = a2 at *
  generalize crossedB n s ((X + 1, Y, Z + 1), 1) = a3 at *
  generalize crossedB n s ((X + 1, Y + 1, Z), 2) = a4 at *
  generalize decide (1 ≤ Z) = gz at *
  generalize decide (1 ≤ Y) = gy at *
  generalize s (X + 1, Y, Z) = e
  generalize s (X + 1, Y, Z + 1) = g
  generalize s (X + 1, Y + 1, Z) = h
  revert a1 a2 a3 a4 gz gy e g h
  decide

theorem localCount_sum_y (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) (X Y Z : Nat) :
    localCount n s ((X, Y, Z), 1) true + localCount n s ((X, Y, Z), 1) false
      = ringCrossed n s ((X, Y, Z), 1) := by
  have hc : candidates ((X, Y, Z), 1) =
      [((X - 1, Y + 1, Z), 2), ((X, Y + 1, Z - 1), 0),
       ((X, Y + 1, Z), 0), ((X, Y + 1, Z), 2),
       ((X, Y + 1, Z + 1), 0), ((X + 1, Y + 1, Z), 2)] := rfl
  have g2 : crossedB n s ((X, Y + 1, Z), 0) = true → decide (1 ≤ Z) = true := fun h =>
    decide_eq_true_eq.mpr ((crossedB_gate hpin (by omega) h).1 rfl).2
  have g3 : crossedB n s ((X, Y + 1, Z), 2) = true → decide (1 ≤ X) = true := fun h =>
    decide_eq_true_eq.mpr ((crossedB_gate hpin (by omega) h).2.2 rfl).1
  unfold localCount ringCrossed
  rw [hc]
  simp only [ring, List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_y, e2_contributes_false_y]
  simp only [contrib_y2, contrib_y3, contrib_y4, contrib_y5]
  generalize crossedB n s ((X, Y + 1, Z), 0) = a1 at *
  generalize crossedB n s ((X, Y + 1, Z), 2) = a2 at *
  generalize crossedB n s ((X, Y + 1, Z + 1), 0) = a3 at *
  generalize crossedB n s ((X + 1, Y + 1, Z), 2) = a4 at *
  generalize decide (1 ≤ Z) = gz at *
  generalize decide (1 ≤ X) = gx at *
  generalize s (X, Y + 1, Z) = e
  generalize s (X, Y + 1, Z + 1) = g
  generalize s (X + 1, Y + 1, Z) = h
  revert a1 a2 a3 a4 gz gx e g h
  decide

theorem localCount_sum_z (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) (X Y Z : Nat) :
    localCount n s ((X, Y, Z), 2) true + localCount n s ((X, Y, Z), 2) false
      = ringCrossed n s ((X, Y, Z), 2) := by
  have hc : candidates ((X, Y, Z), 2) =
      [((X - 1, Y, Z + 1), 1), ((X, Y - 1, Z + 1), 0),
       ((X, Y, Z + 1), 0), ((X, Y, Z + 1), 1),
       ((X, Y + 1, Z + 1), 0), ((X + 1, Y, Z + 1), 1)] := rfl
  have g2 : crossedB n s ((X, Y, Z + 1), 0) = true → decide (1 ≤ Y) = true := fun h =>
    decide_eq_true_eq.mpr ((crossedB_gate hpin (by omega) h).1 rfl).1
  have g3 : crossedB n s ((X, Y, Z + 1), 1) = true → decide (1 ≤ X) = true := fun h =>
    decide_eq_true_eq.mpr ((crossedB_gate hpin (by omega) h).2.1 rfl).1
  unfold localCount ringCrossed
  rw [hc]
  simp only [ring, List.filter_cons, List.filter_nil, ite_length, ite_false,
    List.length_cons, List.length_nil, Bool.false_eq_true,
    e1_contributes_false_z, e2_contributes_false_z]
  simp only [contrib_z2, contrib_z3, contrib_z4, contrib_z5]
  generalize crossedB n s ((X, Y, Z + 1), 0) = a1 at *
  generalize crossedB n s ((X, Y, Z + 1), 1) = a2 at *
  generalize crossedB n s ((X, Y + 1, Z + 1), 0) = a3 at *
  generalize crossedB n s ((X + 1, Y, Z + 1), 1) = a4 at *
  generalize decide (1 ≤ Y) = gy at *
  generalize decide (1 ≤ X) = gx at *
  generalize s (X, Y, Z + 1) = e
  generalize s (X, Y + 1, Z + 1) = g
  generalize s (X + 1, Y, Z + 1) = h
  revert a1 a2 a3 a4 gy gx e g h
  decide

/-- **Use counts and the ring**: under shell pinning, the two directional use
    counts of any face add up to the number of crossed ring edges. -/
theorem localCount_sum (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) (f : Face) :
    localCount n s f true + localCount n s f false = ringCrossed n s f := by
  obtain ⟨⟨X, Y, Z⟩, i⟩ := f
  by_cases h0 : i = 0
  · subst h0; exact localCount_sum_x n s hpin X Y Z
  by_cases h1 : i = 1
  · subst h1; exact localCount_sum_y n s hpin X Y Z
  by_cases h2 : i = 2
  · subst h2; exact localCount_sum_z n s hpin X Y Z
  · have hge : 3 ≤ i := by omega
    rw [localCount_eq_zero_of_nf_ge_three n s (X, Y, Z) i hge true,
      localCount_eq_zero_of_nf_ge_three n s (X, Y, Z) i hge false]
    have hr : ring ((X, Y, Z), i) = [] := by
      unfold ring
      match i, h0, h1, h2 with
      | i + 3, _, _, _ => rfl
    simp [ringCrossed, hr]

/-! ### From face use counts to mesh duplicates -/

theorem asmSurface_eq_map {ι φ : Type} (ends : φ → ι × ι)
    (qs : List (List (LabeledEdge φ))) :
    asmSurface ends qs = (faceUses qs).map (dirEdge ends) := by
  induction qs with
  | nil => simp [asmSurface, faceUses]
  | cons q qs ih =>
    simp only [asmSurface, faceUses, List.flatMap_cons, List.map_append, id] at ih ⊢
    rw [ih]

theorem mesh_eq_map (n : Nat) (s : Lat → Bool) :
    (cuberilleStencil n s).mesh
      = (faceUses (cuberilleStencil n s).quads).map (dirEdge (faceEnds n)) :=
  asmSurface_eq_map _ _

/-- A face that steps inside the grid joins `c` and `addCell c k`. -/
theorem faceEnds_of_ne_none (n : Nat) (c : Cell) (k : Nat) (hk : k < 3)
    (h : cellStep n c k ≠ none) : faceEnds n (c, k) = (c, addCell c k) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  have hqa : q = addCell c k := by
    obtain ⟨a, b, z⟩ := c
    interval_cases k <;> simp only [cellStep] at hq <;> split_ifs at hq <;>
      first | (cases hq; done) | (cases hq; simp [addCell])
  unfold faceEnds
  simp [hq, hqa]

/-- `dirEdge` is injective on labeled faces that step inside the grid. -/
theorem dirEdge_inj (n : Nat) (lf1 lf2 : LabeledEdge Face)
    (h1 : cellStep n lf1.face.1 lf1.face.2 ≠ none) (h2 : cellStep n lf2.face.1 lf2.face.2 ≠ none)
    (k1 : lf1.face.2 < 3) (k2 : lf2.face.2 < 3)
    (h : dirEdge (faceEnds n) lf1 = dirEdge (faceEnds n) lf2) : lf1 = lf2 := by
  obtain ⟨⟨⟨a1, b1, c1⟩, d1⟩, w1⟩ := lf1
  obtain ⟨⟨⟨a2, b2, c2⟩, d2⟩, w2⟩ := lf2
  simp only at h1 h2 k1 k2
  have e1 := faceEnds_of_ne_none n (a1, b1, c1) d1 k1 h1
  have e2 := faceEnds_of_ne_none n (a2, b2, c2) d2 k2 h2
  unfold dirEdge at h
  simp only [e1, e2] at h
  interval_cases d1 <;> interval_cases d2 <;> cases w1 <;> cases w2 <;>
    simp [addCell, Prod.ext_iff] at h ⊢ <;> omega

theorem cellStep_ne_none_of_ends_ne (n : Nat) (c : Cell) (k : Nat)
    (h : (faceEnds n (c, k)).1 ≠ (faceEnds n (c, k)).2) : cellStep n c k ≠ none := by
  intro hn
  apply h
  unfold faceEnds
  simp [hn]

/-- Every labeled face of the mesh is a used face of a crossed edge; it steps
    inside the grid and has a normal direction `< 3`. -/
theorem mem_faceUses_props (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) {lf : LabeledEdge Face}
    (hm : lf ∈ faceUses (cuberilleStencil n s).quads) :
    cellStep n lf.face.1 lf.face.2 ≠ none ∧ lf.face.2 < 3 := by
  have h0 : faceUses (cuberilleStencil n s).quads =
      (crossed n s).flatMap fun e => labels e.1 e.2 (s e.1) := by
    simp [StencilComplex.quads, cuberilleStencil, faceUses, List.flatMap_map, Function.comp_def]
  rw [h0] at hm
  obtain ⟨e, he, hlf⟩ := List.mem_flatMap.mp hm
  refine ⟨?_, ?_⟩
  · have hne := (crossed_labels_ok n s hpin he).2 lf hlf
    exact cellStep_ne_none_of_ends_ne n lf.face.1 lf.face.2 hne
  · exact labels_face_dir_lt_three e.1 e.2 (s e.1) (f := lf.face) (dir := lf.forward) hlf

/-- **Classification of duplicate-free meshes.** For a shell-pinned sign field
    the directed cuberille mesh repeats no directed dual edge exactly when no
    cell face has all four of its ring edges crossed. -/
theorem mesh_nodup_iff (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    (cuberilleStencil n s).mesh.Nodup ↔ ∀ f : Face, ringCrossed n s f ≤ 2 := by
  have hbal : ∀ f, localCount n s f true = localCount n s f false :=
    (balanced_iff_local n s).mp (balanced_general n s hpin)
  have hcount : ∀ f dir, (faceUses (cuberilleStencil n s).quads).count ⟨f, dir⟩
      = localCount n s f dir := fun f dir => by
    rw [faceUses_count_eq_uses, uses_length_eq_localCount]
  constructor
  · intro hnd f
    have hfu : (faceUses (cuberilleStencil n s).quads).Nodup := by
      rw [mesh_eq_map] at hnd
      exact List.Nodup.of_map _ hnd
    have h1 := List.nodup_iff_count_le_one.mp hfu ⟨f, true⟩
    rw [hcount] at h1
    have := localCount_sum n s hpin f
    have := hbal f
    omega
  · intro hr
    have hfu : (faceUses (cuberilleStencil n s).quads).Nodup := by
      rw [List.nodup_iff_count_le_one]
      intro lf
      obtain ⟨f, dir⟩ := lf
      rw [hcount]
      have := localCount_sum n s hpin f
      have := hbal f
      have := hr f
      cases dir <;> omega
    rw [mesh_eq_map]
    refine List.Nodup.map_on ?_ hfu
    intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := mem_faceUses_props n s hpin hx
    obtain ⟨hy1, hy2⟩ := mem_faceUses_props n s hpin hy
    exact dirEdge_inj n x y hx1 hy1 hx2 hy2 hxy

/-! ### The geometric form: checkerboard faces -/

/-- A crossed ring edge forces the face to be a genuine grid face. -/
theorem ring_crossed_inCells (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) {f : Face} {e : PadEdge}
    (he : e ∈ ring f) (hc : crossedB n s e = true) : InCells n f.1 ∧ f.2 < 3 := by
  obtain ⟨⟨X, Y, Z⟩, i⟩ := f
  obtain ⟨p, d⟩ := e
  have hi : i < 3 := by
    by_contra hge
    have h3 : 3 ≤ i := by omega
    have hr : ring ((X, Y, Z), i) = [] := by
      unfold ring
      match i, h3 with
      | i + 3, _ => rfl
    rw [hr] at he
    cases he
  have hd : d < 3 := by
    unfold ring at he
    interval_cases i <;> simp at he <;> omega
  have hm := crossed_of_crossedB n s hc (List.mem_range.mpr hd)
  obtain ⟨_, hp, hq, hne⟩ := crossed_spec n s hm
  have ht := pinned_transverse n s hpin hp hne
  obtain ⟨hp1, hp2, hp3⟩ := hp
  refine ⟨?_, hi⟩
  unfold ring at he
  show X < n ∧ Y < n ∧ Z < n
  interval_cases i <;> simp at he <;>
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [succN, InLattice] at hq ht ⊢ <;> simp at hq ht <;> omega

/-- A cell face is a **checkerboard** when the four corner samples of its
    perimeter alternate in sign (the ambiguous face of the cuberille). -/
def Checkerboard (s : Lat → Bool) (f : Face) : Prop :=
  s (perimeterCorners f).1 = s (perimeterCorners f).2.2.2 ∧
  s (perimeterCorners f).2.1 = s (perimeterCorners f).2.2.1 ∧
  s (perimeterCorners f).1 ≠ s (perimeterCorners f).2.1

/-- The number of sign changes around a perimeter, in the order of
    `perimeterCorners` (`e f g h`, cycle `e f h g`). -/
def cross4 (e f g h : Bool) : Nat :=
  (if e != f then 1 else 0) + (if f != h then 1 else 0) +
    (if h != g then 1 else 0) + (if g != e then 1 else 0)

theorem cross4_le_two_iff (e f g h : Bool) :
    cross4 e f g h ≤ 2 ↔ ¬ (e = h ∧ f = g ∧ e ≠ f) := by
  revert e f g h
  decide

theorem len_filter_sum {α : Type} (P : α → Bool) (l : List α) :
    (l.filter P).length = (l.map fun a => if P a = true then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : P a = true
    · simp [List.filter_cons, h, ih, add_comm]
    · have h' : P a = false := by simpa using h
      simp [List.filter_cons, h', ih]

theorem cross_shape (e f g h : Bool) :
    (if e = f then 0 else 1) + ((if e = g then 0 else 1) + ((if g = h then 0 else 1)
      + (if f = h then 0 else 1)))
    = (((if e = f then 0 else 1) + (if f = h then 0 else 1)) + (if h = g then 0 else 1))
      + (if g = e then 0 else 1) := by
  revert e f g h
  decide

theorem crossedB_of_lattice (n : Nat) (s : Lat → Bool) (p : Lat) (d : Nat)
    (h1 : InLattice n p) (h2 : InLattice n (succN p d)) :
    crossedB n s (p, d) = (s p != s (succN p d)) := by
  unfold crossedB
  simp only [decide_eq_true h1, decide_eq_true h2, Bool.true_and]

/-- For a genuine grid face the crossed ring edges are exactly the sign
    changes around its perimeter. -/
theorem ringCrossed_eq (n : Nat) (s : Lat → Bool) {f : Face} (hc : InCells n f.1)
    (hi : f.2 < 3) :
    ringCrossed n s f = cross4 (s (perimeterCorners f).1) (s (perimeterCorners f).2.1)
      (s (perimeterCorners f).2.2.1) (s (perimeterCorners f).2.2.2) := by
  obtain ⟨⟨X, Y, Z⟩, i⟩ := f
  have hX : X < n := hc.1
  have hY : Y < n := hc.2.1
  have hZ : Z < n := hc.2.2
  clear hc
  unfold ringCrossed
  rw [len_filter_sum]
  unfold ring perimeterCorners cross4
  interval_cases i
  all_goals
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [crossedB_of_lattice n s _ _ (by simp only [InLattice]; omega) (by simp only [succN, InLattice]; simp; omega),
      crossedB_of_lattice n s _ _ (by simp only [InLattice]; omega) (by simp only [succN, InLattice]; simp; omega),
      crossedB_of_lattice n s _ _ (by simp only [InLattice]; omega) (by simp only [succN, InLattice]; simp; omega),
      crossedB_of_lattice n s _ _ (by simp only [InLattice]; omega) (by simp only [succN, InLattice]; simp; omega)]
    simp only [succN]
    simp
    exact cross_shape _ _ _ _

/-- **Classification of duplicate-free cuberille meshes (every `n`).**
    For a shell-pinned sign field, the directed dual mesh repeats no directed
    edge exactly when no grid face is a checkerboard (its four perimeter
    samples alternating in sign — the ambiguous face). -/
theorem mesh_nodup_iff_noCheckerboard (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false) :
    (cuberilleStencil n s).mesh.Nodup
      ↔ ∀ f : Face, InCells n f.1 → f.2 < 3 → ¬ Checkerboard s f := by
  rw [mesh_nodup_iff n s hpin]
  constructor
  · intro h f hc hi hcb
    have h1 := h f
    rw [ringCrossed_eq n s hc hi] at h1
    exact (cross4_le_two_iff _ _ _ _).mp h1 ⟨hcb.1, hcb.2.1, hcb.2.2⟩
  · intro h f
    by_cases hin : InCells n f.1 ∧ f.2 < 3
    · rw [ringCrossed_eq n s hin.1 hin.2, cross4_le_two_iff]
      exact fun hc => h f hin.1 hin.2 ⟨hc.1, hc.2.1, hc.2.2⟩
    · have h0 : ringCrossed n s f = 0 := by
        unfold ringCrossed
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro e he hcb
        exact hin (ring_crossed_inCells n s hpin he (by simpa using hcb))
      omega

/-- **The Euler characteristic of a checkerboard-free cuberille mesh** (every
    `n`): `E = 2 F` and `χ = V − F` with no further hypothesis on the mesh. -/
theorem euler_of_noCheckerboard (n : Nat) (s : Lat → Bool)
    (hpin : ∀ p, isShell n p = true → s p = false)
    (hnc : ∀ f : Face, InCells n f.1 → f.2 < 3 → ¬ Checkerboard s f) :
    (QuadEuler.undirected (cuberilleStencil n s).mesh).card = 2 * (crossed n s).length ∧
    ((QuadEuler.vertices (cuberilleStencil n s).mesh).card : Int)
        - (QuadEuler.undirected (cuberilleStencil n s).mesh).card + (crossed n s).length
      = (QuadEuler.vertices (cuberilleStencil n s).mesh).card - (crossed n s).length := by
  have hnd := (mesh_nodup_iff_noCheckerboard n s hpin).mpr hnc
  exact ⟨meshEdges_card_general n s hpin hnd, euler_general n s hpin hnd⟩

/-! ### Bounded cross-check at `n = 3` -/

/-- The interior sign field with index `k` on the `n = 3` lattice: bit `j` of
    `k` is the sign at the `j`-th point of `{1,2}^3` (the same indexing as
    `Cuberille.latSignOf`); everything else is `false`. -/
def interiorField (k : Nat) (p : Lat) : Bool :=
  if p.1 = 1 ∧ p.2.1 = 1 ∧ p.2.2 = 1 then k / 1 % 2 = 1
  else if p.1 = 1 ∧ p.2.1 = 1 ∧ p.2.2 = 2 then k / 2 % 2 = 1
  else if p.1 = 1 ∧ p.2.1 = 2 ∧ p.2.2 = 1 then k / 4 % 2 = 1
  else if p.1 = 1 ∧ p.2.1 = 2 ∧ p.2.2 = 2 then k / 8 % 2 = 1
  else if p.1 = 2 ∧ p.2.1 = 1 ∧ p.2.2 = 1 then k / 16 % 2 = 1
  else if p.1 = 2 ∧ p.2.1 = 1 ∧ p.2.2 = 2 then k / 32 % 2 = 1
  else if p.1 = 2 ∧ p.2.1 = 2 ∧ p.2.2 = 1 then k / 64 % 2 = 1
  else if p.1 = 2 ∧ p.2.1 = 2 ∧ p.2.2 = 2 then k / 128 % 2 = 1
  else false

/-- All faces of the `3 x 3 x 3` cell grid. -/
def faces3 : List Face :=
  (List.range 3).flatMap fun x => (List.range 3).flatMap fun y =>
    (List.range 3).flatMap fun z => (List.range 3).map fun i => ((x, y, z), i)

/-- Computable checkerboard test. -/
def checkerB (s : Lat → Bool) (f : Face) : Bool :=
  (s (perimeterCorners f).1 == s (perimeterCorners f).2.2.2) &&
  (s (perimeterCorners f).2.1 == s (perimeterCorners f).2.2.1) &&
  (s (perimeterCorners f).1 != s (perimeterCorners f).2.1)

/-- The number of the 256 interior fields at `n = 3` whose mesh repeats no
    directed edge equals the number with no checkerboard face, and both are
    `136 = 127 + 9`, the edge-manifold fields of the bounded landscape in
    `Vdb/Cuberille.lean` (`bounded_chi_landscape`). A computed cross-check of
    `mesh_nodup_iff_noCheckerboard` against the actual mesh. -/
theorem nodup_landscape_three :
    ((List.range 256).filter fun k =>
        decide ((cuberilleStencil 3 (interiorField k)).mesh.Nodup)).length = 136 ∧
    ((List.range 256).filter fun k =>
        faces3.all fun f => !checkerB (interiorField k) f).length = 136 ∧
    (∀ k ∈ List.range 256,
        decide ((cuberilleStencil 3 (interiorField k)).mesh.Nodup)
          = faces3.all fun f => !checkerB (interiorField k) f) := by
  native_decide

end PadGrid

end Vdb
