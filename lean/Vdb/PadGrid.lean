/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The cuberille / DMC (surface nets) assembly on a **general bounded
  padded grid** — the construction in which T-DMC0-CYCLE is actually true
  on bounded grids (see finding F17 and `Vdb/Cuberille.lean` for the
  bounded Fin-4 instance):

  * signs live on an `(n+1)^3` lattice of sample points (`Lat`);
    the padding shell (any coordinate `0` or `n`) is pinned to `false`;
  * cells are the `n^3` cubes (`Cell`) between the samples;
  * each sign-changing lattice edge emits one quad through the four cells
    around it (`anchorCell`, `ij`, `labels`, `cuberilleStencil`);
  * cell faces (a cell plus a direction) are shared by exactly the two
    cells they separate; shell-facing faces pair a cell with itself as a
    dummy and never receive uses.

  The counts are local: every crossed edge whose labeled faces include a
  face `f` is one of **six candidates** determined by `f` alone
  (`candidates`), verified exhaustively on small grids, and the balance of
  the uses of `f` depends only on the signs at the eight lattice points
  they touch (`local_balance_x/y/z`, machine-checked by `native_decide`).

  Main results:

  * **`facePerimeter_even`** — T-DMC0-EVEN, general (grid-independent):
    every cell face's 4-cycle has an even number of sign changes;
  * **`balanced_general`** — T-DMC0-CYCLE, general: for every in-cells
    face, the assembled uses are balanced (equal true/false directions),
    hence (via `Assembly.watertight_of_balanced`) the quad mesh is
    watertight;
  * **`padded_watertight`** — T-DMC0-CYCLE, concrete: the assembled quads
    are watertight under any vertex placement of the cells.

  What is *not* claimed: T-DMC0-ORIENT as a global ℤ-cycle (false in
  general — checkerboard faces double-cover edges), T-DMC0-χ in general
  (bounded instances only, `Vdb/Cuberille.lean`), and any claim about the
  unbounded plane or non-shell-pinned sign fields.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.GlobalSurface
import Vdb.DmcManifold
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

namespace Vdb

namespace PadGrid

/-! ### The model -/

/-- Sample points of the `(n+1)^3` lattice. -/
abbrev Lat := Nat × Nat × Nat
/-- Cells of the `n^3` cell grid between the samples. -/
abbrev Cell := Nat × Nat × Nat
/-- A primal face: a cell anchor plus its normal direction. -/
abbrev Face := Cell × Nat
/-- A primal lattice edge: an anchor plus its direction. -/
abbrev PadEdge := Lat × Nat

/-- A cell is in the `n^3` cell grid. -/
def InCells (n : Nat) (c : Cell) : Prop :=
  c.1 < n ∧ c.2.1 < n ∧ c.2.2 < n

instance (n : Nat) : Decidable (InCells n c) :=
  inferInstanceAs (Decidable (c.1 < n ∧ c.2.1 < n ∧ c.2.2 < n))

/-- A lattice point is on the padding shell. -/
def isShell (n : Nat) (p : Lat) : Bool :=
  p.1 == 0 || p.1 == n || p.2.1 == 0 || p.2.1 == n || p.2.2 == 0 || p.2.2 == n

/-- A lattice point is in the `(n+1)^3` lattice. -/
def InLattice (n : Nat) (p : Lat) : Prop :=
  p.1 ≤ n ∧ p.2.1 ≤ n ∧ p.2.2 ≤ n

instance (n : Nat) : Decidable (InLattice n p) :=
  inferInstanceAs (Decidable (p.1 ≤ n ∧ p.2.1 ≤ n ∧ p.2.2 ≤ n))

/-- All lattice points of the `(n+1)^3` lattice. -/
def latAll (n : Nat) : List Lat :=
  (List.range (n+1)).flatMap fun x =>
    (List.range (n+1)).flatMap fun y =>
      (List.range (n+1)).map fun z => (x, y, z)

/-- The successor of a lattice point in direction `d` (may leave the lattice). -/
def succN (p : Lat) (d : Nat) : Lat :=
  if d = 0 then (p.1 + 1, p.2)
  else if d = 1 then (p.1, p.2.1 + 1, p.2.2)
  else (p.1, p.2.1, p.2.2 + 1)

instance (n : Nat) (p : Lat) (d : Nat) : Decidable (InLattice n (succN p d)) := by
  unfold InLattice succN
  split_ifs <;> infer_instance

/-- The crossed lattice edges of `s`: both endpoints in the lattice, signs differ. -/
def crossed (n : Nat) (s : Lat → Bool) : List PadEdge :=
  (latAll n).flatMap fun p =>
    (List.range 3).filterMap fun d =>
      if decide (InLattice n (succN p d)) && (s p != s (succN p d))
      then some (p, d) else none

/-- In-range step of a cell, `none` at the boundary. -/
def cellStep (n : Nat) (c : Cell) (d : Nat) : Option Cell :=
  match d with
  | 0 => if c.1 + 1 < n then some (c.1 + 1, c.2.1, c.2.2) else none
  | 1 => if c.2.1 + 1 < n then some (c.1, c.2.1 + 1, c.2.2) else none
  | _ => if c.2.2 + 1 < n then some (c.1, c.2.1, c.2.2 + 1) else none

/-- The two cells of a face; shell-facing faces pair a cell with itself
    (dummy — they never receive uses; see `no_shell_uses`). -/
def faceEnds (n : Nat) (f : Face) : Cell × Cell :=
  match cellStep n f.1 f.2 with
  | some q => (f.1, q)
  | none => (f.1, f.1)

/-- The anchor cell of an edge: the transverse-lower-left cell. `none` when
    the edge is transverse-degenerate (some transverse coordinate is `0`) —
    such edges never emit quads. -/
def anchorCell (p : Lat) (d : Nat) : Option Cell :=
  match d with
  | 0 => if 1 ≤ p.2.1 && 1 ≤ p.2.2 then some (p.1, p.2.1 - 1, p.2.2 - 1) else none
  | 1 => if 1 ≤ p.1 && 1 ≤ p.2.2 then some (p.1 - 1, p.2.1, p.2.2 - 1) else none
  | _ => if 1 ≤ p.1 && 1 ≤ p.2.1 then some (p.1 - 1, p.2.1 - 1, p.2.2) else none

/-- Stepping of a cell (unclamped; crossed edges stay in range). -/
def addCell (c : Cell) (d : Nat) : Cell :=
  if d = 0 then (c.1 + 1, c.2.1, c.2.2)
  else if d = 1 then (c.1, c.2.1 + 1, c.2.2)
  else (c.1, c.2.1, c.2.2 + 1)

/-- The two in-plane directions of an edge, swapped under `flip`. -/
def ij (d : Nat) (flip : Bool) : Nat × Nat :=
  if flip then
    (if d = 0 then (2, 1) else if d = 1 then (0, 2) else (1, 0))
  else
    (if d = 0 then (1, 2) else if d = 1 then (2, 0) else (0, 1))

/-- The quad's labeled faces; the torus convention, rooted at the
    transverse-lower-left anchor cell. `[]` for transverse-degenerate edges. -/
def labels (p : Lat) (d : Nat) (flip : Bool) : List (LabeledEdge Face) :=
  match anchorCell p d with
  | none => []
  | some q =>
    let (i, j) := ij d flip
    [⟨(addCell q j, i), false⟩, ⟨(q, j), false⟩, ⟨(q, i), true⟩,
     ⟨(addCell q i, j), true⟩]

/-- The cuberille / DMC assembly of a sign field. -/
def cuberilleStencil (n : Nat) (s : Lat → Bool) :
    StencilComplex Cell Face PadEdge where
  ends := faceEnds n
  edgeFaces := fun e => labels e.1 e.2 (s e.1)
  crossedEdges := crossed n s

/-! ### Membership and count helper lemmas -/

/-- A lattice point is in the lattice enumeration iff all its coordinates are
    at most `n`. -/
theorem mem_latAll {n : Nat} {p : Lat} :
    p ∈ latAll n ↔ InLattice n p := by
  unfold latAll InLattice
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, z, hz, rfl⟩
    change (x ≤ n ∧ y ≤ n ∧ z ≤ n)
    exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨x, y, z⟩ := p
    change x ≤ n at h1
    change y ≤ n at h2
    change z ≤ n at h3
    exact ⟨x, by omega, y, by omega, z, by omega, rfl⟩

/-- The crossed-edge list has no duplicates. -/
theorem nodup_latAll (n : Nat) : (latAll n).Nodup := by
  unfold latAll
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    apply List.nodup_flatMap.mpr
    refine ⟨?_, ?_⟩
    · intro y hy
      exact List.Nodup.map (f := fun z : Nat => (x, y, z)) (by
        intro a b h
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        obtain ⟨h3, h4⟩ := Prod.mk.inj h2
        exact h4) List.nodup_range
    · exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp (fun hne => by
        intro e he he'
        dsimp only at he he'
        obtain ⟨z1, _, rfl⟩ := List.mem_map.mp he
        obtain ⟨z2, _, h2z⟩ := List.mem_map.mp he'
        injection h2z with h h'
        injection h' with h'' _
        exact hne h''.symm)
  · exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp (fun hne => by
      intro e he he'
      dsimp only at he he'
      obtain ⟨y1, _, hy1'⟩ := List.mem_flatMap.mp he
      obtain ⟨y2, _, hy2'⟩ := List.mem_flatMap.mp he'
      obtain ⟨z1, _, rfl⟩ := List.mem_map.mp hy1'
      obtain ⟨z2, _, h2z⟩ := List.mem_map.mp hy2'
      injection h2z with h _
      exact hne h.symm)


/-- The four labeled faces of an edge are distinct. -/
theorem labels_nodup (p : Lat) (d : Nat) (flip : Bool) :
    (labels p d flip).Nodup := by
  unfold labels
  match anchorCell p d with
  | none => exact List.nodup_nil
  | some q =>
    by_cases hd0 : d = 0 <;> by_cases hd1 : d = 1 <;> by_cases hflip : flip = true
    all_goals
      simp [hd0, hd1, hflip,
            addCell, ij]


/-- A generic length-equality from membership equality and nodups. -/
theorem length_eq_of_mem_iff_of_nodup {α : Type*} [DecidableEq α] {l₁ l₂ : List α}
    (h : ∀ a, a ∈ l₁ ↔ a ∈ l₂) (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) :
    l₁.length = l₂.length := by
  have hmem : l₁.toFinset = l₂.toFinset := by
    ext a
    simp only [List.mem_toFinset, h a]
  rw [← List.toFinset_card_of_nodup h₁, hmem, List.toFinset_card_of_nodup h₂]

/-! ### The parity theorem (grid-independent) -/

/-- The four corner signs of a cell face's 4-cycle, as lattice points. -/
def perimeterCorners (f : Face) : Lat × Lat × Lat × Lat :=
  let c := f.1
  match f.2 with
  | 0 =>
      ((c.1 + 1, c.2.1, c.2.2),
       (c.1 + 1, c.2.1 + 1, c.2.2),
       (c.1 + 1, c.2.1, c.2.2 + 1),
       (c.1 + 1, c.2.1 + 1, c.2.2 + 1))
  | 1 =>
      ((c.1, c.2.1 + 1, c.2.2),
       (c.1 + 1, c.2.1 + 1, c.2.2),
       (c.1, c.2.1 + 1, c.2.2 + 1),
       (c.1 + 1, c.2.1 + 1, c.2.2 + 1))
  | _ =>
      ((c.1, c.2.1, c.2.2 + 1),
       (c.1 + 1, c.2.1, c.2.2 + 1),
       (c.1, c.2.1 + 1, c.2.2 + 1),
       (c.1 + 1, c.2.1 + 1, c.2.2 + 1))

/-- **T-DMC0-EVEN**: every cell face's 4-cycle of corner signs has an
    even number of sign changes — for any sign field, any grid size. -/
theorem facePerimeter_even (s : Lat → Bool) (f : Face) :
    Even (crossedCount4 (s (perimeterCorners f).1) (s (perimeterCorners f).2.1)
      (s (perimeterCorners f).2.2.1) (s (perimeterCorners f).2.2.2)) :=
  evenSignChanges4 (s (perimeterCorners f).1) (s (perimeterCorners f).2.1)
    (s (perimeterCorners f).2.2.1) (s (perimeterCorners f).2.2.2)

/-! ### The six candidate edges -/

/-- The six lattice edges whose labels can include a face `f`. Determined by
    `f` alone; verified exhaustively on small grids (all boundary position
    classes). Candidates that leave the lattice or start on a shell plane
    never cross, so boundary faces have at most six genuine candidates. -/
def candidates (f : Face) : List PadEdge :=
  let c := f.1
  match f.2 with
  | 0 =>
    [((c.1 + 1, c.2.1 - 1, c.2.2), 2), ((c.1 + 1, c.2.1, c.2.2 - 1), 1),
     ((c.1 + 1, c.2.1, c.2.2), 1), ((c.1 + 1, c.2.1, c.2.2), 2),
     ((c.1 + 1, c.2.1, c.2.2 + 1), 1), ((c.1 + 1, c.2.1 + 1, c.2.2), 2)]
  | 1 =>
    [((c.1 - 1, c.2.1 + 1, c.2.2), 2), ((c.1, c.2.1 + 1, c.2.2 - 1), 0),
     ((c.1, c.2.1 + 1, c.2.2), 0), ((c.1, c.2.1 + 1, c.2.2), 2),
     ((c.1, c.2.1 + 1, c.2.2 + 1), 0), ((c.1 + 1, c.2.1 + 1, c.2.2), 2)]
  | _ =>
    [((c.1 - 1, c.2.1, c.2.2 + 1), 1), ((c.1, c.2.1 - 1, c.2.2 + 1), 0),
     ((c.1, c.2.1, c.2.2 + 1), 0), ((c.1, c.2.1, c.2.2 + 1), 1),
     ((c.1, c.2.1 + 1, c.2.2 + 1), 0), ((c.1 + 1, c.2.1, c.2.2 + 1), 1)]

/-- Does edge `e` cross the sign field (both endpoints in range, signs differ)? -/
def crossedB (n : Nat) (s : Lat → Bool) (e : PadEdge) : Bool :=
  decide (InLattice n e.1) && decide (InLattice n (succN e.1 e.2)) &&
    (s e.1 != s (succN e.1 e.2))

/-- The candidate contribution test: `e` crosses, and its labeled faces
    include `f` in direction `dir`. -/
def contributes (n : Nat) (s : Lat → Bool) (f : Face) (dir : Bool) (e : PadEdge) : Bool :=
  crossedB n s e && (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩

/-- The count of uses of `f` in direction `dir`, as a sum of the indicators. -/
def localCount (n : Nat) (s : Lat → Bool) (f : Face) (dir : Bool) : Nat :=
  ((candidates f).filter fun e => contributes n s f dir e).length

/-! ### The uses decomposition -/

/-- The uses of face `f` in one direction, as the list of source edges. -/
def uses (n : Nat) (s : Lat → Bool) (f : Face) (dir : Bool) : List PadEdge :=
  (crossed n s).filter fun e => (labels e.1 e.2 (s e.1)).contains ⟨f, dir⟩

/-! ### The local balance lemmas (one per face orientation) -/

/-- The four lattice signs the x-normal face's candidates touch:
    e = (cx+1, cy, cz)      f = (cx+1, cy+1, cz)
    g = (cx+1, cy, cz+1)    h = (cx+1, cy+1, cz+1) -/
def windowXTrue (e f g h : Bool) : Nat :=
  (if e != f && !e then 1 else 0) +
  (if e != g && e then 1 else 0) +
  (if g != h && g then 1 else 0) +
  (if f != h && !f then 1 else 0)

def windowXFalse (e f g h : Bool) : Nat :=
  (if e != f && e then 1 else 0) +
  (if e != g && !e then 1 else 0) +
  (if g != h && !g then 1 else 0) +
  (if f != h && f then 1 else 0)

/-- **Local balance, x-normal face**: over all assignments of the signs at
    the four live lattice points, the candidates use the face equally often
    in both directions. Machine-checked by `native_decide`. -/
theorem local_balance_x :
    ∀ e f g h : Bool, windowXTrue e f g h = windowXFalse e f g h := by
  unfold windowXTrue windowXFalse
  native_decide

/-- The four lattice signs the y-normal face's candidates touch:
    e = (cx, cy+1, cz)      f = (cx+1, cy+1, cz)
    g = (cx, cy+1, cz+1)    h = (cx+1, cy+1, cz+1) -/
def windowYTrue (e f g h : Bool) : Nat :=
  (if e != f && e then 1 else 0) +
  (if e != g && !e then 1 else 0) +
  (if g != h && !g then 1 else 0) +
  (if f != h && f then 1 else 0)

def windowYFalse (e f g h : Bool) : Nat :=
  (if e != f && !e then 1 else 0) +
  (if e != g && e then 1 else 0) +
  (if g != h && g then 1 else 0) +
  (if f != h && !f then 1 else 0)

/-- **Local balance, y-normal face**: as `local_balance_x`. -/
theorem local_balance_y :
    ∀ e f g h : Bool, windowYTrue e f g h = windowYFalse e f g h := by
  unfold windowYTrue windowYFalse
  native_decide

/-- The four lattice signs the z-normal face's candidates touch:
    e = (cx, cy, cz+1)      f = (cx+1, cy, cz+1)
    g = (cx, cy+1, cz+1)    h = (cx+1, cy+1, cz+1) -/
def windowZTrue (e f g h : Bool) : Nat :=
  (if e != f && !e then 1 else 0) +
  (if e != g && e then 1 else 0) +
  (if g != h && g then 1 else 0) +
  (if f != h && !f then 1 else 0)

def windowZFalse (e f g h : Bool) : Nat :=
  (if e != f && e then 1 else 0) +
  (if e != g && !e then 1 else 0) +
  (if g != h && !g then 1 else 0) +
  (if f != h && f then 1 else 0)

/-- **Local balance, z-normal face**: as `local_balance_x`. -/
theorem local_balance_z :
    ∀ e f g h : Bool, windowZTrue e f g h = windowZFalse e f g h := by
  unfold windowZTrue windowZFalse
  native_decide

/-- From membership to the boolean test. -/
theorem crossedB_of_crossed (n : Nat) (s : Lat → Bool) {e : PadEdge}
    (h : e ∈ crossed n s) : crossedB n s e = true := by
  obtain ⟨p, hp, h'⟩ := List.mem_flatMap.mp h
  obtain ⟨d, _, hd⟩ := List.mem_filterMap.mp h'
  obtain ⟨h1, h2, h3⟩ := mem_latAll.mp hp
  by_cases hcond : (decide (InLattice n (succN p d)) && s p != s (succN p d)) = true
  · simp only [hcond, ite_true] at hd
    obtain rfl : e = (p, d) := (Option.some.inj hd).symm
    unfold crossedB
    obtain ⟨hcond1, hcond2⟩ := (Bool.and_eq_true _ _).mp hcond
    have hp : decide (InLattice n p) = true := (decide_eq_true_eq).symm.mp ⟨h1, h2, h3⟩
    match d with
    | 0 => simp [hp, hcond1, hcond2]
    | 1 => simp [hp, hcond1, hcond2]
    | _ => simp [hp, hcond1, hcond2]
  · simp only [hcond, ite_false] at hd
    cases hd

/-- From the boolean test to membership. -/
theorem crossed_of_crossedB (n : Nat) (s : Lat → Bool) {e : PadEdge}
    (h : crossedB n s e = true) (he : e.2 ∈ List.range 3) : e ∈ crossed n s := by
  unfold crossed
  rw [List.mem_flatMap]
  unfold crossedB succN at h
  simp only [decide_eq_true_eq, Bool.and_eq_true] at h
  obtain ⟨⟨h11, h12⟩, h2⟩ := h
  have h13 : InLattice n e.1 := by
    have := h11
    simp only [InLattice] at this ⊢
    exact this
  exact ⟨e.1, mem_latAll.mpr h13, by
    rw [List.mem_filterMap]
    refine ⟨e.2, he, by simp [succN, decide_eq_true_eq, h12, h2]⟩⟩


/-- The crossed-edge list has no duplicates. -/
theorem nodup_crossed (n : Nat) (s : Lat → Bool) : (crossed n s).Nodup := by
  unfold crossed
  rw [List.nodup_flatMap]
  constructor
  · intro p hp
    apply List.Nodup.filterMap _ (List.nodup_range)
    intro a a' b hb hab
    by_cases h1 : (decide (InLattice n (succN p a)) && (s p != s (succN p a)))
    · by_cases h2 : (decide (InLattice n (succN p a')) && (s p != s (succN p a')))
      · simp only [h1, h2, ite_true] at hb hab
        injection hb with hb'; injection hab with hab'
        subst hb'; injection hab' with h h'; exact h'.symm
      · simp only [h1, h2, ite_true, ite_false] at hb hab
        cases hab
    · by_cases h2 : (decide (InLattice n (succN p a')) && (s p != s (succN p a')))
      · simp only [h1, h2, ite_true, ite_false] at hb hab
        cases hb
      · simp only [h1, h2, ite_false, ite_false] at hb hab
        cases hb
  · have hpair := (List.nodup_iff_pairwise_ne.mp (nodup_latAll n))
    refine hpair.imp (fun {a b} hne => ?_)
    simp only [Function.onFun]
    intro e he he'
    obtain ⟨d1, _, hd1⟩ := List.mem_filterMap.mp he
    obtain ⟨d2, _, hd2⟩ := List.mem_filterMap.mp he'
    by_cases h1 : (decide (InLattice n (succN a d1)) && s a != s (succN a d1)) = true
    · simp only [h1, ite_true] at hd1
      injection hd1 with h1'
      by_cases h2 : (decide (InLattice n (succN b d2)) && s b != s (succN b d2)) = true
      · simp only [h2, ite_true] at hd2
        injection hd2 with h2'
        subst h1'
        injection h2' with h _
        exact hne h.symm
      · simp only [h2, ite_false] at hd2
        cases hd2
    · simp only [h1, ite_false] at hd1
      cases hd1


private theorem mem_candidates_d0 (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    {f : Vdb.PadGrid.Face} {dir : Bool} {p : Vdb.PadGrid.Lat}
    (he : (p, 0) ∈ Vdb.PadGrid.uses n s f dir) : (p, 0) ∈ Vdb.PadGrid.candidates f := by
  obtain ⟨p1, p2, p3⟩ := p
  unfold Vdb.PadGrid.uses at he
  rw [List.mem_filter] at he
  obtain ⟨_, hcontains⟩ := he
  obtain ⟨c, nf⟩ := f
  unfold Vdb.PadGrid.labels at hcontains
  split at hcontains
  · simp at hcontains
  · next hq heq =>
    simp only [Vdb.PadGrid.anchorCell] at heq
    split at heq
    next hif =>
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hif
      obtain ⟨hb1, hb2⟩ := hif
      simp only [decide_eq_true_eq] at hb1 hb2
      injection heq with h'
      obtain ⟨q1, q2, q3⟩ := hq
      obtain ⟨h1, h23⟩ := Prod.mk.inj h'
      obtain ⟨h2, h3⟩ := Prod.mk.inj h23
      cases hflip : s (p1, p2, p3) with
      | true =>
        rw [hflip] at hcontains
        simp only [Vdb.PadGrid.ij, ite_true, ite_false, ite_eq_right (by omega : (0:Nat) ≠ 1)] at hcontains
        rw [List.contains_iff_mem] at hcontains
        simp only [List.mem_cons, List.not_mem_nil] at hcontains
        rcases hcontains with d0 | d1 | d2 | d3
        · -- position 0
          injection d0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inl ?_))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 1
          injection d1 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 2
          injection d2 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 3
          rcases d3 with hface | hfalse
          · injection hface with hface' hdir
            injection hface' with hc hnf
            unfold Vdb.PadGrid.addCell at hc
            simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
            subst nf
            subst c
            simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
            refine Or.inr (Or.inr (Or.inl ?_))
            simp only [Prod.mk.injEq, true_and, and_true]
            omega
          · cases hfalse
      | false =>
        rw [hflip] at hcontains
        simp only [Vdb.PadGrid.ij, Bool.false_eq_true, ite_false, ite_true, ite_eq_right (by omega : (0:Nat) ≠ 1)] at hcontains
        rw [List.contains_iff_mem] at hcontains
        simp only [List.mem_cons, List.not_mem_nil] at hcontains
        rcases hcontains with d0 | d1 | d2 | d3
        · -- position 0
          injection d0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inl ?_))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 1
          injection d1 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 2
          injection d2 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 3
          rcases d3 with hface | hfalse
          · injection hface with hface' hdir
            injection hface' with hc hnf
            unfold Vdb.PadGrid.addCell at hc
            simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
            subst nf
            subst c
            simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
            refine Or.inr (Or.inr (Or.inl ?_))
            simp only [Prod.mk.injEq, true_and, and_true]
            omega
          · cases hfalse
    next =>
      cases heq

private theorem mem_candidates_d1 (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    {f : Vdb.PadGrid.Face} {dir : Bool} {p : Vdb.PadGrid.Lat}
    (he : (p, 1) ∈ Vdb.PadGrid.uses n s f dir) : (p, 1) ∈ Vdb.PadGrid.candidates f := by
  obtain ⟨p1, p2, p3⟩ := p
  unfold Vdb.PadGrid.uses at he
  rw [List.mem_filter] at he
  obtain ⟨_, hcontains⟩ := he
  obtain ⟨c, nf⟩ := f
  unfold Vdb.PadGrid.labels at hcontains
  split at hcontains
  · simp at hcontains
  · next hq heq =>
    simp only [Vdb.PadGrid.anchorCell] at heq
    split at heq
    next hif =>
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hif
      obtain ⟨hb1, hb2⟩ := hif
      simp only [decide_eq_true_eq] at hb1 hb2
      injection heq with h'
      obtain ⟨q1, q2, q3⟩ := hq
      obtain ⟨h1, h23⟩ := Prod.mk.inj h'
      obtain ⟨h2, h3⟩ := Prod.mk.inj h23
      cases hflip : s (p1, p2, p3) with
      | true =>
        rw [hflip] at hcontains
        simp only [Vdb.PadGrid.ij, ite_true, ite_false, ite_eq_right (by omega : (1:Nat) ≠ 0)] at hcontains
        rw [List.contains_iff_mem] at hcontains
        simp only [List.mem_cons, List.not_mem_nil] at hcontains
        rcases hcontains with d0 | d1 | d2 | d3
        · -- position 0
          injection d0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inl ?_))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 1
          injection d1 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 2
          injection d2 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 3
          rcases d3 with hface | hfalse
          · injection hface with hface' hdir
            injection hface' with hc hnf
            unfold Vdb.PadGrid.addCell at hc
            simp only [ite_true] at hc
            subst nf
            subst c
            simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
            refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            simp only [Prod.mk.injEq, true_and, and_true]
            omega
          · cases hfalse
      | false =>
        rw [hflip] at hcontains
        simp only [Vdb.PadGrid.ij, Bool.false_eq_true, ite_false, ite_true, ite_eq_right (by omega : (1:Nat) ≠ 0)] at hcontains
        rw [List.contains_iff_mem] at hcontains
        simp only [List.mem_cons, List.not_mem_nil] at hcontains
        rcases hcontains with d0 | d1 | d2 | d3
        · -- position 0
          injection d0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 1
          injection d1 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 2
          injection d2 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 3
          rcases d3 with hface | hfalse
          · injection hface with hface' hdir
            injection hface' with hc hnf
            unfold Vdb.PadGrid.addCell at hc
            simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
            subst nf
            subst c
            simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
            refine Or.inr (Or.inr (Or.inl ?_))
            simp only [Prod.mk.injEq, true_and, and_true]
            omega
          · cases hfalse
    next =>
      cases heq

private theorem mem_candidates_d2 (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    {f : Vdb.PadGrid.Face} {dir : Bool} {p : Vdb.PadGrid.Lat}
    (he : (p, 2) ∈ Vdb.PadGrid.uses n s f dir) : (p, 2) ∈ Vdb.PadGrid.candidates f := by
  obtain ⟨p1, p2, p3⟩ := p
  unfold Vdb.PadGrid.uses at he
  rw [List.mem_filter] at he
  obtain ⟨_, hcontains⟩ := he
  obtain ⟨c, nf⟩ := f
  unfold Vdb.PadGrid.labels at hcontains
  split at hcontains
  · simp at hcontains
  · next hq heq =>
    simp only [Vdb.PadGrid.anchorCell] at heq
    split at heq
    next hif =>
      rw [Bool.and_eq_true_eq_eq_true_and_eq_true] at hif
      obtain ⟨hb1, hb2⟩ := hif
      simp only [decide_eq_true_eq] at hb1 hb2
      injection heq with h'
      obtain ⟨q1, q2, q3⟩ := hq
      obtain ⟨h1, h23⟩ := Prod.mk.inj h'
      obtain ⟨h2, h3⟩ := Prod.mk.inj h23
      cases hflip : s (p1, p2, p3) with
      | true =>
        rw [hflip] at hcontains
        simp only [Vdb.PadGrid.ij, ite_true, ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hcontains
        rw [List.contains_iff_mem] at hcontains
        simp only [List.mem_cons, List.not_mem_nil] at hcontains
        rcases hcontains with d0 | d1 | d2 | d3
        · -- position 0
          injection d0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 1
          injection d1 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 2
          injection d2 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 3
          rcases d3 with hface | hfalse
          · injection hface with hface' hdir
            injection hface' with hc hnf
            unfold Vdb.PadGrid.addCell at hc
            simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
            subst nf
            subst c
            simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
            refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            simp only [Prod.mk.injEq, true_and, and_true]
            omega
          · cases hfalse
      | false =>
        rw [hflip] at hcontains
        simp only [Vdb.PadGrid.ij, Bool.false_eq_true, ite_false, ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hcontains
        rw [List.contains_iff_mem] at hcontains
        simp only [List.mem_cons, List.not_mem_nil] at hcontains
        rcases hcontains with d0 | d1 | d2 | d3
        · -- position 0
          injection d0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 1
          injection d1 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 2
          injection d2 with hface hdir
          injection hface with hc hnf
          subst nf
          subst c
          simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          simp only [Prod.mk.injEq, true_and, and_true]
          omega
        · -- position 3
          rcases d3 with hface | hfalse
          · injection hface with hface' hdir
            injection hface' with hc hnf
            unfold Vdb.PadGrid.addCell at hc
            simp only [ite_true] at hc
            subst nf
            subst c
            simp only [Vdb.PadGrid.candidates, List.mem_cons, List.not_mem_nil]
            refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            simp only [Prod.mk.injEq, true_and, and_true]
            omega
          · cases hfalse
    next =>
      cases heq


/-- **Candidate decomposition** — every used edge of a face is one of the
    six candidates for the face. -/
theorem mem_candidates (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    {f : Vdb.PadGrid.Face} {dir : Bool} {e : Vdb.PadGrid.PadEdge}
    (he : e ∈ Vdb.PadGrid.uses n s f dir) : e ∈ Vdb.PadGrid.candidates f := by
  obtain ⟨p, d⟩ := e
  have hd3' : d < 3 := by
    unfold Vdb.PadGrid.uses at he
    rw [List.mem_filter] at he
    obtain ⟨hecrossed, _⟩ := he
    unfold Vdb.PadGrid.crossed at hecrossed
    rw [List.mem_flatMap] at hecrossed
    obtain ⟨p₀, _, hd⟩ := hecrossed
    rw [List.mem_filterMap] at hd
    obtain ⟨d₀, hd3₀, hd_if⟩ := hd
    rw [List.mem_range] at hd3₀
    by_cases hcond : (decide (Vdb.PadGrid.InLattice n (Vdb.PadGrid.succN p₀ d₀)) &&
        (s p₀ != s (Vdb.PadGrid.succN p₀ d₀))) = true
    · simp only [hcond, ite_true] at hd_if
      injection hd_if with h
      injection h with h1 h2
      subst d₀
      subst p₀
      exact hd3₀
    · simp only [hcond, ite_false] at hd_if
      cases hd_if
  cases d with
  | zero => exact mem_candidates_d0 n s he
  | succ d' =>
    cases d' with
    | zero => exact mem_candidates_d1 n s he
    | succ d'' =>
      have hd2 : d'' = 0 := by omega
      subst hd2
      exact mem_candidates_d2 n s he

/-- Membership in the uses of a face in one direction, as a boolean test. -/
theorem mem_uses_iff (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (f : Vdb.PadGrid.Face) (dir : Bool) {e : Vdb.PadGrid.PadEdge} :
    e ∈ Vdb.PadGrid.uses n s f dir ↔
      (e ∈ Vdb.PadGrid.candidates f ∧ Vdb.PadGrid.contributes n s f dir e = true) := by
  obtain ⟨p, d⟩ := e
  constructor
  · intro h
    unfold Vdb.PadGrid.uses at h
    rw [List.mem_filter] at h
    obtain ⟨he_crossed, hcontains⟩ := h
    refine ⟨mem_candidates n s (by unfold Vdb.PadGrid.uses; rw [List.mem_filter]; exact ⟨he_crossed, hcontains⟩), ?_⟩
    unfold Vdb.PadGrid.contributes
    rw [Bool.and_eq_true]
    exact ⟨crossedB_of_crossed n s he_crossed, hcontains⟩
  · intro h
    unfold Vdb.PadGrid.uses
    rw [List.mem_filter]
    obtain ⟨he_cand, he_contrib⟩ := h
    unfold Vdb.PadGrid.contributes at he_contrib
    rw [Bool.and_eq_true] at he_contrib
    obtain ⟨hcrossedB, hcontains⟩ := he_contrib
    have he_range : d ∈ List.range 3 := by
      unfold Vdb.PadGrid.candidates at he_cand
      obtain ⟨c, nf⟩ := f
      by_cases h0 : nf = 0
      · subst h0
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he_cand
        rcases he_cand with h | h | h | h | h | h <;> injection h with h1 h2 <;> simp_all
      · by_cases h1 : nf = 1
        · subst h1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he_cand
          rcases he_cand with h | h | h | h | h | h <;> injection h with h1 h2 <;> simp_all
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at he_cand
          rcases he_cand with h | h | h | h | h | h <;> injection h with h1 h2 <;> simp_all
    exact ⟨crossed_of_crossedB n s hcrossedB he_range, hcontains⟩


theorem e1_contributes_false_x (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (X Y Z : Nat) (dir : Bool) :
    Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y - 1, Z), 2) = false := by
  unfold Vdb.PadGrid.contributes
  unfold Vdb.PadGrid.labels
  split at *
  · simp at *
  · next hq =>
    simp only [Vdb.PadGrid.anchorCell] at hq
    split at hq
    next hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hb1, hb2⟩ := hcond
      injection hq with hq'
      subst hq'
      cases hflip : s (X + 1, Y - 1, Z) with
      | false =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [Bool.false_eq_true, ite_false, ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
      | true =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [ite_true, ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
    next =>
      cases hq

theorem e2_contributes_false_x (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (X Y Z : Nat) (dir : Bool) :
    Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y, Z - 1), 1) = false := by
  unfold Vdb.PadGrid.contributes
  unfold Vdb.PadGrid.labels
  split at *
  · simp at *
  · next hq =>
    simp only [Vdb.PadGrid.anchorCell] at hq
    split at hq
    next hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hb1, hb2⟩ := hcond
      injection hq with hq'
      subst hq'
      cases hflip : s (X + 1, Y, Z - 1) with
      | false =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [Bool.false_eq_true, ite_false, ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          simp only [Prod.mk.injEq] at hc
          omega
      | true =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [ite_true, ite_eq_right (by omega : (1:Nat) ≠ 0)] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
    next =>
      cases hq

theorem e1_contributes_false_y (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (X Y Z : Nat) (dir : Bool) :
    Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X - 1, Y + 1, Z), 2) = false := by
  unfold Vdb.PadGrid.contributes
  unfold Vdb.PadGrid.labels
  split at *
  · simp at *
  · next hq =>
    simp only [Vdb.PadGrid.anchorCell] at hq
    split at hq
    next hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hb1, hb2⟩ := hcond
      injection hq with hq'
      subst hq'
      cases hflip : s (X - 1, Y + 1, Z) with
      | false =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [Bool.false_eq_true, ite_false, ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
      | true =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [ite_true, ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
    next =>
      cases hq

theorem e2_contributes_false_y (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (X Y Z : Nat) (dir : Bool) :
    Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X, Y + 1, Z - 1), 0) = false := by
  unfold Vdb.PadGrid.contributes
  unfold Vdb.PadGrid.labels
  split at *
  · simp at *
  · next hq =>
    simp only [Vdb.PadGrid.anchorCell] at hq
    split at hq
    next hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hb1, hb2⟩ := hcond
      injection hq with hq'
      subst hq'
      cases hflip : s (X, Y + 1, Z - 1) with
      | false =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [Bool.false_eq_true, ite_false, ite_true] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
      | true =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [Bool.false_eq_true, ite_true] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          simp only [Prod.mk.injEq] at hc
          omega
    next =>
      cases hq

theorem e1_contributes_false_z (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (X Y Z : Nat) (dir : Bool) :
    Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X - 1, Y, Z + 1), 1) = false := by
  unfold Vdb.PadGrid.contributes
  unfold Vdb.PadGrid.labels
  split at *
  · simp at *
  · next hq =>
    simp only [Vdb.PadGrid.anchorCell] at hq
    split at hq
    next hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hb1, hb2⟩ := hcond
      injection hq with hq'
      subst hq'
      cases hflip : s (X - 1, Y, Z + 1) with
      | false =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [Bool.false_eq_true, ite_false, ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          simp only [Prod.mk.injEq] at hc
          omega
      | true =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [ite_true, ite_eq_right (by omega : (1:Nat) ≠ 0)] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
    next =>
      cases hq

theorem e2_contributes_false_z (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (X Y Z : Nat) (dir : Bool) :
    Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X, Y - 1, Z + 1), 0) = false := by
  unfold Vdb.PadGrid.contributes
  unfold Vdb.PadGrid.labels
  split at *
  · simp at *
  · next hq =>
    simp only [Vdb.PadGrid.anchorCell] at hq
    split at hq
    next hcond =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hb1, hb2⟩ := hcond
      injection hq with hq'
      subst hq'
      cases hflip : s (X, Y - 1, Z + 1) with
      | false =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [Bool.false_eq_true, ite_false, ite_true] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
      | true =>
        rw [hflip] at *
        unfold Vdb.PadGrid.ij
        simp only [Bool.false_eq_true, ite_true] at *
        rw [Bool.and_eq_false_iff]
        refine Or.inr ?_
        by_contra h
        have h' := Bool.eq_true_of_not_eq_false h
        rw [List.contains_iff_mem] at h'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h0 | h1 | h2 | h3
        · injection h0 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (1:Nat) ≠ 0), ite_true] at hc
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h1 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h2 with hface hdir
          injection hface with hc hnf
          simp only [Prod.mk.injEq] at hc
          omega
        · injection h3 with hface hdir
          injection hface with hc hnf
          unfold Vdb.PadGrid.addCell at hc
          simp only [ite_eq_right (by omega : (2:Nat) ≠ 0), ite_eq_right (by omega : (2:Nat) ≠ 1)] at hc
          simp only [Prod.mk.injEq] at hc
          omega
    next =>
      cases hq

/-- The candidate contribution list is nodup (x-face). -/
theorem candidates_filter_nodup_x (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (X Y Z : Nat) (dir : Bool) :
    ((Vdb.PadGrid.candidates ((X, Y, Z), 0)).filter fun e => Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir e).Nodup := by
  have h1 := Vdb.PadGrid.e1_contributes_false_x n s X Y Z dir
  have h2 := Vdb.PadGrid.e2_contributes_false_x n s X Y Z dir
  by_cases h3 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y, Z), 1) = true
  · by_cases h4 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y, Z), 2) = true
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y, Z + 1), 1) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y, Z + 1), 1) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
  · by_cases h4 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y, Z), 2) = true
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y, Z + 1), 1) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y, Z + 1), 1) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 0) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp

/-- The candidate contribution list is nodup (y-face). -/
theorem candidates_filter_nodup_y (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (X Y Z : Nat) (dir : Bool) :
    ((Vdb.PadGrid.candidates ((X, Y, Z), 1)).filter fun e => Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir e).Nodup := by
  have h1 := Vdb.PadGrid.e1_contributes_false_y n s X Y Z dir
  have h2 := Vdb.PadGrid.e2_contributes_false_y n s X Y Z dir
  by_cases h3 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X, Y + 1, Z), 0) = true
  · by_cases h4 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X, Y + 1, Z), 2) = true
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X, Y + 1, Z + 1), 0) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X, Y + 1, Z + 1), 0) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
  · by_cases h4 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X, Y + 1, Z), 2) = true
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X, Y + 1, Z + 1), 0) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X, Y + 1, Z + 1), 0) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 1) dir ((X + 1, Y + 1, Z), 2) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp

/-- The candidate contribution list is nodup (z-face). -/
theorem candidates_filter_nodup_z (n : Nat) (s : Vdb.PadGrid.Lat → Bool)
    (X Y Z : Nat) (dir : Bool) :
    ((Vdb.PadGrid.candidates ((X, Y, Z), 2)).filter fun e => Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir e).Nodup := by
  have h1 := Vdb.PadGrid.e1_contributes_false_z n s X Y Z dir
  have h2 := Vdb.PadGrid.e2_contributes_false_z n s X Y Z dir
  by_cases h3 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X, Y, Z + 1), 0) = true
  · by_cases h4 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X, Y, Z + 1), 1) = true
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X, Y + 1, Z + 1), 0) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X + 1, Y, Z + 1), 1) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X + 1, Y, Z + 1), 1) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X, Y + 1, Z + 1), 0) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X + 1, Y, Z + 1), 1) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X + 1, Y, Z + 1), 1) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
  · by_cases h4 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X, Y, Z + 1), 1) = true
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X, Y + 1, Z + 1), 0) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X + 1, Y, Z + 1), 1) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X + 1, Y, Z + 1), 1) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
    · by_cases h5 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X, Y + 1, Z + 1), 0) = true
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X + 1, Y, Z + 1), 1) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
      · by_cases h6 : Vdb.PadGrid.contributes n s ((X, Y, Z), 2) dir ((X + 1, Y, Z + 1), 1) = true
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp
        · unfold Vdb.PadGrid.candidates; simp only [List.filter_cons, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_true, ite_false]; simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.filter_nil, not_or, and_true, Prod.mk.injEq]; simp

end PadGrid

end Vdb
