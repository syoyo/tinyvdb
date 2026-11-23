/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-2: edge collapse on the shared index mesh (`Vdb/PhysMesh.lean`). The C
  simplifier repeatedly collapses an edge `a—b` onto `a` after checking the
  link condition (the two endpoints share exactly the two opposite vertices of
  the incident faces). This module models the retarget/degenerate-face-removal
  transform and proves the counting contracts: faces never increase, unused
  vertices leave the topology unchanged, and the Euler arithmetic of an
  interior collapse (`V−1, E−3, F−2`) is recorded.

  The general manifold-preservation theorem would need a full link/star proof
  over oriented meshes; following the §4.0 budget it is *not* claimed here.
  Instead `collapse_watertight_fin4` verifies it exhaustively on all 256 face
  subsets of a tetrahedron's eight oriented triangles, and the C API checks
  the output mesh's edge closure before returning. The general claim is an
  explicit boundary in VERIFICATION.md.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.PhysMesh

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

namespace EdgeCollapse

variable {ι V : Type} [DecidableEq ι]

/-- Retarget every occurrence of `b` to `a`. -/
def retargetTri (a b : ι) (t : TriIdx ι) : TriIdx ι :=
  ⟨if t.a = b then a else t.a,
   if t.b = b then a else t.b,
   if t.c = b then a else t.c⟩

theorem retargetTri_id_of_not_mem {a b : ι} {t : TriIdx ι}
    (h : b ∉ ({t.a, t.b, t.c} : Finset ι)) : retargetTri a b t = t := by
  rcases t with ⟨x, y, z⟩
  simp at h
  have hx : x ≠ b := by intro hx; exact h.1 hx.symm
  have hy : y ≠ b := by intro hy; exact h.2.1 hy.symm
  have hz : z ≠ b := by intro hz; exact h.2.2 hz.symm
  simp [retargetTri, hx, hy, hz]

def nondegenerate (t : TriIdx ι) : Prop := t.a ≠ t.b ∧ t.b ≠ t.c ∧ t.a ≠ t.c

/-- Bool twin of `nondegenerate`, used by `List.filter`. -/
def nondegenerateB (t : TriIdx ι) : Bool := t.a != t.b && t.b != t.c && t.a != t.c

theorem nondegenerateB_eq_true {t : TriIdx ι} : nondegenerateB t = true ↔ nondegenerate t := by
  constructor <;> intro h <;>
    simp [nondegenerateB, nondegenerate, beq_iff_eq] at h ⊢ <;> tauto

/-- Collapse `b` onto `a`, placing the surviving vertex at `v`, and drop the
    faces that become degenerate. -/
def collapse (m : PhysMesh ι V) (a b : ι) (v : V) : PhysMesh ι V :=
  { pos := fun x => if x = b then v else m.pos x,
    faces := (m.faces.map (retargetTri a b)).filter nondegenerateB }

@[simp] theorem collapse_pos_b (m : PhysMesh ι V) (a b : ι) (v : V) :
    (collapse m a b v).pos b = v := by simp [collapse]

@[simp] theorem collapse_pos_ne (m : PhysMesh ι V) (a b x : ι) (v : V)
    (hx : x ≠ b) : (collapse m a b v).pos x = m.pos x := by simp [collapse, hx]

theorem map_filter_length_le (l : List α) (f : α → β) (p : β → Bool) :
    ((l.map f).filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.filter_cons]
      split
      · exact Nat.succ_le_succ ih
      · exact Nat.le_trans ih (Nat.le_succ xs.length)

theorem collapse_faces_length_le (m : PhysMesh ι V) (a b : ι) (v : V) :
    (collapse m a b v).faces.length ≤ m.faces.length := by
  exact map_filter_length_le m.faces (retargetTri a b) nondegenerateB

/-- If `b` is used by no face, collapsing it leaves the face list unchanged
    (provided the input faces are nondegenerate) and therefore preserves the
    directed-edge closure. -/
theorem map_filter_eq_self_of_not_mem {a b : ι} (l : List (TriIdx ι))
    (h : ∀ t ∈ l, b ∉ ({t.a, t.b, t.c} : Finset ι))
    (hndeg : ∀ t ∈ l, nondegenerate t) :
    (l.map (retargetTri a b)).filter nondegenerateB = l := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
      have ht_eq : retargetTri a b t = t := retargetTri_id_of_not_mem (h t (by simp))
      have htB : nondegenerateB t = true := nondegenerateB_eq_true.mpr (hndeg t (by simp))
      simp only [List.map_cons, List.filter_cons, ht_eq, htB, ite_true]
      congr 1
      exact ih (by intro u hu; exact h u (by simp [hu]))
        (by intro u hu; exact hndeg u (by simp [hu]))

theorem collapse_faces_eq_of_not_mem (m : PhysMesh ι V) (a b : ι) (v : V)
    (h : ∀ t ∈ m.faces, b ∉ ({t.a, t.b, t.c} : Finset ι))
    (hndeg : ∀ t ∈ m.faces, nondegenerate t) :
    (collapse m a b v).faces = m.faces := by
  exact map_filter_eq_self_of_not_mem m.faces h hndeg

theorem collapse_watertight_of_not_mem (m : PhysMesh ι V) (a b : ι) (v : V)
    (h : ∀ t ∈ m.faces, b ∉ ({t.a, t.b, t.c} : Finset ι))
    (hndeg : ∀ t ∈ m.faces, nondegenerate t)
    (hw : m.Watertight) : (collapse m a b v).Watertight := by
  simpa [PhysMesh.Watertight, PhysMesh.edges,
    collapse_faces_eq_of_not_mem m a b v h hndeg] using hw

/-! ### Link condition and counts -/

/-- The neighbours of a vertex in the directed edge list. -/
def neighbors (es : List (ι × ι)) (a : ι) : Finset ι :=
  ((es.filter fun e => e.1 = a).map Prod.snd).toFinset ∪
    ((es.filter fun e => e.2 = a).map Prod.fst).toFinset

/-- The common neighbours of `a` and `b` other than themselves. -/
def linkSet (m : PhysMesh ι V) (a b : ι) : Finset ι :=
  (neighbors m.edges a ∩ neighbors m.edges b) \ {a, b}

/-- C's safe-collapse criterion: the edge's two incident faces contribute
    exactly two common neighbours. -/
def LinkCondition (m : PhysMesh ι V) (a b : ι) : Prop :=
  a ≠ b ∧ (linkSet m a b).card = 2

/-- Euler arithmetic of an interior collapse. Stated separately so that the
    combinatorial proof of the three counts can be developed independently. -/
theorem euler_preserved_of_counts {V₀ E₀ F₀ V₁ E₁ F₁ : ℕ}
    (hv : V₁ + 1 = V₀) (he : E₁ + 3 = E₀) (hf : F₁ + 2 = F₀) :
    (V₁ : ℤ) - E₁ + F₁ = (V₀ : ℤ) - E₀ + F₀ := by
  omega

/-! ### Bounded manifold-preservation evidence -/

/-- The eight oriented triangles of a tetrahedron on `Fin 4`. -/
def tetraFaces4 : List (TriIdx (Fin 4)) :=
  [⟨0, 1, 2⟩, ⟨0, 2, 1⟩, ⟨0, 1, 3⟩, ⟨0, 3, 1⟩,
   ⟨0, 2, 3⟩, ⟨0, 3, 2⟩, ⟨1, 2, 3⟩, ⟨1, 3, 2⟩]

/-- Mesh from an arbitrary face list (positions are irrelevant for closure). -/
def tetraMesh4 (fs : List (TriIdx (Fin 4))) : PhysMesh (Fin 4) (Fin 3) :=
  ⟨fun _ => 0, fs⟩

/-- **Bounded manifold preservation.** For every submesh of the tetrahedron's
    oriented faces that is closed, duplicate-free and satisfies the link
    condition on edge `(0,1)`, the collapse is still watertight. Machine-checked
    by `native_decide` over all 256 subsets. The general-n theorem is the
    documented topological boundary of this module. The finite check is a Bool
    so `native_decide` can enumerate it. -/
instance physMeshFin4WatertightDec (m : PhysMesh (Fin 4) (Fin 3)) :
    Decidable m.Watertight := by
  unfold PhysMesh.Watertight
  infer_instance

instance linkConditionFin4Dec (m : PhysMesh (Fin 4) (Fin 3)) (a b : Fin 4) :
    Decidable (LinkCondition m a b) := by
  unfold LinkCondition linkSet neighbors
  infer_instance

def checkTetraFace (fs : List (TriIdx (Fin 4))) : Bool :=
  decide ((tetraMesh4 fs).Watertight →
    (tetraMesh4 fs).edges.Nodup →
    LinkCondition (tetraMesh4 fs) 0 1 →
    (collapse (tetraMesh4 fs) 0 1 (0 : Fin 3)).Watertight)

def tetraCheck : Bool := tetraFaces4.sublists.all checkTetraFace

theorem tetraCheck_true : tetraCheck = true := by
  native_decide

theorem collapse_watertight_fin4 (fs : List (TriIdx (Fin 4)))
    (hsub : fs ∈ tetraFaces4.sublists)
    (hw : (tetraMesh4 fs).Watertight)
    (hnd : (tetraMesh4 fs).edges.Nodup)
    (hlink : LinkCondition (tetraMesh4 fs) 0 1) :
    (collapse (tetraMesh4 fs) 0 1 (0 : Fin 3)).Watertight := by
  have hall : checkTetraFace fs = true := (List.all_eq_true.mp tetraCheck_true) fs hsub
  have himp : (tetraMesh4 fs).Watertight →
      (tetraMesh4 fs).edges.Nodup →
      LinkCondition (tetraMesh4 fs) 0 1 →
      (collapse (tetraMesh4 fs) 0 1 (0 : Fin 3)).Watertight := by
    exact of_decide_eq_true hall
  exact himp hw hnd hlink

end EdgeCollapse
end Vdb
