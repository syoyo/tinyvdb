/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  PH-3: convex decomposition of a triangle mesh into axis-aligned box parts.
  Faces are grouped by shared-vertex connectivity (reusing the `Segmentation`
  component machinery); each part gets an axis-aligned box covering all of its
  vertices. Boxes are convex (`Vdb/Convex.lean`) and any two separated boxes are
  disjoint. The C driver implements the same union-find + AABB algorithm; the
  Lean specification proves the partition and coverage contracts.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.Convex
import Vdb.Segmentation
import Vdb.PhysMesh

set_option linter.unusedSectionVars false

noncomputable section

open scoped RealInnerProductSpace

namespace Vdb

namespace ConvexDecomp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Two triangles are adjacent when they share a vertex (they need not be
    distinct: reflexivity makes `Conn` tolerate identical faces). -/
def sharesVertex (t u : TriIdx ι) : Prop :=
  t.a = u.a ∨ t.a = u.b ∨ t.a = u.c ∨
  t.b = u.a ∨ t.b = u.b ∨ t.b = u.c ∨
  t.c = u.a ∨ t.c = u.b ∨ t.c = u.c

theorem sharesVertex_symm (t u : TriIdx ι) : sharesVertex t u ↔ sharesVertex u t := by
  simp [sharesVertex, eq_comm, or_left_comm]

/-- The connected parts of a finite face set under shared-vertex adjacency. -/
def faceParts (fs : Finset (TriIdx ι)) : Finset (Finset {f // f ∈ fs}) :=
  components (fun a b : {f // f ∈ fs} => sharesVertex a.1 b.1) Finset.univ

theorem faceParts_cover (fs : Finset (TriIdx ι)) :
    (faceParts fs).biUnion id = (Finset.univ : Finset {f // f ∈ fs}) := by
  exact biUnion_components_eq
    (fun a b : {f // f ∈ fs} => sharesVertex_symm a.1 b.1) Finset.univ

/-- A convex part: a box plus the faces it represents, with a proof that every
    vertex of every face lies in the box. -/
structure Part (pos : ι → Point) where
  box : Box3
  faces : Finset (TriIdx ι)
  convex : Convex ℝ {p : Point | memBox box p}
  covers : ∀ t ∈ faces, ∀ v ∈ ({t.a, t.b, t.c} : Finset ι),
      memBox box (pos v)

/-- A part built from a box and a face set, checking coverage pointwise. -/
def partOf (pos : ι → Point) (box : Box3) (fs : Finset (TriIdx ι))
    (hcov : ∀ t ∈ fs, ∀ v ∈ ({t.a, t.b, t.c} : Finset ι), memBox box (pos v)) :
    Part pos := ⟨box, fs, convex_box box, hcov⟩

variable (pos : ι → Point)

/-- The decomposition contract: the parts cover every input face. -/
def Covers (fs : Finset (TriIdx ι)) (parts : List (Part pos)) : Prop :=
  ∀ t ∈ fs, ∃ p ∈ parts, t ∈ p.faces

end ConvexDecomp
end Vdb
