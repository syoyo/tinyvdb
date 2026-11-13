/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Global assembly of the dual (DMC) surface from primal incidence.

  The DMC construction produces one dual quad per crossed primal *edge*. The
  quad's four sides are dual edges through the four primal *faces* around that
  primal edge. The assembly criterion is therefore a per-face one: every
  crossed primal face must be traversed by its two incident crossed primal
  edges in opposite directions.

  This module models that directly. A `LabeledEdge` is a primal face plus the
  direction in which a quad walks the face's dual edge; `dirEdge` gives the
  concrete directed dual edge. A quad is a list of labeled edges, and an
  assembly is a list of quads. `Balanced` says every face occurs once in each
  direction, and `watertight_of_balanced` proves that the concrete surface is
  `Watertight`: the two uses of a face cancel.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Vdb.DualSurface
import Vdb.GlobalSurface

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

/-- One use of a primal face by a dual quad: the face and the direction in
    which the quad traverses the face's dual edge. -/
structure LabeledEdge (φ : Type) where
  face : φ
  forward : Bool
  deriving DecidableEq, Repr

/-- The concrete directed dual edge of a labeled edge. -/
def dirEdge {ι φ : Type} (ends : φ → ι × ι) (e : LabeledEdge φ) : ι × ι :=
  if e.forward then ends e.face else ((ends e.face).2, (ends e.face).1)

theorem dirEdge_true {ι φ : Type} (ends : φ → ι × ι) (f : φ) :
    dirEdge ends ⟨f, true⟩ = ends f := by
  simp [dirEdge]

theorem dirEdge_false {ι φ : Type} (ends : φ → ι × ι) (f : φ) :
    dirEdge ends ⟨f, false⟩ = ((ends f).2, (ends f).1) := by
  simp [dirEdge]

/-- Walking a face in the opposite direction gives the reverse dual edge. -/
theorem dirEdge_swap {ι φ : Type} (ends : φ → ι × ι) {f : φ} {a b : ι}
    (h : dirEdge ends ⟨f, true⟩ = (a, b)) :
    dirEdge ends ⟨f, false⟩ = (b, a) := by
  rw [dirEdge_true] at h
  rw [dirEdge_false, h]

theorem dirEdge_swap' {ι φ : Type} (ends : φ → ι × ι) {f : φ} {a b : ι}
    (h : dirEdge ends ⟨f, false⟩ = (a, b)) :
    dirEdge ends ⟨f, true⟩ = (b, a) := by
  rw [dirEdge_false] at h
  have h' : ((ends f).2, (ends f).1) = (a, b) := h
  have h1 : (ends f).2 = a := congrArg Prod.fst h'
  have h2 : (ends f).1 = b := congrArg Prod.snd h'
  rw [dirEdge_true]
  exact Prod.ext h2 h1

/-- The concrete directed dual surface of an assembly of labeled quads. -/
def asmSurface {ι φ : Type} (ends : φ → ι × ι)
    (qs : List (List (LabeledEdge φ))) : List (ι × ι) :=
  qs.flatMap (fun q => q.map (dirEdge ends))

/-- A directed edge list is closed when each edge appears with its reverse. -/
def EdgeClosed {ι : Type} (es : List (ι × ι)) : Prop :=
  ∀ a b : ι, (a, b) ∈ es ↔ (b, a) ∈ es

/-- The flat list of face uses of an assembly. -/
def faceUses {φ : Type} (qs : List (List (LabeledEdge φ))) : List (LabeledEdge φ) :=
  qs.flatMap id

/-- **The DMC assembly criterion**: every primal face is used equally often
    in the two directions. -/
def Balanced {φ : Type} [DecidableEq φ] (qs : List (List (LabeledEdge φ))) : Prop :=
  ∀ f : φ, (faceUses qs).count ⟨f, true⟩ = (faceUses qs).count ⟨f, false⟩

theorem mem_asmSurface {ι φ : Type} {ends : φ → ι × ι}
    {qs : List (List (LabeledEdge φ))} {a b : ι} :
    (a, b) ∈ asmSurface ends qs ↔
      ∃ q ∈ qs, ∃ e ∈ q, dirEdge ends e = (a, b) := by
  simp only [asmSurface, List.mem_flatMap, List.mem_map]

/-- If a face is used in one direction, its balance gives a use in the other,
    and the two concrete edges are reverses. -/
theorem reverse_mem_of_mem {ι φ : Type} [DecidableEq φ] {ends : φ → ι × ι}
    {qs : List (List (LabeledEdge φ))} (hbal : Balanced qs) :
    ∀ {a b : ι}, (a, b) ∈ asmSurface ends qs → (b, a) ∈ asmSurface ends qs := by
  intro a b hab
  obtain ⟨q, hq, e, he, hdir⟩ := mem_asmSurface.mp hab
  obtain ⟨f, σ⟩ := e
  cases σ
  · -- the quad walks the face backwards
    have hm : (⟨f, false⟩ : LabeledEdge φ) ∈ faceUses qs :=
      List.mem_flatMap.mpr ⟨q, hq, he⟩
    have hpos : 0 < (faceUses qs).count ⟨f, true⟩ := by
      rw [hbal f]
      exact List.count_pos_iff.mpr hm
    obtain ⟨q', hq', he'⟩ := List.mem_flatMap.mp (List.count_pos_iff.mp hpos)
    exact mem_asmSurface.mpr ⟨q', hq', ⟨f, true⟩, he', dirEdge_swap' ends hdir⟩
  · -- the quad walks the face forwards
    have hm : (⟨f, true⟩ : LabeledEdge φ) ∈ faceUses qs :=
      List.mem_flatMap.mpr ⟨q, hq, he⟩
    have hpos : 0 < (faceUses qs).count ⟨f, false⟩ := by
      rw [← hbal f]
      exact List.count_pos_iff.mpr hm
    obtain ⟨q', hq', he'⟩ := List.mem_flatMap.mp (List.count_pos_iff.mp hpos)
    exact mem_asmSurface.mpr ⟨q', hq', ⟨f, false⟩, he', dirEdge_swap ends hdir⟩

/-- **Global dual-surface watertightness from primal incidence**: if every
    crossed primal face is used once in each direction, the assembled dual
    quads form a watertight surface. -/
theorem watertight_of_balanced {ι φ : Type} [DecidableEq φ] {ends : φ → ι × ι}
    {qs : List (List (LabeledEdge φ))} (hbal : Balanced qs) :
    EdgeClosed (asmSurface ends qs) := by
  intro a b
  exact ⟨reverse_mem_of_mem hbal, reverse_mem_of_mem hbal⟩

/-- Bridge to the concrete quad surface: if an index-quad complex has exactly
    the assembled edge set, its concrete placement is watertight. -/
theorem watertight_concrete_of_edges {ι : Type} {qs : List (IxQuad ι)}
    (h : EdgeClosed (ixSurfaceEdges qs)) (V : ι → Point) :
    Watertight (qs.map (IxQuad.map V)) :=
  watertight_of_ix (by simpa [IxWatertight, EdgeClosed] using h) V

/-- The crossed-edge/face stencil complex of a grid: for every crossed primal
    edge, the four labeled faces around it. -/
structure StencilComplex (ι φ ε : Type) where
  /-- The two cubes adjacent to each primal face. -/
  ends : φ → ι × ι
  /-- The labeled faces around each crossed primal edge. -/
  edgeFaces : ε → List (LabeledEdge φ)
  /-- The crossed primal edges. -/
  crossedEdges : List ε

namespace StencilComplex

def quads (S : StencilComplex ι φ ε) : List (List (LabeledEdge φ)) :=
  S.crossedEdges.map S.edgeFaces

def mesh (S : StencilComplex ι φ ε) : List (ι × ι) :=
  asmSurface S.ends S.quads

/-- The assembly criterion in stencil form. -/
def Balanced [DecidableEq φ] (S : StencilComplex ι φ ε) : Prop :=
  Vdb.Balanced S.quads

/-- **The assembled DMC surface is watertight** when each primal face is used
    in both directions. -/
theorem watertight [DecidableEq φ] (S : StencilComplex ι φ ε) (h : S.Balanced) :
    EdgeClosed S.mesh :=
  Vdb.watertight_of_balanced h

end StencilComplex


/-! ### Concrete balanced assemblies -/

/-- A four-quad belt: quad `i` walks face `i` forwards and face `i-1`
    backwards, so every face is used once in each direction. -/
def beltQuads : List (List (LabeledEdge (Fin 4))) :=
  [ [⟨0, true⟩, ⟨3, false⟩],
    [⟨1, true⟩, ⟨0, false⟩],
    [⟨2, true⟩, ⟨1, false⟩],
    [⟨3, true⟩, ⟨2, false⟩] ]

theorem beltQuads_balanced : Balanced beltQuads := by
  unfold Balanced faceUses
  decide

theorem beltQuads_edgeClosed {ι : Type} (ends : Fin 4 → ι × ι) :
    EdgeClosed (asmSurface ends beltQuads) :=
  watertight_of_balanced beltQuads_balanced

/-- A directed edge list of a closed oriented surface has zero net displacement sum. -/
def flip (e : Point × Point) : Point × Point := (e.2, e.1)

def sumEdges (es : List (Point × Point)) : Point :=
  match es with
  | [] => 0
  | e :: t => (e.2 - e.1) + sumEdges t

theorem sumEdges_nil : sumEdges [] = 0 := rfl

theorem sumEdges_cons (a b : Point) (t : List (Point × Point)) :
    sumEdges ((a, b) :: t) = (b - a) + sumEdges t := rfl

theorem sumEdges_map_flip : ∀ (es : List (Point × Point)),
    sumEdges (es.map flip) = - sumEdges es := by
  intro es
  induction es with
  | nil => simp [sumEdges]
  | cons e t ih =>
      obtain ⟨a, b⟩ := e
      simp only [List.map_cons, sumEdges_cons, flip]
      rw [ih]
      calc
        (a - b : Point) + (- sumEdges t : Point)
            = (-(b - a : Point)) + (- sumEdges t) := by
                rw [neg_sub (a := b) (b := a)]
        _ = -((b - a : Point) + sumEdges t) := by rw [neg_add]

def ClosedSurface (es : List (Point × Point)) : Prop :=
  es = es.map flip

theorem sumEdges_eq_zero_of_closed {es : List (Point × Point)}
    (h : ClosedSurface es) : sumEdges es = 0 := by
  have h1 : sumEdges es = -sumEdges es := by
    conv_lhs => rw [h]
    rw [sumEdges_map_flip]
  have h2 : sumEdges es + sumEdges es = 0 := by
    nth_rewrite 2 [h1]
    exact add_neg_cancel _
  have h3 : (2 : ℝ) • (sumEdges es) = 0 := by
    rw [two_smul]
    exact h2
  exact (smul_eq_zero.mp h3).resolve_left (by norm_num)

end Vdb
