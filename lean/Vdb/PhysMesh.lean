/-
  TinyVDB - Lean 4 formalization of the OpenVDB file format and volume operators.

  A shared index-mesh representation for the physics-processing track (collision
  proxies, convex parts, contact manifolds). Positions are kept as an abstract
  type `V` so that the combinatorial contracts (watertightness, looplessness,
  edge counts, Euler characteristic) are proved once and can be instantiated at
  exact `Q3` for executable twins and at `Point` for geometric statements.

  The key bridge is `watertight_triangulate`: triangulating every quad of an
  index-watertight quad mesh (`GlobalSurface.IxWatertight`) gives a watertight
  triangle mesh — the two internal diagonals cancel and each boundary edge is
  supplied by the neighbouring quad. This lets collision proxies produced by
  the DMC machinery be consumed by triangle-based narrowphase code.

  Non-self-intersection is deliberately a *hypothesis*, not a claim: proving it
  for a geometric embedding is out of scope, and the physics track states it
  explicitly wherever it is needed.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Data.Sym.Sym2
import Vdb.GlobalSurface
import Vdb.QuadEuler

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Vdb

/-- A triangle by vertex indices. -/
structure TriIdx (ι : Type) where
  a : ι
  b : ι
  c : ι
  deriving DecidableEq

namespace TriIdx

/-- The three directed edges of a triangle, in cyclic order. -/
def edges (t : TriIdx ι) : List (ι × ι) :=
  [(t.a, t.b), (t.b, t.c), (t.c, t.a)]

end TriIdx

/-- An index mesh: vertex positions plus a list of oriented triangles. -/
structure PhysMesh (ι V : Type) where
  pos : ι → V
  faces : List (TriIdx ι)

namespace PhysMesh

/-- All directed index edges of the mesh. -/
def edges (m : PhysMesh ι V) : List (ι × ι) :=
  m.faces.flatMap TriIdx.edges

/-- Combinatorial watertightness: every directed edge appears with its reverse.
    This is exactly `Assembly.EdgeClosed m.edges`. -/
def Watertight (m : PhysMesh ι V) : Prop :=
  ∀ i j : ι, (i, j) ∈ m.edges ↔ (j, i) ∈ m.edges

/-- No directed edge is a loop. -/
def Loopless (m : PhysMesh ι V) : Prop :=
  ∀ i j : ι, (i, j) ∈ m.edges → i ≠ j

/-- The undirected index edges (as `Sym2`), reusing the quad-mesh counting
    infrastructure; the lemma applies to triangles just as well. -/
abbrev undirected [DecidableEq ι] (m : PhysMesh ι V) : Finset (Sym2 ι) :=
  QuadEuler.undirected m.edges

/-- The tails of the directed edges: the vertices actually used by faces. -/
abbrev vertices [DecidableEq ι] (m : PhysMesh ι V) : Finset ι :=
  QuadEuler.vertices m.edges

/-! ### Elementary closure facts -/

theorem watertight_empty (pos : ι → V) :
    ({ pos := pos, faces := [] } : PhysMesh ι V).Watertight := by
  intro i j
  simp [Watertight, edges]

theorem watertight_append {m₁ m₂ : PhysMesh ι V}
    (h₁ : m₁.Watertight) (h₂ : m₂.Watertight) :
    ({ pos := m₁.pos, faces := m₁.faces ++ m₂.faces } : PhysMesh ι V).Watertight := by
  intro i j
  simp only [Watertight, edges, List.flatMap_append, List.mem_append] at h₁ h₂ ⊢
  constructor <;> intro h
  · rcases h with h | h
    · exact Or.inl ((h₁ i j).mp h)
    · exact Or.inr ((h₂ i j).mp h)
  · rcases h with h | h
    · exact Or.inl ((h₁ i j).mpr h)
    · exact Or.inr ((h₂ i j).mpr h)

theorem loopless_empty (pos : ι → V) :
    ({ pos := pos, faces := [] } : PhysMesh ι V).Loopless := by
  intro i j h
  simp [Loopless, edges] at h

/-! ### Counting for closed meshes -/

/-- The half-edge count for a closed, duplicate-free, loop-free triangle mesh. -/
theorem edges_card [DecidableEq ι] {m : PhysMesh ι V}
    (hnd : m.edges.Nodup) (hw : m.Watertight) (hl : m.Loopless) :
    2 * (m.undirected).card = m.edges.length :=
  QuadEuler.two_mul_card_undirected m.edges hnd hw hl

/-- **Euler relation for a closed triangle mesh.** With `F` faces and no
    repeated/looping edges, `2·χ = 2·V − F`. The half-integer form is avoided
    on purpose: `F` need not be even for the identity to be meaningful over ℤ. -/
theorem euler_triangle [DecidableEq ι] {m : PhysMesh ι V}
    (hnd : m.edges.Nodup) (hw : m.Watertight) (hl : m.Loopless)
    (F : ℕ) (hF : m.edges.length = 3 * F) :
    2 * (((m.vertices.card : ℤ) - (m.undirected.card : ℤ)) + F) =
      2 * (m.vertices.card : ℤ) - F := by
  have hE := QuadEuler.two_mul_card_undirected m.edges hnd hw hl
  have hE' : (2 * (m.undirected.card : ℤ) : ℤ) = m.edges.length := by exact_mod_cast hE
  have hF' : (m.edges.length : ℤ) = 3 * F := by exact_mod_cast hF
  omega

/-! ### Quad-to-triangle bridge -/

/-- Split a quad into the two triangles `(a,b,c)` and `(a,c,d)`. -/
def triangulate (qs : List (IxQuad ι)) : List (TriIdx ι) :=
  qs.flatMap fun q => [{ a := q.a, b := q.b, c := q.c }, { a := q.a, b := q.c, c := q.d }]

/-- Every edge of a quad occurs in one of its two triangles. -/
theorem quadEdge_mem_triangulate_edges {q : IxQuad ι} {i j : ι}
    (h : (i, j) ∈ q.edges) :
    (i, j) ∈ ({ a := q.a, b := q.b, c := q.c } : TriIdx ι).edges ∨
    (i, j) ∈ ({ a := q.a, b := q.c, c := q.d } : TriIdx ι).edges := by
  rcases q with ⟨a, b, c, d⟩
  simp [IxQuad.edges, TriIdx.edges] at h ⊢
  tauto

/-- Triangulating an index-watertight quad mesh yields a watertight triangle
    mesh. The internal diagonals `(a,c)` / `(c,a)` cancel within each quad, and
    every quad boundary edge is supplied by the adjacent quad. -/
theorem watertight_triangulate (qs : List (IxQuad ι)) (h : IxWatertight qs)
    (pos : ι → V) :
    ({ pos := pos, faces := triangulate qs } : PhysMesh ι V).Watertight := by
  let es := (triangulate qs).flatMap TriIdx.edges
  have step : ∀ {i j : ι}, (i, j) ∈ es → (j, i) ∈ es := by
    intro i j hij
    rcases List.mem_flatMap.mp hij with ⟨t, ht, hijt⟩
    rcases List.mem_flatMap.mp ht with ⟨q, hq, htmem⟩
    rcases q with ⟨a, b, c, d⟩
    simp only [triangulate, List.flatMap_cons, List.mem_cons, List.not_mem_nil, or_false] at htmem
    have quadEdge_step : ∀ {u v : ι},
        (u, v) ∈ ({ a := a, b := b, c := c, d := d } : IxQuad ι).edges → (v, u) ∈ es := by
      intro u v huv
      have huvS : (u, v) ∈ ixSurfaceEdges qs := by
        exact List.mem_flatMap.mpr ⟨⟨a, b, c, d⟩, hq, huv⟩
      have hvuS : (v, u) ∈ ixSurfaceEdges qs := (h u v).mp huvS
      rcases List.mem_flatMap.mp hvuS with ⟨q', hq', hvq'⟩
      rcases quadEdge_mem_triangulate_edges hvq' with htri | htri
      · exact List.mem_flatMap.mpr
          ⟨{ a := q'.a, b := q'.b, c := q'.c },
            List.mem_flatMap.mpr ⟨q', hq', by simp⟩, htri⟩
      · exact List.mem_flatMap.mpr
          ⟨{ a := q'.a, b := q'.c, c := q'.d },
            List.mem_flatMap.mpr ⟨q', hq', by simp⟩, htri⟩
    rcases htmem with rfl | rfl
    · simp only [TriIdx.edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hijt
      rcases hijt with hcase | hcase | hcase
      · rcases hcase with ⟨hi, hj⟩
        subst i; subst j
        exact quadEdge_step (by simp [IxQuad.edges])
      · rcases hcase with ⟨hi, hj⟩
        subst i; subst j
        exact quadEdge_step (by simp [IxQuad.edges])
      · -- the internal diagonal (c,a), answered by the second triangle
        rcases hcase with ⟨hi, hj⟩
        subst i; subst j
        exact List.mem_flatMap.mpr
          ⟨{ a := a, b := c, c := d }, List.mem_flatMap.mpr ⟨⟨a, b, c, d⟩, hq, by simp⟩,
            by simp [TriIdx.edges]⟩
    · simp only [TriIdx.edges, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hijt
      rcases hijt with hcase | hcase | hcase
      · -- the internal diagonal (a,c), answered by the first triangle
        rcases hcase with ⟨hi, hj⟩
        subst i; subst j
        exact List.mem_flatMap.mpr
          ⟨{ a := a, b := b, c := c }, List.mem_flatMap.mpr ⟨⟨a, b, c, d⟩, hq, by simp⟩,
            by simp [TriIdx.edges]⟩
      · rcases hcase with ⟨hi, hj⟩
        subst i; subst j
        exact quadEdge_step (by simp [IxQuad.edges])
      · rcases hcase with ⟨hi, hj⟩
        subst i; subst j
        exact quadEdge_step (by simp [IxQuad.edges])
  intro i j
  change (i, j) ∈ es ↔ (j, i) ∈ es
  constructor
  · exact step
  · intro hji
    exact step hji

end PhysMesh
end Vdb
