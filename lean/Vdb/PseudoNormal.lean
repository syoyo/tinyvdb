/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  The unweighted vertex pseudo-normal sign rule is unsound,
  even for convex polyhedra (F16).

  Motivation: `mesh_pseudo_normal` in `src/tinyvdb_mesh_conversion.inl`
  (the F11 fix) computes the inside/outside test sign from the closest
  feature with an **unweighted sum of the unit face normals** incident on
  that feature (vertex: all incident faces; edge: the two edge faces; face
  interior: the face normal itself), and `mesh_fill_rows` maps a negative
  dot product to "inside". This module machine-checks a counterexample at
  a **vertex** feature of a pointed, bounded, convex tetrahedron:

  * `p = t·(1, 0, 0)` (`t > 0`) lies outside the tetrahedron (it violates
    the first face's half-space);
  * the apex `q = (0, 0, 0)` is its closest point (proved by a direct
    inequality: every feasible point has `x ≤ 0`, so `|p − v| ≥ t`);
  * the faces tight at `q` — exactly the vertex figure of the apex —
    have outward unit normals
    `n₁ = (1, 0, 0)`, `n₂ = (−2/3, 2/3, 1/3)`, `n₃ = (−2/3, −2/3, 1/3)`
    (all unit vectors, rational coordinates);
  * the unweighted pseudo-normal `ν = n₁ + n₂ + n₃ = (−1/3, 0, 2/3)`
    pairs negatively: `⟨ν, p − q⟩ = −t/3 < 0`.

  So the unweighted rule classifies an outside point as inside — even on a
  convex, closed, oriented mesh. The tetrahedron is concrete: apex at the
  origin and base triangle `z = -1` with corners `(0, 1/2, -1)`,
  `(0, -1/2, -1)`, `(-1/2, 0, -1)`.

  What this does **not** show: failure at *edge* features (there the
  unweighted sum pairs non-negatively under the closest-point cone
  characterization — the elementary half of that pairing identity is the
  `edge_pairing_*` lemmas below; the cone characterization itself is not
  formalised), failure at face-interior features (trivially sound), any
  statement about the BVH path, and anything about angle-weighted
  (Bærentzen–Aanæs) pseudo-normals — those weights depend on face corner
  angles, not just normals, and are not modelled here. The C sign test
  remains sound at face-interior features unconditionally and at edge
  features for convex polyhedra; the vertex case needs angle weights or an
  additional fallback to be safe in general.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.WindingNumber

namespace Vdb

/-! ### Rational unit normals of the three tight (side) faces -/

/-- Outward unit normal of side face 1 (`x ≤ 0` half-space). -/
def pnN1 : V3 := ⟨1, 0, 0⟩

/-- Outward unit normal of side face 2 (`-2x + 2y + z = 0` half-space). -/
noncomputable def pnN2 : V3 := ⟨-2 / 3, 2 / 3, 1 / 3⟩

/-- Outward unit normal of side face 3 (`-2x - 2y + z = 0` half-space). -/
noncomputable def pnN3 : V3 := ⟨-2 / 3, -2 / 3, 1 / 3⟩

theorem pnN1_unit : V3.dot pnN1 pnN1 = 1 := by norm_num [pnN1, V3.dot]
theorem pnN2_unit : V3.dot pnN2 pnN2 = 1 := by norm_num [pnN2, V3.dot]
theorem pnN3_unit : V3.dot pnN3 pnN3 = 1 := by norm_num [pnN3, V3.dot]

/-! ### The tetrahedron as a half-space intersection

`inTetra` is the closed polyhedron: the three side half-spaces (all tight
at the apex `0`) together with the base slab `z ≥ -1`. It is bounded with
nonempty interior — a genuine convex triangle mesh (a tetrahedron). -/

/-- Membership in the tetrahedron: all four half-spaces satisfied. -/
def inTetra (v : V3) : Prop :=
  V3.dot pnN1 v ≤ 0 ∧ V3.dot pnN2 v ≤ 0 ∧ V3.dot pnN3 v ≤ 0 ∧ -1 ≤ v.z

theorem tetra_apex_mem : inTetra ⟨0, 0, 0⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [inTetra, pnN1, pnN2, pnN3, V3.dot]

/-- The interior is nonempty, e.g. `(-1/4, 0, -3/4)` is strictly inside. -/
theorem tetra_interior_witness :
    V3.dot pnN1 ⟨-1/4, 0, -3/4⟩ < 0 ∧
    V3.dot pnN2 ⟨-1/4, 0, -3/4⟩ < 0 ∧
    V3.dot pnN3 ⟨-1/4, 0, -3/4⟩ < 0 ∧
    -1 < (-3/4 : ℝ) := by
  norm_num [pnN1, pnN2, pnN3, V3.dot]

/-! ### The outside point and its closest point

`p = (t, 0, 0)`, `t > 0`. It violates side face 1, so it is outside.
The squared distance from `p` to any feasible `v` is at least `t²`,
because every feasible `v` has `x ≤ 0`. The apex attains it. -/

/-- The outside point on the axis of face 1's outward normal. -/
def pnP (t : ℝ) : V3 := ⟨t, 0, 0⟩

theorem tetra_outside {t : ℝ} (ht : 0 < t) : ¬ inTetra (pnP t) := by
  intro h
  have hx := h.1
  norm_num [pnP, pnN1, V3.dot] at hx
  linarith

/-- The apex (the vertex feature whose incident faces are exactly faces
    1, 2, 3) is the closest point of the tetrahedron to `p`. -/
theorem tetra_closest_point {t : ℝ} (ht : 0 < t) :
    ∀ v, inTetra v → t ^ 2 ≤ (v.x - t) ^ 2 + v.y ^ 2 + v.z ^ 2 := by
  intro v hv
  have hx : v.x ≤ 0 := by
    have h := hv.1
    simpa [pnN1, V3.dot] using h
  have hdiff : 0 ≤ v.x ^ 2 - 2 * t * v.x := by
    have h2 : (0:ℝ) ≤ (-v.x) * (2 * t - v.x) :=
      mul_nonneg (neg_nonneg.mpr hx) (by linarith [ht, hx])
    nlinarith [h2]
  have hsq : t ^ 2 ≤ (t - v.x) ^ 2 := by nlinarith [hdiff]
  have he : (v.x - t) ^ 2 = (t - v.x) ^ 2 := by ring
  have hy := sq_nonneg v.y
  have hz := sq_nonneg v.z
  linarith [hsq, hy, hz, he]

/-- The three side faces are exactly the faces tight at the apex
    (the apex vertex figure), and the base is not tight there. -/
theorem tetra_apex_tight :
    V3.dot pnN1 ⟨0, 0, 0⟩ = 0 ∧
    V3.dot pnN2 ⟨0, 0, 0⟩ = 0 ∧
    V3.dot pnN3 ⟨0, 0, 0⟩ = 0 ∧
    -1 ≠ (0 : ℝ) := by
  norm_num [pnN1, pnN2, pnN3, V3.dot]

/-! ### The unweighted vertex pseudo-normal and its failure

`mesh_pseudo_normal` at a vertex feature sums the unit normals of the
incident faces. Here that sum is `ν = (−1/3, 0, 2/3)` and it pairs
*negatively* with `p − q`, so the C sign test
(`direction >= 0.0f ? 1 : -1`) classifies the outside point as inside. -/

/-- The unweighted vertex pseudo-normal at the apex. -/
noncomputable def pnNu : V3 := V3.add (V3.add pnN1 pnN2) pnN3

theorem pnNu_eq : pnNu = ⟨-1/3, 0, 2/3⟩ := by
  norm_num [pnNu, pnN1, pnN2, pnN3, V3.add]

theorem pnNu_dot_pnN1 : V3.dot pnNu pnN1 = -1/3 := by
  norm_num [pnNu, pnN1, pnN2, pnN3, V3.add, V3.dot]

/-- The main counterexample: at the apex vertex of a convex, closed,
    oriented tetrahedron, an outside point whose closest point is the
    vertex has a negative unweighted pseudo-normal pairing. -/
theorem unweighted_vertex_pseudo_normal_misclassifies {t : ℝ} (ht : 0 < t) :
    ¬ inTetra (pnP t) ∧                                     -- `p` is outside
    inTetra ⟨0, 0, 0⟩ ∧                                     -- the apex is in the solid
    (∀ v, inTetra v → t ^ 2 ≤ (v.x - t) ^ 2 + v.y ^ 2 + v.z ^ 2) ∧  -- apex is closest
    V3.dot pnNu (V3.sub (pnP t) ⟨0, 0, 0⟩) = -t / 3 := by    -- pseudo-normal pairs negatively
  refine ⟨tetra_outside ht, tetra_apex_mem, tetra_closest_point ht, ?_⟩
  norm_num [pnNu, pnP, pnN1, pnN2, pnN3, V3.add, V3.sub, V3.dot]
  ring

/-! ### Elementary edge-feature pairing identity

For an edge feature the normal cone is generated by the two incident
face normals `nₐ, n_b` (the dihedral angle is `< π`, i.e. `nₐ + n_b ≠ 0`),
and a closest-point direction has the form `λₐ • nₐ + λ_b • n_b` with
`λₐ, λ_b ≥ 0`. The pairing with the unweighted sum then factors:
`⟨nₐ + n_b, λₐ nₐ + λ_b n_b⟩ = (λₐ + λ_b)(1 + ⟨nₐ, n_b⟩)`, which is
non-negative for unit normals. This is the elementary half of edge-feature
soundness; the closest-point cone characterization is *not* formalised. -/

/-- Scalar multiple of a `V3`. -/
def pnSmul (s : ℝ) (v : V3) : V3 := ⟨s * v.x, s * v.y, s * v.z⟩

theorem dot_self_nonneg (v : V3) : 0 ≤ V3.dot v v := by
  cases v with | mk x y z =>
  simp only [V3.dot]
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]

/-- The factoring identity for the edge pairing (for unit normals). -/
theorem edge_pairing_identity (na nb : V3) (la lb : ℝ)
    (hunitA : V3.dot na na = 1) (hunitB : V3.dot nb nb = 1) :
    V3.dot (V3.add na nb)
      (V3.add (pnSmul la na) (pnSmul lb nb)) =
      (la + lb) * (1 + V3.dot na nb) := by
  cases na; cases nb
  simp only [pnSmul, V3.add, V3.dot] at hunitA hunitB ⊢
  linear_combination la * hunitA + lb * hunitB

/-- For unit normals, the edge pairing is non-negative — the unweighted
    edge pseudo-normal cannot misclassify the way the vertex one does. -/
theorem edge_pairing_nonneg (na nb : V3) (la lb : ℝ)
    (hunitA : V3.dot na na = 1) (hunitB : V3.dot nb nb = 1)
    (hla : 0 ≤ la) (hlb : 0 ≤ lb) :
    0 ≤ V3.dot (V3.add na nb) (V3.add (pnSmul la na) (pnSmul lb nb)) := by
  have h2 : (0:ℝ) ≤ 1 + V3.dot na nb := by
    have hnn := dot_self_nonneg (V3.add na nb)
    cases na; cases nb
    simp only [V3.add, V3.dot] at hnn hunitA hunitB ⊢
    nlinarith [hnn, hunitA, hunitB]
  rw [edge_pairing_identity na nb la lb hunitA hunitB]
  exact mul_nonneg (add_nonneg hla hlb) h2

end Vdb
