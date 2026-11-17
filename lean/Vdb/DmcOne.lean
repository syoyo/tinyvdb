/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **DMC-1 (Nielson dual marching cubes) — the local patch foundation,
  machine-checked over all 256 cases.**

  Nielson's dual marching cubes (`plan-lean.md` P3): per cube, one vertex
  **per MC patch** (a connected component of the cube's MC triangle soup);
  each MC vertex is then owned by its patches, and the DMC-1 mesh joins
  the patch-vertices around every crossed primal edge into a quad. This
  module lands the cube-local half of that construction on top of the
  shipped MC table machine-checked in `Vdb/McTable.lean`:

  * `usedVerts` — the edge ids used by a case's triangle soup;
  * `mcPatchCount k` — the number of connected components of the case's
    triangle soup (union-find over the used edges; empty soup ⇒ 0);
  * `mcTriPatch k t` — the patch index of each triangle;
  * `patchesUsing k e` — the (deduplicated) patches that use edge `e`,
    i.e. the cube-local corners the DMC-1 quad for `e` takes from this
    cell.

  Machine-checked facts (all `native_decide` over all 256 cases):

  * **`mcPatchCount_le_four`** — no case has more than 4 patches;
  * **`mcPatchCount_dist`** — the exact distribution over the 256 cases:
    2 cases with 0 patches (the two trivial all-uniform cases), 162 with
    1, 82 with 2, 8 with 3 (`[26, 37, 74, 82, 88, 133, 161, 164]`) and
    2 with 4 (`[90, 165]`);
  * **`patches_using_le_one`** — every cube edge belongs to **at most
    one** patch (the DMC-1 quad therefore takes at most one corner from
    any cell; the valence around a crossed edge is exactly the number of
    incident cells, as Nielson's construction requires);
  * **`patches_using_eq_one_of_sign_change`** — every sign-change edge of
    a case is used by exactly one patch (from
    `McTable.everySignChangeEdgeUsed` + `patches_using_le_one`);
  * **`triPatch_count_eq`** — the number of distinct triangle patch ids
    equals `mcPatchCount` (the union-find rank assignment is consistent);
  * **`mcPatchCount_pos_iff_crossed`** — a case has a nontrivial patch
    iff it has a sign-change edge.

  What is **not** claimed: the general padded-grid DMC-1 manifold theorem
  (`T-DMC1-MANIFOLD` — patch decomposition and quad stitching across the
  padded lattice, with shell-pinned boundary; the multi-week padded-grid
  model that DMC-1 needs and the 2×2×2 `Fin 2` torus cannot host) and the
  DMC duality (`T-DMC1-DUAL` — bijection between MC triangle patches and
  DMC vertices, MC vertices and DMC quads, χ equal). The cube-local
  machinery here is what those theorems consume; the global stitching
  remains open, as recorded in `lean/VERIFICATION.md`.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.McTable

open Vdb Vdb.McTable

set_option linter.unusedSectionVars false

namespace Vdb

/-! ### Union-find over the 12 cube edges -/

/-- Union-find parent array, one slot per cube edge id. -/
def ufInit : Array Nat := Array.ofFn (fun (i : Fin 12) => i.1)

/-- Union-find root with a fixed iteration cap (12 edges; no recursion). -/
def ufFind (parent : Array Nat) (x : Nat) : Nat := Id.run do
  let mut y := x
  for _ in List.range (parent.size + 1) do
    let p := parent.getD y y
    if p = y then break
    y := p
  return y

/-- Union by attaching the root of `x` to the root of `y`. -/
def ufUnion (parent : Array Nat) (x y : Nat) : Array Nat :=
  let px := ufFind parent x
  let py := ufFind parent y
  if px = py then parent
  else parent.set! px py

/-- Merge the three vertices of one triangle into one component. -/
def ufStep (parent : Array Nat) (t : Nat × Nat × Nat) : Array Nat :=
  let (a, b, c) := t
  ufUnion (ufUnion parent a b) b c

/-! ### Patches of the MC triangle soup of a case -/

/-- The edge ids used by a case's triangle soup (deduplicated). -/
def usedVerts (tris : List (Nat × Nat × Nat)) : List Nat :=
  (tris.foldr (fun (a, b, c) acc => a :: b :: c :: acc) []).eraseDups

/-- The number of connected components of the case's triangle soup (at
    most 12; the edge ids are `0..11`). Empty soup ⇒ 0. -/
def mcPatchCount (k : Nat) : Nat :=
  let tris := trisOf k
  let verts := usedVerts tris
  if verts.isEmpty then 0 else
    let parent := tris.foldl ufStep ufInit
    verts.countP (fun i => ufFind parent i == i)

/-- The patch id of each triangle of the case (rank of the triangle's
    root among the used-vertex roots). -/
def mcTriPatch (k : Nat) : Array Nat :=
  let tris := trisOf k |>.toArray
  let parent := tris.foldl ufStep ufInit
  let verts := usedVerts (tris.toList)
  let roots := verts.filter (fun i => ufFind parent i == i)
  tris.map (fun (a, _, _) => roots.findIdx (· == ufFind parent a))

/-- The (deduplicated) patches using edge `e`. In the DMC-1 mesh this is
    the set of patch-vertices that own `e` inside this cube — the corners
    the DMC-1 quad for `e` takes from this cell. -/
def patchesUsing (k : Nat) (e : Nat) : List Nat :=
  let tris := trisOf k
  let parent := tris.foldl ufStep ufInit
  let verts := usedVerts tris
  let roots := verts.filter (fun i => ufFind parent i == i)
  let used := tris.filter (fun (a, b, c) => a == e || b == e || c == e)
  (used.map (fun (a, _, _) => roots.findIdx (· == ufFind parent a))).eraseDups

/-! ### Machine-checked facts, all 256 cases -/

theorem mcPatchCount_le_four : ∀ k : Fin 256, mcPatchCount k.val ≤ 4 := by native_decide

/-- The exact patch-count distribution over the 256 cases:
    (0-patch, 1-patch, 2-patch, 3-patch, ≥4-patch) = (2, 162, 82, 8, 2). -/
theorem mcPatchCount_dist :
    (((List.range 256).filter (fun k => mcPatchCount k == 0)).length,
     ((List.range 256).filter (fun k => mcPatchCount k == 1)).length,
     ((List.range 256).filter (fun k => mcPatchCount k == 2)).length,
     ((List.range 256).filter (fun k => mcPatchCount k == 3)).length,
     ((List.range 256).filter (fun k => mcPatchCount k ≥ 4)).length)
    = (2, 162, 82, 8, 2) := by native_decide

/-- The eight 3-patch cases. -/
theorem mcPatchCount_three_cases :
    (List.range 256).filter (fun k => mcPatchCount k == 3)
      = [26, 37, 74, 82, 88, 133, 161, 164] := by native_decide

/-- The two 4-patch cases. -/
theorem mcPatchCount_four_cases :
    (List.range 256).filter (fun k => mcPatchCount k == 4)
      = [90, 165] := by native_decide

/-- **Every cube edge belongs to at most one patch** of the case — the
    cube-local valence bound the DMC-1 quad construction needs (at most
    one corner per cell around a crossed edge). -/
theorem patches_using_le_one : ∀ k : Fin 256, ∀ e : Fin 12,
    (patchesUsing k.val e.val).length ≤ 1 := by native_decide

/-- Every sign-change edge of a case is used by exactly one patch (from
    `McTable.everySignChangeEdgeUsed` + `patches_using_le_one`). -/
theorem patches_using_eq_one_of_sign_change : ∀ k : Fin 256, ∀ e : Fin 12,
    (signChangeEdges k.val).contains e.val → (patchesUsing k.val e.val).length = 1 := by
  native_decide

/-- Consistency of the union-find rank assignment: the number of distinct
    patch ids equals `mcPatchCount`. -/
theorem triPatch_count_eq : ∀ k : Fin 256,
    (mcTriPatch k.val).toList.eraseDups.length = mcPatchCount k.val := by native_decide

/-- A case has a nontrivial patch iff it has a sign-change edge. -/
theorem mcPatchCount_pos_iff_crossed : ∀ k : Fin 256,
    0 < mcPatchCount k ↔ signChangeEdges k ≠ [] := by native_decide

end Vdb
