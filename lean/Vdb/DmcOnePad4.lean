/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  **DMC-1 (Nielson dual marching cubes) on the `n = 4` padded grid —
  a seeded sample (bounded evidence).**

  The exhaustive machine-check at `n = 3` (all 256 shell-pinned sign
  fields) is in `Vdb/DmcOnePad.lean` and `Vdb/DmcOneDual.lean`. At
  `n = 4` the interior is `3^3 = 27` points, so exhaustive enumeration
  is `2^27` fields — infeasible. This module instead machine-checks a
  **curated sample** of dense and structured sign fields, verifying the
  same invariants the exhaustive `n = 3` check covers:

  * the 27 **single-point** fields (`2^k`, one interior point each);
  * eight **seeded fields** exercising sparse, dense and mixed
    patterns: `[3, 77, 424242, 3735928559, 4294967295, 267452175,
    4042322160, 305419896]`;
  * the two-cluster field `2^0 + 2^26` (points `(1,1,1)` and `(3,3,3)`).

  Machine-checked facts:

  * **`fin4_sample_nodup`** / **`fin4_sample_edgeClosed`** /
    **`fin4_sample_loopless`** / **`fin4_sample_mesh_nodup`** —
    every sampled quad has four pairwise-distinct corners; the directed
    mesh edge list is `EdgeClosed` (watertight); no loops; no repeated
    directed edge;
  * **`fin4_sample_components`** — the soup and mesh component counts
    agree on every sampled field (the sample includes fields with 2
    and 3 components);
  * **`fin4_two_cluster_chi`** — the two-cluster field's
    `χ = V − F = 4` (two spheres).

  What is **not** claimed: exhaustive coverage of the `n = 4` family;
  arbitrary `n` (the bounded sample only; the general padded-grid
  DMC-1 theorem remains open and multi-week); any χ statement beyond
  the sample.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Assembly
import Vdb.DmcOne
import Vdb.DmcOneDual
import Vdb.DmcOnePad
import Vdb.McTable
import Vdb.PadGrid
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

open Vdb.McTable Vdb.DmcOnePad

namespace Vdb
namespace DmcOnePad4

abbrev Lat := Nat × Nat × Nat
abbrev Cell := Nat × Nat × Nat
abbrev PadEdge := Lat × Nat
abbrev V := DmcOnePad.V

/-- The interior sign field with index `k`: bit `j` of `k` is the sign at
    the `j`-th interior lattice point (lexicographic), bit 0 = `(1,1,1)`. -/
def fin4SignOf (k : Nat) (p : Lat) : Bool :=
  if p.1 == 0 || p.1 == 4 || p.2.1 == 0 || p.2.1 == 4 || p.2.2 == 0 || p.2.2 == 4 then false
  else
    let idx := (p.1 - 1) * 9 + (p.2.1 - 1) * 3 + (p.2.2 - 1)
    k / 2 ^ idx % 2 = 1

/-- The DMC-1 quad of a crossed lattice edge at `n = 4`. -/
def dmcOneQuad4 (s : Lat → Bool) (e : PadEdge) : List V :=
  if s e.1 == s (Vdb.PadGrid.succN e.1 e.2) then [] else
    match incidentCells s e with
    | [a, b, c, dd] =>
      [cellPatchVertex s a e.1 e.2, cellPatchVertex s b e.1 e.2,
       cellPatchVertex s c e.1 e.2, cellPatchVertex s dd e.1 e.2]
    | _ => []

/-- The quads of a sign field on the bounded `n = 4` padded grid. -/
def dmcOneQuads4 (s : Lat → Bool) : List (List V) :=
  (Vdb.PadGrid.latAll 4).flatMap fun p =>
    (List.range 3).filterMap fun d =>
      if decide (Vdb.PadGrid.InLattice 4 (Vdb.PadGrid.succN p d)) && (s p != s (Vdb.PadGrid.succN p d))
      then some (dmcOneQuad4 s (p, d))
      else none

/-- The directed edge list of the assembled DMC-1 mesh at `n = 4`. -/
def dmcOneMeshEdges4 (s : Lat → Bool) : List (V × V) :=
  (dmcOneQuads4 s).flatMap quadDirectedEdges

/-- The curated sample of dense and structured seeds. -/
def sampleSeeds : List Nat :=
  [3, 77, 424242, 3735928559, 4294967295, 267452175, 4042322160, 305419896]

/-! ### Machine-checked facts over the sample -/

theorem fin4_sample_nodup : ∀ seed ∈ sampleSeeds,
    (dmcOneQuads4 (fin4SignOf seed)).all quadNodup = true := by native_decide

theorem fin4_sample_edgeClosed : ∀ seed ∈ sampleSeeds,
    edgeClosedB (dmcOneMeshEdges4 (fin4SignOf seed)) = true := by native_decide

theorem fin4_sample_loopless : ∀ seed ∈ sampleSeeds,
    looplessB (dmcOneMeshEdges4 (fin4SignOf seed)) = true := by native_decide

theorem fin4_sample_mesh_nodup : ∀ seed ∈ sampleSeeds,
    (dmcOneMeshEdges4 (fin4SignOf seed)).Nodup := by native_decide

theorem fin4_sample_components : ∀ seed ∈ sampleSeeds,
    Vdb.DmcOneDual.meshComponents (dmcOneMeshEdges4 (fin4SignOf seed))
      = Vdb.DmcOneDual.soupComponents
          (Vdb.DmcOneDual.buildSoup 4 (fin4SignOf seed)) := by native_decide

/-- The 27 single-point fields: each is one sphere (χ = 2). -/
theorem fin4_singles_nodup : ∀ k ∈ List.range 27,
    (dmcOneQuads4 (fin4SignOf (2 ^ k))).all quadNodup = true := by native_decide

theorem fin4_singles_components : ∀ k ∈ List.range 27,
    Vdb.DmcOneDual.soupComponents (Vdb.DmcOneDual.buildSoup 4 (fin4SignOf (2 ^ k))) = 1 := by
  native_decide

/-- The two-cluster field (points `(1,1,1)` and `(3,3,3)`): all
    invariants, and `χ = V − F = 4` (two spheres). -/
theorem fin4_two_cluster_invariants :
    (dmcOneQuads4 (fin4SignOf (2 ^ 0 + 2 ^ 26))).all quadNodup = true ∧
    edgeClosedB (dmcOneMeshEdges4 (fin4SignOf (2 ^ 0 + 2 ^ 26))) = true ∧
    (dmcOneMeshEdges4 (fin4SignOf (2 ^ 0 + 2 ^ 26))).Nodup ∧
    Vdb.DmcOneDual.soupComponents (Vdb.DmcOneDual.buildSoup 4 (fin4SignOf (2 ^ 0 + 2 ^ 26))) = 2 := by
  native_decide

theorem fin4_two_cluster_chi :
    (Vdb.DmcOnePad.meshVerts (dmcOneMeshEdges4 (fin4SignOf (2 ^ 0 + 2 ^ 26)))).length
      - (dmcOneQuads4 (fin4SignOf (2 ^ 0 + 2 ^ 26))).length = 4 := by native_decide

end DmcOnePad4
end Vdb
