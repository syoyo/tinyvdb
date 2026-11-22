/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format
  and the volume operators.

  BOUNDED DMC-1 TOPOLOGY differential twin (VS-3 / DMC-1 slice).
  Driven by `scripts/check_dmc1_topology.sh` against `scripts/dmc1_topology_c.c`,
  which calls the REAL `tvdb_sdf_to_mesh_dual_one_ex` on all 256 shell-pinned
  sign fields of the n = 3 padded grid and dumps one line per field:

    case <k> crossed <n> verts <v> quads <f> comps <c> closed <0|1> chi <int>

  Every field's six invariants are recomputed INDEPENDENTLY from the landed
  Lean model -- `Vdb.DmcOnePad` (fin3SignOf, crossed quads, mesh edges, mesh
  vertices, edgeClosedB), `Vdb.DmcOneEuler` (the assembled quads),
  `Vdb.DmcOneDual` (meshComponents), `Vdb.QuadEuler` (undirected edges) and
  `Vdb.PadGrid` (crossed edges) -- and compared with exact Nat/Int values.

  NOT mirrored (reported loudly in the `stages_unmirrored=` banner, never
  counted as a pass): C's vertex-index allocation/order, the QEF/centroid
  vertex positions, and the C patch-id allocation/order. The C patch
  decomposition, quad stitching, winding and edge enumeration ARE mirrored
  indirectly through the six topology invariants.

  Coverage: all 256 shell-pinned fields on the 4^3-sample (3^3-cell) lattice.
  No theorem is weakened; this is an executable differential check.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.DmcOneDual
import Vdb.DmcOneEuler
import Vdb.DmcOnePad
import Vdb.PadGrid
import Vdb.QuadEuler
import Mathlib.Tactic

namespace Vdb
namespace Dmc1TopologyCheck

/-- One parsed `case` line from the C dump. -/
structure Row where
  k : Nat := 0
  crossed : Nat := 0
  verts : Nat := 0
  quads : Nat := 0
  comps : Nat := 0
  closed : Nat := 0
  chi : Int := 0
  deriving Inhabited

/-- The six invariants recomputed from the landed Lean model. -/
structure Expected where
  crossed : Nat
  verts : Nat
  quads : Nat
  comps : Nat
  closed : Nat
  chi : Int

/-- Parse `case <k> crossed <n> verts <v> quads <f> comps <c> closed <0|1> chi <z>`. -/
def parseCaseLine (s : String) : Option Row :=
  match s.splitOn " " with
  | ["case", k, "crossed", cr, "verts", v, "quads", f, "comps", c, "closed", cl, "chi", ch] =>
      match k.toNat?, cr.toNat?, v.toNat?, f.toNat?, c.toNat?, cl.toNat?, ch.toInt? with
      | some a, some b, some c', some d, some e, some g, some h =>
          some { k := a, crossed := b, verts := c', quads := d, comps := e, closed := g, chi := h }
      | _, _, _, _, _, _, _ => none
  | _ => none

/-- The independent Lean recomputation for sign field `k`. -/
def expected (k : Nat) : Expected :=
  let s : Vdb.PadGrid.Lat → Bool := Vdb.DmcOnePad.fin3SignOf k
  let es := Vdb.DmcOnePad.dmcOneMeshEdges s
  let qs := Vdb.DmcOnePad.dmcOneQuads s
  let vs := Vdb.DmcOnePad.meshVerts es
  let ue : Nat := (Vdb.QuadEuler.undirected es).card
  { crossed := (Vdb.PadGrid.crossed 3 s).length
    verts := vs.length
    quads := qs.length
    comps := Vdb.DmcOneDual.meshComponents es
    closed := if Vdb.DmcOnePad.edgeClosedB es then 1 else 0
    chi := (vs.length : Int) - (ue : Int) + (qs.length : Int) }

end Dmc1TopologyCheck
end Vdb

/-- Twin executable. Reads the C dump from argv[0] and prints
    `fields=... badCrossed=... badVerts=... badQuads=... badComps=...
     badClosed=... badChi=...` plus the `stages_unmirrored=` banner. The
    `main` lives in the root namespace, as the Lake executable entry point
    resolves it there. -/
def main (argv : List String) : IO Unit := do
  match argv with
  | [path] =>
      let raw ← IO.FS.readFile path
      let mut nfields := 0
      let mut rows : Array (Vdb.Dmc1TopologyCheck.Row) := #[]
      for line in raw.splitOn "\n" do
        let t := line
        if t.length == 0 then continue
        match t.splitOn " " with
        | ["fields", n] => nfields := n.toNat?.getD 0
        | _ =>
            match Vdb.Dmc1TopologyCheck.parseCaseLine t with
            | some r => rows := rows.push r
            | none => pure ()
      let mut badCrossed := 0
      let mut badVerts := 0
      let mut badQuads := 0
      let mut badComps := 0
      let mut badClosed := 0
      let mut badChi := 0
      for k in List.range 256 do
        let e := Vdb.Dmc1TopologyCheck.expected k
        match rows.find? (fun r => r.k == k) with
        | none =>
            -- A missing field is a disagreement on every invariant.
            badCrossed := badCrossed + 1
            badVerts := badVerts + 1
            badQuads := badQuads + 1
            badComps := badComps + 1
            badClosed := badClosed + 1
            badChi := badChi + 1
        | some r =>
            if r.crossed != e.crossed then badCrossed := badCrossed + 1
            if r.verts != e.verts then badVerts := badVerts + 1
            if r.quads != e.quads then badQuads := badQuads + 1
            if r.comps != e.comps then badComps := badComps + 1
            if r.closed != e.closed then badClosed := badClosed + 1
            if r.chi != e.chi then badChi := badChi + 1
      IO.println s!"fields={rows.size} badCrossed={badCrossed} badVerts={badVerts} badQuads={badQuads} badComps={badComps} badClosed={badClosed} badChi={badChi}"
      IO.println "stages_unmirrored=vertex-indices,vertex-positions,patch-ids"
      if nfields != 256 || rows.size != 256 || badCrossed > 0 || badVerts > 0 ||
         badQuads > 0 || badComps > 0 || badClosed > 0 || badChi > 0 then
        throw (IO.userError "dmc1 topology differential check failed")
  | _ =>
      IO.println "usage: dmc1topocheck <c-output-file>"
      throw (IO.userError "dmc1topocheck: bad args")
