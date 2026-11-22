/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Axiom audit gate (plan-lean.md §1). Imports the whole `VdbSpec` library,
  walks every first-party declaration (`Vdb.*`), and reports the transitive
  axiom profile using Lean's own `collectAxioms` (the implementation behind
  `#print axioms`). The audit fails if any axiom outside the documented
  allow-list appears.

  Allowed: `propext`, `Classical.choice`, `Quot.sound` (the standard Lean
  quotient/choice profile) and `Lean.ofReduceBool` (the native reduction
  certificate used by `native_decide` self-checks). The per-theorem
  `native_decide` atoms are counted, not treated as new axiom kinds.

  Run: `cd lean && lake env lean AxiomAudit.lean` (or `scripts/check_axioms.sh`).
  There is no `sorry`/`admit` in landed modules; `grep` checks that separately.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/

import VdbSpec

open Lean
open Lean.Elab.Command

namespace TinyVdbAxiomAudit

/-- The documented axiom allow-list. -/
def allowed : Std.HashSet Name :=
  { `propext, `Classical.choice, `Quot.sound, `Lean.ofReduceBool }

/-- `native_decide` proof certificates are named
    `<theorem>._native.native_decide.ax_<n>`; they are reduction certificates,
    not new logical axioms, and are counted in the report. -/
def isNativeDecideAtom (a : Name) : Bool :=
  let s := a.toString
  s.contains "_native.native_decide.ax" || s.contains "_native.bv_decide.ax" ||
    s.contains "Lean.ofReduceBool"

/-- Collect axiom -> number of first-party declarations that (transitively)
    depend on it. Generated native-decide helper declarations are skipped;
    their axioms are reported through the theorems that use them. -/
def collectProfile (env : Environment) :
    CommandElabM (Std.HashMap Name Nat × Std.HashMap Name Nat) := do
  let mut axioms : Std.HashMap Name Nat := {}
  let mut disallowed : Std.HashMap Name Nat := {}
  let mut visited := 0
  for (n, _) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Vdb" && !s.contains "_native" then
      visited := visited + 1
      let axs ← collectAxioms n
      for a in axs do
        axioms := axioms.insert a (axioms.getD a 0 + 1)
        if !allowed.contains a && !isNativeDecideAtom a then
          disallowed := disallowed.insert a (disallowed.getD a 0 + 1)
  IO.println s!"Vdb declarations audited: {visited}"
  return (axioms, disallowed)

/-- The audit command: prints the profile and fails on any disallowed axiom. -/
elab "audit_vdb_axioms" : command => do
  let env ← getEnv
  let (axioms, disallowed) ← collectProfile env
  let mut lines : Array String := #[]
  for (a, c) in axioms.toList do
    lines := lines.push s!"  {a}: {c}"
  IO.println "Vdb axiom profile (axiom -> #declarations depending on it):"
  for l in lines do IO.println l
  if disallowed.isEmpty then
    IO.println "AUDIT OK: only documented axioms used"
  else
    let mut bad : Array String := #[]
    for (a, _) in disallowed.toList do
      bad := bad.push a.toString
    logError m!"AUDIT FAILED: disallowed axioms: {bad.toList}"

end TinyVdbAxiomAudit

open TinyVdbAxiomAudit

audit_vdb_axioms
