#!/usr/bin/env bash
# Axiom-profile gate: runs the in-tree AxiomAudit.lean, which walks every
# Vdb.* declaration using Lean's own collectAxioms and fails on any axiom
# outside {propext, Classical.choice, Quot.sound, native/bv_decide certificates}.
set -euo pipefail

if ! command -v lake >/dev/null 2>&1; then
  echo "SKIP: Lean toolchain (lake) is not available"
  exit 77
fi
here=$(cd "$(dirname "$0")/.." && pwd)
export ELAN_TOOLCHAIN="$(cat "$here/lean-toolchain")"

cd "$here"
out=$(timeout 600 lake env lean AxiomAudit.lean 2>&1)
echo "$out"

case "$out" in
  *"AUDIT OK: only documented axioms used"*) ;;
  *) echo "FAIL: axiom audit did not pass" >&2; exit 1;;
esac
# Negative control: the gate must actually fail if an unexpected axiom
# appears.  We check the audit text contains the declaration count so a
# silently truncated run cannot pass.
case "$out" in
  *"Vdb declarations audited: 4729"*) ;;
  *) echo "FAIL: audit did not cover the expected declaration count" >&2; exit 1;;
esac
echo "OK axiom audit: 4729 Vdb declarations, documented axiom profile only"
