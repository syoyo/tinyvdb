/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format and the
  volume operators implemented by tinyvdbio.

  lakefile for the `VdbSpec` package.

  mathlib is pinned to the toolchain's tag. Only the coordinate/geometry
  layers need it; the byte, value and mask layers use Lean core alone, but
  the package depends on mathlib as a whole (as the tinyexr formalization
  does) so the build is uniform.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

package vdbSpec where
  -- Formalization artifact; proofs must stay sorry-free.
  leanOptions := #[⟨`warningAsError, true⟩]

@[default_target]
lean_lib VdbSpec where
  globs := #[`VdbSpec, `Vdb.+]

/-- Model-side `.vdb` inspector (differential harness, Lean half). -/
lean_exe vdbcheck where
  root := `VdbCheck

/-- Model-side mask-compression enumeration (differential harness, Lean half,
    driven by `scripts/check_mask_classify.sh`). -/
lean_exe maskcheck where
  root := `MaskClassify

/-- Model-side half-float differential check (differential harness, Lean half,
    driven by `scripts/check_half.sh`). -/
lean_exe halfcheck where
  root := `HalfCheck

/-- Seeded well-formed `.vdb` generator (differential harness, model half). -/
lean_exe vdbgen where
  root := `VdbGen
