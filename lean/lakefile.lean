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
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.36.0"

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

/-- Model-side Godunov differential harness (driven by `scripts/check_godunov.sh`). -/
lean_exe godunovcheck where
  root := `Vdb.GodunovCheck

/-- Model-side signed-flood-fill differential harness (driven by `scripts/check_fill.sh`). -/
lean_exe fillcheck where
  root := `Vdb.FillCheck

/-- Model-side Euler-characteristic differential harness (driven by `scripts/check_euler.sh`). -/
lean_exe eulercheck where
  root := `Vdb.EulerCheck

/-- Model-side fast-sweeping differential harness (driven by `scripts/check_fastsweep.sh`). -/
lean_exe fastsweepcheck where
  root := `Vdb.FastSweepCheck

/-- Model-side dense CSG differential harness (driven by `scripts/check_csg.sh`). -/
lean_exe csgcheck where
  root := `Vdb.CsgCheck

/-- Model-side dense mesh→SDF differential harness (driven by
    `scripts/check_meshsdf.sh`). -/
lean_exe meshsdfcheck where
  root := `Vdb.MeshSdfCheck

/-- Model-side dense mesh→SDF BVH differential twin (driven by
    `scripts/check_meshsdf_bvh.sh`). -/
lean_exe meshsdfbvhcheck where
  root := `Vdb.MeshSdfBvhCheck

/-- Model-side dense marching-cubes topology twin (driven by
    `scripts/check_mc_topology.sh`). -/
lean_exe mctopocheck where
  root := `Vdb.McTopologyCheck

/-- Model-side Float32 BVH tie-explanation twin (driven by
    `scripts/check_meshsdf_bvh_ties.sh`). -/
lean_exe meshsdfbvhtiecheck where
  root := `Vdb.MeshSdfBvhTieCheck

/-- Model-side mesh→SDF double-fallback/RNE twin (driven by
    `scripts/check_meshsdf_double.sh`). -/
lean_exe meshsdfdoublecheck where
  root := `Vdb.MeshSdfDoubleCheck

/-- Model-side sparse/tree marching-cubes topology twin (driven by
    `scripts/check_mc_sparse_topology.sh`). -/
lean_exe mcsparsetopocheck where
  root := `Vdb.McSparseTopologyCheck

/-- Model-side DMC-1 topology differential twin (driven by
    `scripts/check_dmc1_topology.sh`). -/
lean_exe dmc1topocheck where
  root := `Vdb.Dmc1TopologyCheck

/-- Model-side winding-number executable check (driven by `scripts/check_winding.sh`). -/
lean_exe windingcheck where
  root := `Vdb.WindingCheck

/-- Model-side MC-adaptivity Float-floor/int64-key twin (driven by
    `scripts/check_mc_adapt.sh`). -/
lean_exe mckeycheck where
  root := `Vdb.McAdaptKey

/-- Model-side collision-pipeline twin (driven by `scripts/check_collision_pipeline.sh`). -/
lean_exe collisioncheck where
  root := `Vdb.CollisionPipelineCheck

/-- Model-side SDF ray-crossing twin (driven by `scripts/check_ray_sdf.sh`). -/
lean_exe raysdfcheck where
  root := `Vdb.RaySdfCheck

/-- Model-side ray-DDA twin (driven by `scripts/check_ray_dda.sh`). -/
lean_exe rayddacheck where
  root := `Vdb.RayDdaCheck

/-- Model-side sphere/mesh contact twin (driven by `scripts/check_contact.sh`). -/
lean_exe contactcheck where
  root := `Vdb.ContactCheck

/-- Model-side convex-part decomposition twin (driven by
    `scripts/check_convex_parts.sh`). -/
lean_exe convexcheck where
  root := `Vdb.ConvexDecompCheck

/-- Model-side collision-proxy differential twin (driven by
    `scripts/check_proxy.sh`). -/
lean_exe proxycheck where
  root := `Vdb.CollisionProxyCheck

/-- Model-side SDF part/cavity differential twin (driven by
    `scripts/check_sdf_parts.sh`). -/
lean_exe sdfpartcheck where
  root := `Vdb.SdfPartsCheck

/-- Seeded well-formed `.vdb` generator (differential harness, model half). -/
lean_exe vdbgen where
  root := `VdbGen
