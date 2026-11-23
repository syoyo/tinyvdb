/-
  TinyVDB - Lean 4 formalization of the OpenVDB (`.vdb`) file format.

  Root module for the `VdbSpec` library.

  Copyright (c) 2026 Syoyo Fujita and TinyVDB authors
  SPDX-License-Identifier: Apache-2.0
-/
import Vdb.Bytes
import Vdb.Value
import Vdb.Mask
import Vdb.Coord
import Vdb.Layout
import Vdb.LevelSet
import Vdb.Sign
import Vdb.MeshDistance
import Vdb.MarchingCubes
import Vdb.DualVertex
import Vdb.Reconstruct
import Vdb.DualSurface
import Vdb.GlobalSurface
import Vdb.Assembly
import Vdb.CubeGrid
import Vdb.CubeField
import Vdb.Winding
import Vdb.BoxInside
import Vdb.MeshRay
import Vdb.Tree
import Vdb.MaskCompress
import Vdb.NodeRecord
import Vdb.ValueCount
import Vdb.Half
import Vdb.Chunk
import Vdb.Stable
import Vdb.Chunks
import Vdb.Meta
import Vdb.Topology
import Vdb.TreeNode
import Vdb.TreeBuffer
import Vdb.TreeDerived
import Vdb.TreeHalf
import Vdb.Transform
import Vdb.File
import Vdb.FilePrefix
import Vdb.GridDescriptor
import Vdb.GridBody
import Vdb.GridBody5
import Vdb.GridHeader
import Vdb.Header
import Vdb.PseudoNormal
import Vdb.EikonalTop
import Vdb.Cuberille
import Vdb.StaircaseRatio
import Vdb.NormalCone
import Vdb.McTable
import Vdb.TreeSweep
import Vdb.PadGrid
import Vdb.PadGridBoundary
import Vdb.PhysMesh
import Vdb.SdfMask
import Vdb.Segmentation
-- `Vdb.GenusMeasure` is deliberately not imported here: it depends on
-- `Vdb.Euler`, whose `Vdb.C3` name collides with `Vdb.CubeGrid.C3` (both are in
-- the root import). Like `Vdb.Euler` itself it is built by the `Vdb.+` glob but
-- stays a standalone module.
import Vdb.Cpt
import Vdb.Qem
import Vdb.EdgeCollapse
import Vdb.CollisionProxy
import Vdb.Convex
import Vdb.ConvexDecomp
import Vdb.ConvexHull
import Vdb.Contact
import Vdb.Manifold
import Vdb.RayDda
import Vdb.RaySdf
import Vdb.TetStuffing
import Vdb.NarrowPhase
import Vdb.PersistentManifold
import Vdb.AngleNFaceRatBounded
import Vdb.FastSweep1D
import Vdb.StaircaseReflectionBounded
-- Vdb.EulerDisjointBounded is standalone: Vdb.Euler.C3 collides with Vdb.CubeGrid.C3
