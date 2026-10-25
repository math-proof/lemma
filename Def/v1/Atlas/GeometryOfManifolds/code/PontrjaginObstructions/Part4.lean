/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/PontrjaginObstructions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic
import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part5
set_option autoImplicit false
open scoped Manifold


/-- The square $\alpha^2 \cdot [M] = Q(\alpha, \alpha)$ evaluated via the bilinear pairing. -/
def AlmostComplexObstructionDataGeneral.square_eval
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (obsData : AlmostComplexObstructionDataGeneral M)
    (α : Fin obsData.rank_H2 → ℤ) : ℤ :=
  obsData.pairing α α

/-- Self-pairing $Q([A], [A])$ of a homology class with itself under the intersection form. -/
def AlmostComplexObstructionDataGeneral.Q_selfpairing
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (obsData : AlmostComplexObstructionDataGeneral M)
    (A : Fin obsData.rank_H2 → ℤ) : ℤ :=
  obsData.pairing A A

