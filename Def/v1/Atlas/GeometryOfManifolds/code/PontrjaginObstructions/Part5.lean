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
import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part6
set_option autoImplicit false
open scoped Manifold


/-- Forget the link to `Mfd4Topology` and produce general almost-complex obstruction data. -/
def AlmostComplexObstructionData.toGeneral
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]
    (obsData : AlmostComplexObstructionData M) :
    AlmostComplexObstructionDataGeneral M where
  rank_H2 := obsData.rank_H2
  euler := htop.euler
  signature := htop.Q.signature
  pairing := obsData.pairing
  pairing_symm := obsData.pairing_symm

