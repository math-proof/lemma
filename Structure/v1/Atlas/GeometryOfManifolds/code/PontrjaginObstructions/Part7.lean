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
import Def.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part5
set_option autoImplicit false
open scoped Manifold


/-- Witness that an almost complex structure `J` has a first Chern class with the given
integer coordinates in the obstruction basis. -/
structure HasFirstChernClass
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]
    (J : Mfd4AlmostComplexStr M)
    (obsData : AlmostComplexObstructionData M) where
  c₁_coords : Fin obsData.rank_H2 → ℤ

