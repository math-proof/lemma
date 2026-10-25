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
import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part2
set_option autoImplicit false
open scoped Manifold


/-- First Pontrjagin number $p_1 \cdot [M] = c_1^2 - 2 c_2$, the Whitney sum relation for an
almost complex $4$-manifold. -/
def HasChernPontrjaginData.p₁ {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [Mfd4Topology M]
    (hcp : HasChernPontrjaginData M) : ℤ :=
  hcp.c₁_sq - 2 * hcp.c₂


