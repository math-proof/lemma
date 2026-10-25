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
import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part4
set_option autoImplicit false
open scoped Manifold


/-- Construct the bundled closed Chern–Pontrjagin data from `HasChernPontrjaginData` together
with `Mfd4Topology`, assuming the simply-connected case. -/
def ChernPontrjaginDataClosed.ofSimplyConnected
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M]
    (hcp : HasChernPontrjaginData M) :
    ChernPontrjaginDataClosed M where
  mfd := ClosedOriented4ManifoldData.ofChernPontrjagin hcp
  euler := htop.euler
  c₁_sq := hcp.c₁_sq
  c₂ := hcp.c₂
  c₂_eq_euler := hcp.c₂_eq_euler
  p₁_whitney := by

    show (ClosedOriented4ManifoldData.ofChernPontrjagin hcp).p₁ = hcp.c₁_sq - 2 * hcp.c₂
    dsimp only [ClosedOriented4ManifoldData.ofChernPontrjagin, HasChernPontrjaginData.p₁]


