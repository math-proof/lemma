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
import Class.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions
set_option autoImplicit false
open scoped Manifold


/-- Chern and Pontrjagin number data for a closed $4$-manifold equipped with an almost complex
structure: $c_1^2 \cdot [M]$, $c_2 \cdot [M]$, with $c_2 = \chi(M)$. -/
structure HasChernPontrjaginData (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M] where
  c₁_sq : ℤ
  c₂ : ℤ
  c₂_eq_euler : c₂ = htop.euler

