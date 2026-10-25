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
import Def.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part2
set_option autoImplicit false
open scoped Manifold


/-- Bundled data for a closed oriented almost-complex $4$-manifold: the underlying topology,
Euler number $\chi$, $c_1^2$, $c_2 = \chi$, and the Whitney relation $p_1 = c_1^2 - 2c_2$. -/
structure ChernPontrjaginDataClosed (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M] where
  mfd : ClosedOriented4ManifoldData M
  euler : ℤ
  c₁_sq : ℤ
  c₂ : ℤ
  c₂_eq_euler : c₂ = euler
  p₁_whitney : mfd.p₁ = c₁_sq - 2 * c₂

