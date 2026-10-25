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
import Structure.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions
set_option autoImplicit false
open scoped Manifold


/-- Topological data attached to a closed smooth $4$-manifold $M$: its intersection form `Q`
and Euler characteristic $\chi(M) = 2 + b_2(M)$ (for simply connected $M$). -/
class Mfd4Topology (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M] where
  Q : Mfd4IntersectionForm
  euler : ℤ
  euler_eq : euler = 2 + (Q.b₂ : ℤ)


