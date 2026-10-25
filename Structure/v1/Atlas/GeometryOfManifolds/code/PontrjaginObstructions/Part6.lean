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
import Def.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part4
set_option autoImplicit false
open scoped Manifold


/-- Witness that an almost complex structure `J` has first Chern class with prescribed coordinates
in the basis of $H^2(M; \mathbb{Z})$. -/
structure HasFirstChernClassGeneral
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    (J : Mfd4AlmostComplexStr M)
    (obsData : AlmostComplexObstructionDataGeneral M) where
  c₁_coords : Fin obsData.rank_H2 → ℤ


/-- Theorem 2 (almost-complex existence): there exists an almost complex structure $J$ on $M^4$
with $\alpha = c_1(TM, J)$ iff $\alpha^2 \cdot [M] = 2\chi + 3\sigma$ and
$\alpha \cdot [A] \equiv Q([A], [A]) \pmod 2$ for every $[A] \in H_2(M; \mathbb{Z})$. -/
structure AlmostComplexObstructionData (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M]
    [htop : Mfd4Topology M] where
  rank_H2 : ℕ
  rank_eq : rank_H2 = htop.Q.b₂
  pairing : (Fin rank_H2 → ℤ) → (Fin rank_H2 → ℤ) → ℤ
  pairing_symm : ∀ (α β : Fin rank_H2 → ℤ), pairing α β = pairing β α

