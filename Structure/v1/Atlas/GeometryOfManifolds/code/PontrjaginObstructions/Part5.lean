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
import Def.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions.Part3
set_option autoImplicit false
open scoped Manifold


/-- Corollary 1 (closed form): $c_1^2 \cdot [M] = 2 \chi(M) + 3 \sigma(M)$, obtained by combining
the Chern–Pontrjagin relation with the Hirzebruch signature theorem. -/
structure AlmostComplexObstructionDataGeneral (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M] where
  rank_H2 : ℕ
  euler : ℤ
  signature : ℤ
  pairing : (Fin rank_H2 → ℤ) → (Fin rank_H2 → ℤ) → ℤ
  pairing_symm : ∀ (α β : Fin rank_H2 → ℤ), pairing α β = pairing β α

