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
import Def.v1.Atlas.GeometryOfManifolds.code.PontrjaginObstructions
set_option autoImplicit false
open scoped Manifold


/-- Data of a closed oriented $4$-manifold: Pontrjagin number $p_1$, Betti numbers
$b_2^\pm$, signature $\sigma$, and a symmetric intersection form on $H^2 \cong \mathbb{Z}^{b_2}$. -/
structure ClosedOriented4ManifoldData (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] [CompactSpace M] where
  p₁ : ℤ
  b₂_plus : ℕ
  b₂_minus : ℕ
  signature : ℤ
  signature_eq : signature = (b₂_plus : ℤ) - (b₂_minus : ℤ)
  intersectionForm : (Fin (b₂_plus + b₂_minus) → ℤ) →
    (Fin (b₂_plus + b₂_minus) → ℤ) → ℤ
  intersectionForm_symm : ∀ x y, intersectionForm x y = intersectionForm y x

