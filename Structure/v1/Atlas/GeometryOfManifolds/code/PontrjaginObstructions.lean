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
set_option autoImplicit false
open scoped Manifold


/-- Algebraic data of the intersection form of a closed oriented $4$-manifold:
second Betti number $b_2 = b_2^+ + b_2^-$, signature $\sigma = b_2^+ - b_2^-$, parity, and a
symmetric bilinear form on $H^2(M; \mathbb{Z}) \cong \mathbb{Z}^{b_2}$. -/
structure Mfd4IntersectionForm where
  b₂ : ℕ
  b₂_plus : ℕ
  b₂_minus : ℕ
  rank_decomp : b₂ = b₂_plus + b₂_minus
  signature : ℤ
  signature_eq : signature = (b₂_plus : ℤ) - (b₂_minus : ℤ)
  isEven : Bool
  bilinForm : (Fin b₂ → ℤ) → (Fin b₂ → ℤ) → ℤ
  bilinForm_symm : ∀ x y, bilinForm x y = bilinForm y x

/-- An almost-complex structure $J$ on a smooth $4$-manifold (placeholder, witnessing existence). -/
structure Mfd4AlmostComplexStr (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (𝓡 4) ⊤ M] where
  mk' ::

