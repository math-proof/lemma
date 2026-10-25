/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Structure.v1.Atlas.TensorCategories.code.QuasiBialgebra
set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


/-- Definition 1.35.2 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-Hopf algebra is
a quasi-bialgebra `(H, Δ, ε, Φ)` equipped with an antipode `(S, α, β)` where
`S` is bijective. -/
class QuasiHopfAlgebra (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [Algebra R H]
    extends QuasiBialgebra R H where
  S : H ≃ₗ[R] H
  α_elem : H
  β_elem : H
  S_anti_mul : ∀ a b : H, S (a * b) = S b * S a
  S_one : S 1 = 1
  left_antipode : ∀ b : H,
    QuasiBialgebra.sAlphaMap R H S.toLinearMap α_elem (comul b) = counit b • α_elem
  right_antipode : ∀ b : H,
    QuasiBialgebra.betaSMap R H S.toLinearMap β_elem (comul b) = counit b • β_elem
  phi_beta_S_alpha :
    QuasiBialgebra.phiBetaSAlphaMap R H S.toLinearMap α_elem β_elem
      (Φ : H ⊗[R] (H ⊗[R] H)) = 1
  phiInv_S_alpha_beta_S :
    QuasiBialgebra.phiInvSAlphaBetaSMap R H S.toLinearMap α_elem β_elem
      (↑Φ⁻¹ : H ⊗[R] (H ⊗[R] H)) = 1


