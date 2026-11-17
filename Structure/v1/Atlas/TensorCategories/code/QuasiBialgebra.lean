/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Def.v1.Atlas.TensorCategories.code.QuasiBialgebra.Part2
public section

set_option maxHeartbeats 800000

open scoped TensorProduct

universe u v


/-- Definition 1.35.2 (Etingof–Gelaki–Nikshych–Ostrik): An antipode on a
quasi-bialgebra is a triple `(S, α, β)` with `S : H → H` a unital algebra
antihomomorphism and `α, β ∈ H` satisfying the antipode identities
(1.35.1) and (1.35.2). -/
structure QuasiBialgebraAntipode (R : Type u) (H : Type v)
    [CommSemiring R] [Semiring H] [Algebra R H]
    [qb : QuasiBialgebra R H] where
  S : H →ₗ[R] H
  α_elem : H
  β_elem : H
  S_anti_mul : ∀ a b : H, S (a * b) = S b * S a
  S_one : S 1 = 1
  left_antipode : ∀ b : H,
    QuasiBialgebra.sAlphaMap R H S α_elem (qb.comul b) = qb.counit b • α_elem
  right_antipode : ∀ b : H,
    QuasiBialgebra.betaSMap R H S β_elem (qb.comul b) = qb.counit b • β_elem
  phi_beta_S_alpha :
    QuasiBialgebra.phiBetaSAlphaMap R H S α_elem β_elem
      (qb.Φ : H ⊗[R] (H ⊗[R] H)) = 1
  phiInv_S_alpha_beta_S :
    QuasiBialgebra.phiInvSAlphaBetaSMap R H S α_elem β_elem
      (↑qb.Φ⁻¹ : H ⊗[R] (H ⊗[R] H)) = 1


