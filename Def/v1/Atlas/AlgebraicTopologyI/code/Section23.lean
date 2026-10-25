/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section23.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.Order.Directed
import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.Flat.Localization


namespace HomTensorAdjunction

open TensorProduct

/-- Lemma 23.1 (Hom–tensor adjunction). The natural map
`Hom(L, Hom(M, N)) → Hom(L ⊗ M, N)` is an isomorphism, witnessed here as an `R`-linear
equivalence between `L →ₗ[R] M →ₗ[R] N` and `L ⊗[R] M →ₗ[R] N`. -/
noncomputable def homTensorEquiv
    (R : Type*) [CommSemiring R]
    (L M N : Type*) [AddCommMonoid L] [AddCommMonoid M] [AddCommMonoid N]
    [Module R L] [Module R M] [Module R N] :
    (L →ₗ[R] M →ₗ[R] N) ≃ₗ[R] (L ⊗[R] M →ₗ[R] N) :=
  TensorProduct.lift.equiv (RingHom.id R) L M N

end HomTensorAdjunction
