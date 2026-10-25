/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra WithConv LinearMap
open scoped TensorProduct

universe u v


section Proposition_1_22_1

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- The candidate "antimultiplication" map `A ⊗ A → A` in the commutative case, defined as
`μ ∘ (S ⊗ S)`. Used to show `S` is an algebra antihomomorphism. -/
def HopfAlgebra.antimulComm : A ⊗[R] A →ₗ[R] A :=
  (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toLinearMap.comp
    (TensorProduct.map (antipode R) (antipode R))

end Proposition_1_22_1
