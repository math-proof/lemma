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
import Def.v1.Atlas.TensorCategories.code.HopfAlgebra
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra WithConv LinearMap
open scoped TensorProduct

universe u v


section HopfAlgebraRecap

variable (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [HopfAlgebra R A]

example : A →ₗ[R] A := HopfAlgebra.antipode R

example : mul' R A ∘ₗ (antipode R).rTensor A ∘ₗ comul =
    (Algebra.linearMap R A) ∘ₗ counit :=
  HopfAlgebra.mul_antipode_rTensor_comul

example : mul' R A ∘ₗ (antipode R).lTensor A ∘ₗ comul =
    (Algebra.linearMap R A) ∘ₗ counit :=
  HopfAlgebra.mul_antipode_lTensor_comul

example : HopfAlgebra.antipode R (1 : A) = 1 :=
  HopfAlgebra.antipode_one

example (a : A) : counit (HopfAlgebra.antipode R a) = counit (R := R) a :=
  HopfAlgebra.counit_antipode a

end HopfAlgebraRecap


section Proposition_1_22_1

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- The antipode acts as a right inverse to the identity in the convolution algebra:
`S * id = 1` in `WithConv (A →ₗ[R] A)`. -/
theorem HopfAlgebra.antipode_conv_id {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [HopfAlgebra R A] :
    (toConv (antipode R) : WithConv (A →ₗ[R] A)) * toConv .id = 1 := by
  ext a; simp [convMul_apply, convOne_apply]; exact mul_antipode_rTensor_comul_apply a

/-- The antipode acts as a left inverse to the identity in the convolution algebra:
`id * S = 1` in `WithConv (A →ₗ[R] A)`. -/
theorem HopfAlgebra.id_conv_antipode {R : Type u} {A : Type v}
    [CommSemiring R] [Semiring A] [HopfAlgebra R A] :
    (toConv (.id : A →ₗ[R] A)) * toConv (antipode R) = 1 := by
  ext a; simp [convMul_apply, convOne_apply]; exact mul_antipode_lTensor_comul_apply a

end Proposition_1_22_1
