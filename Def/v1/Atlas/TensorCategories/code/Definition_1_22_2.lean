/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_22_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
open Coalgebra HopfAlgebra LinearMap
open scoped TensorProduct

universe u v


section Definition_1_22_2

variable (k : Type u) [CommSemiring k] (H : Type v) [Semiring H] [Bialgebra k H]

/-- Definition 1.22.2: An antipode on a bialgebra H is a linear map S : H → H satisfying the
antipode axiom from Proposition 1.22.1, namely mu ∘ (id ⊗ S) ∘ Delta = i ∘ eps =
mu ∘ (S ⊗ id) ∘ Delta as maps H → H. -/
def Definition_1_22_2 (S : H →ₗ[k] H) : Prop :=
  mul' k H ∘ₗ S.rTensor H ∘ₗ comul = (Algebra.linearMap k H) ∘ₗ counit ∧
  mul' k H ∘ₗ S.lTensor H ∘ₗ comul = (Algebra.linearMap k H) ∘ₗ counit

end Definition_1_22_2

section Definition_1_22_2_instance

variable (k : Type u) [CommSemiring k] (H : Type v) [Semiring H] [HopfAlgebra k H]

/-- Given a bialgebra H and a linear map S satisfying the antipode axiom of Definition 1.22.2,
this constructs a Hopf algebra structure on H with antipode S. -/
@[reducible]
def Definition_1_22_2_corresponds_to_HopfAlgebra
    (S : H →ₗ[k] H) (hS : Definition_1_22_2 k H S) : HopfAlgebra k H :=
  letI : HopfAlgebraStruct k H := ⟨S⟩
  { mul_antipode_rTensor_comul := hS.1
    mul_antipode_lTensor_comul := hS.2 }

end Definition_1_22_2_instance
