/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Products.Basic
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


section CoalgebraRecap

variable (R : Type u) (A : Type v) [CommSemiring R] [AddCommMonoid A] [Module R A]

variable [Coalgebra R A]

example : A →ₗ[R] A ⊗[R] A := Coalgebra.comul

example : A →ₗ[R] R := Coalgebra.counit

example : TensorProduct.assoc R A A A ∘ₗ comul.rTensor A ∘ₗ comul =
    comul.lTensor A ∘ₗ (comul : A →ₗ[R] A ⊗[R] A) :=
  Coalgebra.coassoc

example : counit.rTensor A ∘ₗ (comul : A →ₗ[R] A ⊗[R] A) = TensorProduct.mk R _ _ 1 :=
  Coalgebra.rTensor_counit_comp_comul

example : counit.lTensor A ∘ₗ (comul : A →ₗ[R] A ⊗[R] A) = (TensorProduct.mk R _ _).flip 1 :=
  Coalgebra.lTensor_counit_comp_comul

end CoalgebraRecap
