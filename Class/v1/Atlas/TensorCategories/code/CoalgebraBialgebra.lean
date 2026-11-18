module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Products.Basic
public section
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


class Comodule (R : Type u) (C : Type v) (M : Type*)
    [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M] where
  coact : M →ₗ[R] C ⊗[R] M
  coassoc : TensorProduct.assoc R C C M ∘ₗ Coalgebra.comul.rTensor M ∘ₗ coact =
    coact.lTensor C ∘ₗ coact
  counit_coact : Coalgebra.counit.rTensor M ∘ₗ coact = TensorProduct.mk R R M 1

