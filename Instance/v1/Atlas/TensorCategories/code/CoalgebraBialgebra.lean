/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Products.Basic
public import Structure.v1.Atlas.TensorCategories.code.CoalgebraBialgebra

@[expose] public section

set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


namespace Subcoalgebra

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

instance : SetLike (Subcoalgebra R A) A where
  coe S := S.toSubmodule
  coe_injective S T h := by
    cases S; cases T; congr 1; exact SetLike.coe_injective h

end Subcoalgebra
