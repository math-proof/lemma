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
import Structure.v1.Atlas.TensorCategories.code.CoalgebraBialgebra
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


namespace Subcoalgebra

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

instance : SetLike (Subcoalgebra R A) A where
  coe S := S.toSubmodule
  coe_injective' S T h := by
    cases S; cases T; congr 1; exact SetLike.coe_injective h

end Subcoalgebra
