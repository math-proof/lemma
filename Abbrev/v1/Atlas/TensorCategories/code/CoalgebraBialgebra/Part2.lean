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
import Class.v1.Atlas.TensorCategories.code.CoalgebraBialgebra
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


abbrev LeftComodule_def_1_20_2 (R : Type u) (C : Type v) (M : Type*) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] :=
  Comodule R C M

abbrev Definition_1_20_2 (R : Type u) (C : Type v) (M : Type*) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] :=
  Comodule R C M

