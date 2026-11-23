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
public import Class.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part2
@[expose] public section

set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


abbrev RightComodule_def_1_20_2 (R : Type u) (C : Type v) (M : Type*) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C] [AddCommMonoid M] [Module R M] :=
  RightComodule R C M

