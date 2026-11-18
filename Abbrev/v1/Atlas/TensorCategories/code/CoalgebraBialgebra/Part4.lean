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
@[expose] public section
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


section Def_1_21_2

/-- A bialgebra over `R` is an algebra equipped with a compatible coalgebra structure. -/
abbrev IsBialgebra (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] :=
  Bialgebra R H

/-- Definition 1.21.2: An algebra `H` with comultiplication `Δ` and counit `ε` satisfying
the bialgebra axioms is called a *bialgebra*. -/
abbrev Definition_1_21_2 (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] :=
  Bialgebra R H

end Def_1_21_2
