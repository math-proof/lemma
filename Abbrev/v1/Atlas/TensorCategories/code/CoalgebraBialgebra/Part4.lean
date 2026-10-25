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
import Def.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part2
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
