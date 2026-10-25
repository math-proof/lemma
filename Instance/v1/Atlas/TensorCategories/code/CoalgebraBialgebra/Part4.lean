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
import Def.v1.Atlas.TensorCategories.code.CoalgebraBialgebra
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


section Thm_1_21_1

open MonoidalCategory

variable (k : Type u) [CommRing k]

variable (C : Type v) [Category.{w} C] [MonoidalCategory C] [Preadditive C] [Linear k C]

variable (F : C ⥤ ModuleCat.{u} k) [F.Monoidal] [F.Faithful]

set_option synthInstance.maxHeartbeats 400000

/-- The tensor product `End(F) ⊗_k End(F)` is itself a (semi)ring via the tensor product
of algebras. -/
noncomputable instance instSemiringEndTensor :
    Semiring (TensorProduct k (End F) (End F)) :=
  Algebra.TensorProduct.instSemiring

/-- The tensor product `End(F) ⊗_k End(F)` is a `k`-algebra. -/
noncomputable instance instAlgebraEndTensor :
    Algebra k (TensorProduct k (End F) (End F)) :=
  Algebra.TensorProduct.instAlgebra

end Thm_1_21_1
