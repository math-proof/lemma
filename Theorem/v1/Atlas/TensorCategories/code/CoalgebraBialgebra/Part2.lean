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
public import Instance.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part3
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

public section

universe u v w


section BialgebraRecap

variable (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Bialgebra R A]

example : Algebra R A := Bialgebra.toAlgebra

example : Coalgebra R A := Bialgebra.toCoalgebra

example : A →ₐ[R] A ⊗[R] A := Bialgebra.comulAlgHom R A

example : A →ₐ[R] R := Bialgebra.counitAlgHom R A

example (a b : A) : Coalgebra.comul (R := R) (a * b) =
    Coalgebra.comul a * Coalgebra.comul b :=
  Bialgebra.comul_mul a b

example (a b : A) : Coalgebra.counit (R := R) (a * b) =
    Coalgebra.counit a * Coalgebra.counit b :=
  Bialgebra.counit_mul a b

example : Coalgebra.comul (R := R) (1 : A) = 1 := Bialgebra.comul_one

example : Coalgebra.counit (R := R) (1 : A) = 1 := Bialgebra.counit_one

end BialgebraRecap
