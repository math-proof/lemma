/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CategoricalFreeness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Structure.v1.Atlas.TensorCategories.code.CategoricalFreeness

@[expose] public section

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w


namespace CategoryTheory

namespace FPdimFunction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A Frobenius-Perron dimension function is integral (Definition 1.48.1) if the dimension
of every object is an integer. -/
def IsIntegral (d : FPdimFunction (C := C)) : Prop :=
  ∀ (X : C), ∃ (n : ℤ), d.fpDim X = ↑n

end FPdimFunction
end CategoryTheory
