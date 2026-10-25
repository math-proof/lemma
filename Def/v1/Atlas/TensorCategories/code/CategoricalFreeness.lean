/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CategoricalFreeness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Structure.v1.Atlas.TensorCategories.code.CategoricalFreeness
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
