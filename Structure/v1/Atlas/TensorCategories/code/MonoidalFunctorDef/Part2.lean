/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorDef
open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

attribute [instance] def_1_1_2_MonoidalSubcategory.instCat
  def_1_1_2_MonoidalSubcategory.instMonoidal
  def_1_1_2_MonoidalSubcategory.instFaithful

section MonoidalFunctor

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
  (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D]

/-- EGNO Definition 1.4.1: a monoidal functor `C ⥤ D` is a functor `F` together with the
data of a monoidal structure on `F`. -/
structure def_1_4_1_MonoidalFunctor where
  F : C ⥤ D
  instMonoidal : F.Monoidal

end MonoidalFunctor
end TensorCategories
