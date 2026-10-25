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
open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

/-- EGNO Definition 1.1.2: a monoidal subcategory of `C` is a category `D` with a
faithful monoidal functor `ι : D ⥤ C`. -/
structure def_1_1_2_MonoidalSubcategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] where
  D : Type u₂
  [instCat : Category.{v₂} D]
  [instMonoidal : MonoidalCategory D]
  ι : D ⥤ C
  [instFaithful : ι.Faithful]
  instMonoidalFunctor : ι.Monoidal

end TensorCategories
