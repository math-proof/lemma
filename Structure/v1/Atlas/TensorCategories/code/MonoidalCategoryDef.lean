/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Def.v1.Atlas.TensorCategories.code.MonoidalCategoryDef.Part3
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v v₂ u u₂


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- EGNO Definition 1.1.2: a monoidal subcategory of `C` is a category `D` equipped with a
faithful monoidal functor `ι : D ⥤ C`. -/
structure Definition_1_1_2 (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  D : Type u₂
  [instCat : Category.{v₂} D]
  [instMonoidal : MonoidalCategory D]
  ι : D ⥤ C
  [instFaithful : ι.Faithful]
  instMonoidalFunctor : ι.Monoidal

end TensorCategories
