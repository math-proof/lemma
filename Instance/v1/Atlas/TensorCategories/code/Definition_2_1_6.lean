/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_1_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.IsomorphismClasses
import Class.v1.Atlas.TensorCategories.code.Definition_2_1_6
universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- An `IsModuleSubcategory` predicate yields a `ModuleSubcategory` instance. -/
instance moduleSubcategory_of_isModuleSubcategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) [h : IsModuleSubcategory C M P] : ModuleSubcategory C M P where
  closed_under_action := h.closed_under_action

/-- A `ModuleSubcategory` predicate yields an `IsModuleSubcategory` instance. -/
instance isModuleSubcategory_of_moduleSubcategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) [h : ModuleSubcategory C M P] : IsModuleSubcategory C M P where
  closed_under_action := h.closed_under_action

end CategoryTheory
