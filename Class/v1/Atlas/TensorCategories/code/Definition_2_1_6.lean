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
universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- A `ModuleSubcategory` of `M` over `C`: a predicate `P : M → Prop` that is closed
under the action of `C` on `M`. -/
class ModuleSubcategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) : Prop where
  closed_under_action : ∀ (X : C) (N : M), P N → P (X ⊗ᵐ N)

end CategoryTheory
