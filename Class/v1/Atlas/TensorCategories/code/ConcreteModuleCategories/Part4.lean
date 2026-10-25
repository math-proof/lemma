/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ConcreteModuleCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Theorem.v1.Atlas.TensorCategories.code.DeligneTensorProductMonoidal
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite
import Def.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part3
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section BimoduleCategory

/-- A predicate `P` on the objects of a left `C`-module category `M` defines a module
subcategory if it is closed under the left action of `C`. -/
class ModuleSubcategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type*) [Category M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) : Prop where
  action_closed : ∀ (X : C) (N : M), P N → P (LeftModuleCategoryStruct.actObj X N)

end BimoduleCategory
end CategoryTheory
