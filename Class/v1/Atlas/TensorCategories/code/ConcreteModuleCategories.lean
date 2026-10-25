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
import Def.v1.Atlas.TensorCategories.code.ConcreteModuleCategories
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section BimoduleCategory

/-- Structure of a right module category over a monoidal category `D`: provides a right
action `ractObj : M → D → M` together with whiskering, associator, and right unitor data. -/
class RightModuleCategoryStruct
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D]
    (M : Type*) [Category M] where
  ractObj : M → D → M
  ractWhiskerLeft {N₁ N₂ : M} (f : N₁ ⟶ N₂) (X : D) :
    ractObj N₁ X ⟶ ractObj N₂ X
  ractWhiskerRight (N : M) {X₁ X₂ : D} (f : X₁ ⟶ X₂) :
    ractObj N X₁ ⟶ ractObj N X₂
  ractAssociator : ∀ (N : M) (X Y : D),
    ractObj (ractObj N X) Y ≅ ractObj N (X ⊗ Y)
  ractRightUnitor : ∀ (N : M), ractObj N (𝟙_ D) ≅ N

end BimoduleCategory
end CategoryTheory
