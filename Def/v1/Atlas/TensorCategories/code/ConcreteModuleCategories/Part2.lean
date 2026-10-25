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
import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part3
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section BimoduleCategory

/-- The bimodule category structure of `C` over itself on both sides: left and right
actions are both given by tensor product, with the middle interchange being the associator. -/
def selfBimoduleCategoryStruct
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] :
    BimoduleCategoryStruct C C C where
  lactObj X N := X ⊗ N
  ractObj N Y := N ⊗ Y
  lactWhiskerLeft X {N₁ N₂} f := X ◁ f
  lactWhiskerRight {X₁ X₂} f N := f ▷ N
  ractWhiskerLeft {N₁ N₂} f Y := f ▷ Y
  ractWhiskerRight N {Y₁ Y₂} f := N ◁ f
  lactAssociator X Y N := α_ X Y N
  ractAssociator N X Y := α_ N X Y
  lactLeftUnitor N := λ_ N
  ractRightUnitor N := ρ_ N
  middleInterchange X N Y := α_ X N Y

end BimoduleCategory
end CategoryTheory
