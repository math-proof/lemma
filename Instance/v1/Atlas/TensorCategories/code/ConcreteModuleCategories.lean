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
import Abbrev.v1.Atlas.TensorCategories.code.ConcreteModuleCategories
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section SelfModuleCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

/-- Every monoidal category `C` is a left module category over itself, with action given by
tensor product. -/
instance selfLeftModuleCategory : LeftModuleCategory C C where
  actObj X Y := X ⊗ Y
  actWhiskerLeft X {M₁ M₂} f := X ◁ f
  actWhiskerRight {X₁ X₂} f N := f ▷ N
  actAssociator X Y N := α_ X Y N
  actLeftUnitor N := λ_ N
  actTensorHom_def _ _ := rfl
  actId_tensorHom_id X N := by simp
  actTensorHom_comp f₁ g₁ f₂ g₂ := by

    slice_lhs 2 3 => rw [whisker_exchange]
    simp [assoc, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  actWhiskerLeft_id X N := by simp
  actId_whiskerRight X N := by simp
  actAssociator_naturality f g h := by

    rw [← MonoidalCategory.tensorHom_def (f ⊗ₘ g) h]
    rw [← MonoidalCategory.tensorHom_def g h]
    rw [← MonoidalCategory.tensorHom_def f (g ⊗ₘ h)]
    exact associator_naturality f g h
  actLeftUnitor_naturality f := leftUnitor_naturality f
  actPentagon X Y Z N := pentagon X Y Z N
  actTriangle X N := triangle X N

end SelfModuleCategory

section SelfExactModuleCategory


variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

/-- When `C` preserves projectives under tensoring, the self-module structure of `C` over itself
is an exact module category. -/
instance selfExactModuleCategory [TensorPreservesProjective C] :
    ExactModuleCategory C C where
  action_preserves_projective P N :=
    TensorPreservesProjective.tensor_projective P N

end SelfExactModuleCategory
end CategoryTheory
