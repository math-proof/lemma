/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleRigidityCompat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Class.v1.Atlas.TensorCategories.code.ModuleRigidityCompat
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

namespace ExactModuleCategory

open Category MonoidalCategory LeftModCat

section AuxLemmas

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
         {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

omit [LeftRigidCategory C] in
/-- Left whiskering of a module action distributes over composition of morphisms in `M`. -/
theorem actWhiskerLeft_comp (X : C) {N₁ N₂ N₃ : M} (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃) :
    X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g := by
  have h := LeftModuleCategory.actTensorHom_comp (𝟙 X) f (𝟙 X) g
  simp only [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight,
    id_comp, comp_id] at h
  exact h.symm

end AuxLemmas
end ExactModuleCategory
end CategoryTheory
