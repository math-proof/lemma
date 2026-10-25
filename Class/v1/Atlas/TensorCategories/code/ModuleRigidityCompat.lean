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
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

namespace ExactModuleCategory

open Category MonoidalCategory LeftModCat

/-- Data of evaluation and coevaluation morphisms compatible with a module action on `M`,
together with the zigzag identities relating them to the module structure on `M`. -/
class ModuleEvalCoeval
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
    (M : Type u₂) [Category.{v₂} M] [ExactModuleCategory C M] where
  modEval : ∀ (P : C), HasLeftDual.leftDual P ⊗ P ⟶ 𝟙_ C
  modCoeval : ∀ (P : C), 𝟙_ C ⟶ P ⊗ HasLeftDual.leftDual P
  zigzag_left : ∀ (P : C) (N A : M) (g : (ᘁP : C) ⊗ᵐ A ⟶ N),
    (ᘁP : C) ◁ᵐ ((actℓ_ A).inv ≫ (modCoeval P) ▷ᵐ A ≫
      (actμ_ P (ᘁP : C) A).hom ≫ P ◁ᵐ g) ≫
      (actμ_ (ᘁP : C) P N).inv ≫ (modEval P) ▷ᵐ N ≫ (actℓ_ N).hom = g
  zigzag_right : ∀ (P : C) (N A : M) (f : A ⟶ P ⊗ᵐ N),
    (actℓ_ A).inv ≫ (modCoeval P) ▷ᵐ A ≫ (actμ_ P (ᘁP : C) A).hom ≫
      P ◁ᵐ ((ᘁP : C) ◁ᵐ f ≫ (actμ_ (ᘁP : C) P N).inv ≫
        (modEval P) ▷ᵐ N ≫ (actℓ_ N).hom) = f

end ExactModuleCategory
end CategoryTheory
