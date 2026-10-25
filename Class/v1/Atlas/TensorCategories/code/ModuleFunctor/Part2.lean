/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Notation.v1.Atlas.TensorCategories.code.ModuleFunctor
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

open ModFun

/-- A primed variant of `LeftModuleCategory`: extends `LeftModuleCategoryStruct'` with the
full set of coherence axioms (bifunctoriality, pentagon, triangle and unitor naturality)
for a left `C`-module category. -/
class LeftModuleCategory' (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] extends LeftModuleCategoryStruct' C M where
  actTensorHom_def {X₁ X₂ : C} {M₁ M₂ : M} (f : X₁ ⟶ X₂) (g : M₁ ⟶ M₂) :
      actTensorHom f g = actWhiskerRight f M₁ ≫ actWhiskerLeft X₂ g := by
    rfl
  actId_tensorHom_id : ∀ (X : C) (N : M),
      actTensorHom (𝟙 X) (𝟙 N) = 𝟙 (X ⊗ᵐ N) := by
    aesop_cat
  actTensorHom_comp : ∀ {X₁ X₂ X₃ : C} {M₁ M₂ M₃ : M}
      (f₁ : X₁ ⟶ X₂) (g₁ : M₁ ⟶ M₂) (f₂ : X₂ ⟶ X₃) (g₂ : M₂ ⟶ M₃),
      actTensorHom f₁ g₁ ≫ actTensorHom f₂ g₂ = actTensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) := by
    aesop_cat
  actWhiskerLeft_id : ∀ (X : C) (N : M), X ◁ᵐ 𝟙 N = 𝟙 (X ⊗ᵐ N) := by
    aesop_cat
  actId_whiskerRight : ∀ (X : C) (N : M), (𝟙 X) ▷ᵐ N = 𝟙 (X ⊗ᵐ N) := by
    aesop_cat
  actAssociator_naturality :
      ∀ {X₁ X₂ : C} {Y₁ Y₂ : C} {M₁ M₂ : M}
        (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : M₁ ⟶ M₂),
      actTensorHom (f ⊗ₘ g) h ≫ (actμ_ X₂ Y₂ M₂).hom =
        (actμ_ X₁ Y₁ M₁).hom ≫ actTensorHom f (actTensorHom g h) := by
    aesop_cat
  actLeftUnitor_naturality :
      ∀ {M₁ M₂ : M} (f : M₁ ⟶ M₂),
      (𝟙_ C) ◁ᵐ f ≫ (actℓ_ M₂).hom = (actℓ_ M₁).hom ≫ f := by
    aesop_cat
  actPentagon : ∀ (X Y Z : C) (N : M),
      (α_ X Y Z).hom ▷ᵐ N ≫ (actμ_ X (Y ⊗ Z) N).hom ≫ X ◁ᵐ (actμ_ Y Z N).hom =
        (actμ_ (X ⊗ Y) Z N).hom ≫ (actμ_ X Y (Z ⊗ᵐ N)).hom := by
    aesop_cat
  actTriangle : ∀ (X : C) (N : M),
      (actμ_ X (𝟙_ C) N).hom ≫ X ◁ᵐ (actℓ_ N).hom = (ρ_ X).hom ▷ᵐ N := by
    aesop_cat

end CategoryTheory
