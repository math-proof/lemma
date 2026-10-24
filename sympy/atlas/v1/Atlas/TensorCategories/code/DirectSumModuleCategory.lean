/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DirectSumModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategory
import Mathlib.CategoryTheory.Products.Basic

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section DirectSum

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
variable (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]
variable (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂]

/-- Componentwise product of isomorphisms `i : A ≅ B` and `j : P ≅ Q` as an isomorphism
`(A, P) ≅ (B, Q)` in the product category `M₁ × M₂`. -/
def prodIso {A B : M₁} {P Q : M₂} (i : A ≅ B) (j : P ≅ Q) :
    @Iso (M₁ × M₂) _ (A, P) (B, Q) where
  hom := (i.hom, j.hom)
  inv := (i.inv, j.inv)
  hom_inv_id := by show (i.hom ≫ i.inv, j.hom ≫ j.inv) = (𝟙 A, 𝟙 P); simp
  inv_hom_id := by show (i.inv ≫ i.hom, j.inv ≫ j.hom) = (𝟙 B, 𝟙 Q); simp

/-- The direct sum (product) category `M₁ × M₂` inherits a `C`-left-module-category
structure with action `X ⊗ (N₁, N₂) = (X ⊗ N₁, X ⊗ N₂)`, and associators/unitors
acting componentwise. -/
instance directSumLeftModuleCategory :
    LeftModuleCategory C (M₁ × M₂) where
  actObj X N := (X ⊗ᵐ N.1, X ⊗ᵐ N.2)
  actWhiskerLeft X {A B} f := (X ◁ᵐ f.1, X ◁ᵐ f.2)
  actWhiskerRight {X₁ X₂} f N := (f ▷ᵐ N.1, f ▷ᵐ N.2)
  actTensorHom {X₁ X₂} {A B} f g :=
    (LeftModuleCategoryStruct.actTensorHom f g.1,
     LeftModuleCategoryStruct.actTensorHom f g.2)
  actAssociator X Y N := prodIso M₁ M₂ (actμ_ X Y N.1) (actμ_ X Y N.2)
  actLeftUnitor N := prodIso M₁ M₂ (actℓ_ N.1) (actℓ_ N.2)
  actTensorHom_def {X₁ X₂} {A B} f g := by
    ext <;> exact LeftModuleCategory.actTensorHom_def f _
  actId_tensorHom_id X N := by
    ext <;> exact LeftModuleCategory.actId_tensorHom_id X _
  actTensorHom_comp f₁ g₁ f₂ g₂ := by
    ext <;> exact LeftModuleCategory.actTensorHom_comp f₁ _ f₂ _
  actWhiskerLeft_id X N := by
    ext <;> exact LeftModuleCategory.actWhiskerLeft_id X _
  actId_whiskerRight X N := by
    ext <;> exact LeftModuleCategory.actId_whiskerRight X _
  actAssociator_naturality f g h := by
    ext <;> exact LeftModuleCategory.actAssociator_naturality f g _
  actLeftUnitor_naturality f := by
    ext <;> exact LeftModuleCategory.actLeftUnitor_naturality _
  actPentagon X Y Z N := by
    ext <;> exact LeftModuleCategory.actPentagon X Y Z _
  actTriangle X N := by
    ext <;> exact LeftModuleCategory.actTriangle X _

/-- Proposition 2.4.1: the direct sum `M = M₁ ⊕ M₂` of two `C`-module categories is
itself a `C`-module category, with componentwise action, associator and unitor. -/
def proposition_2_4_1 : LeftModuleCategory C (M₁ × M₂) :=
  directSumLeftModuleCategory C M₁ M₂

end DirectSum

/-- A `C`-module category `M` is the direct sum of `M₁` and `M₂` (in the sense of
Definition 2.4.2) when `M` is equivalent as a `C`-module category to the product
`M₁ × M₂` equipped with the componentwise action. -/
def IsDirectSumModuleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    (M₁ : Type u₃) [Category.{v₃} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₄) [Category.{v₄} M₂] [LeftModuleCategory C M₂] : Prop :=
  Nonempty (ModuleEquivalence C M (M₁ × M₂))

end CategoryTheory
