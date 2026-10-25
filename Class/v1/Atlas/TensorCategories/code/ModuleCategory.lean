/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

/-- Definition 2.1.1 (EGNO): A left module category over a monoidal category `C` is a category
`M` equipped with a bifunctorial action `⊗ : C × M → M`, an associator natural isomorphism
`(X ⊗ Y) ⊗ N ≅ X ⊗ (Y ⊗ N)`, and a unit functor `𝟙_C ⊗ -` that is an equivalence, satisfying
the pentagon coherence axiom. -/
class Definition_2_1_1_LeftModuleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] where
  actObj : C → M → M
  actWhiskerLeft (X : C) {M₁ M₂ : M} (f : M₁ ⟶ M₂) : actObj X M₁ ⟶ actObj X M₂
  actWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (N : M) : actObj X₁ N ⟶ actObj X₂ N
  actTensorHom {X₁ X₂ : C} {M₁ M₂ : M} (f : X₁ ⟶ X₂) (g : M₁ ⟶ M₂) :
      actObj X₁ M₁ ⟶ actObj X₂ M₂ :=
    actWhiskerRight f M₁ ≫ actWhiskerLeft X₂ g
  actAssociator : ∀ (X Y : C) (N : M),
    actObj (X ⊗ Y) N ≅ actObj X (actObj Y N)
  unitActFunctor : M ⥤ M
  unitActFunctor_obj : ∀ (N : M), unitActFunctor.obj N = actObj (𝟙_ C) N
  unitActEquivalence : unitActFunctor.IsEquivalence
  actWhiskerLeft_id : ∀ (X : C) (N : M), actWhiskerLeft X (𝟙 N) = 𝟙 (actObj X N) := by
    aesop_cat
  actId_whiskerRight : ∀ (X : C) (N : M), actWhiskerRight (𝟙 X) N = 𝟙 (actObj X N) := by
    aesop_cat
  actAssociator_naturality :
      ∀ {X₁ X₂ : C} {Y₁ Y₂ : C} {M₁ M₂ : M}
        (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) (h : M₁ ⟶ M₂),
      actTensorHom (f ⊗ₘ g) h ≫ (actAssociator X₂ Y₂ M₂).hom =
        (actAssociator X₁ Y₁ M₁).hom ≫ actTensorHom f (actTensorHom g h) := by
    aesop_cat
  actPentagon : ∀ (X Y Z : C) (N : M),
      actWhiskerRight (α_ X Y Z).hom N ≫ (actAssociator X (Y ⊗ Z) N).hom ≫
        actWhiskerLeft X (actAssociator Y Z N).hom =
        (actAssociator (X ⊗ Y) Z N).hom ≫ (actAssociator X Y (actObj Z N)).hom := by
    aesop_cat

end CategoryTheory
