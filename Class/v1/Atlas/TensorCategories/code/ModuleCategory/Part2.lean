/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

/-- The bare data of a left module category over `C`: the action bifunctor `actObj`, its
whiskerings and tensor of morphisms, the associator `actAssociator`, and the left unitor
`actLeftUnitor`, without the coherence axioms. -/
class LeftModuleCategoryStruct (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] where
  actObj : C → M → M
  actWhiskerLeft (X : C) {M₁ M₂ : M} (f : M₁ ⟶ M₂) : actObj X M₁ ⟶ actObj X M₂
  actWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (N : M) : actObj X₁ N ⟶ actObj X₂ N
  actTensorHom {X₁ X₂ : C} {M₁ M₂ : M} (f : X₁ ⟶ X₂) (g : M₁ ⟶ M₂) :
      actObj X₁ M₁ ⟶ actObj X₂ M₂ :=
    actWhiskerRight f M₁ ≫ actWhiskerLeft X₂ g
  actAssociator : ∀ (X Y : C) (N : M),
    actObj (X ⊗ Y) N ≅ actObj X (actObj Y N)
  actLeftUnitor : ∀ (N : M), actObj (𝟙_ C) N ≅ N

end CategoryTheory
