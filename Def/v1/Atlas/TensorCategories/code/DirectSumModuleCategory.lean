/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DirectSumModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
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

end DirectSum
end CategoryTheory
