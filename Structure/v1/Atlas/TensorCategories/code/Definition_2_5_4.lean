/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_5_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Category.Basic
open CategoryTheory MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

/-- Raw data of a `(C, D)`-bimodule category structure on `M`: left and right action
functors together with associator and unitor isomorphisms, including a middle
interchange isomorphism between the two actions. -/
structure BimoduleCategoryData
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D]
    (M : Type u₃) [Category.{v₃} M] where
  lactObj : C → M → M
  ractObj : M → D → M
  lactWhiskerLeft : ∀ (X : C) {N₁ N₂ : M}, (N₁ ⟶ N₂) → (lactObj X N₁ ⟶ lactObj X N₂)
  lactWhiskerRight : ∀ {X₁ X₂ : C}, (X₁ ⟶ X₂) → (N : M) → (lactObj X₁ N ⟶ lactObj X₂ N)
  ractWhiskerLeft : ∀ {N₁ N₂ : M}, (N₁ ⟶ N₂) → (Y : D) → (ractObj N₁ Y ⟶ ractObj N₂ Y)
  ractWhiskerRight : ∀ (N : M) {Y₁ Y₂ : D}, (Y₁ ⟶ Y₂) → (ractObj N Y₁ ⟶ ractObj N Y₂)
  lactAssociator : ∀ (X Y : C) (N : M), lactObj (X ⊗ Y) N ≅ lactObj X (lactObj Y N)
  lactLeftUnitor : ∀ (N : M), lactObj (𝟙_ C) N ≅ N
  ractAssociator : ∀ (N : M) (X Y : D), ractObj (ractObj N X) Y ≅ ractObj N (X ⊗ Y)
  ractRightUnitor : ∀ (N : M), ractObj N (𝟙_ D) ≅ N
  middleInterchange : ∀ (X : C) (N : M) (Y : D),
    ractObj (lactObj X N) Y ≅ lactObj X (ractObj N Y)

end CategoryTheory
