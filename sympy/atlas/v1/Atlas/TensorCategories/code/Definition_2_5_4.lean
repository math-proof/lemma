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

/-- Definition 2.5.4: a `(C, D)`-bimodule category is a category `M` equipped with
left- and right-action data satisfying the bimodule pentagon and triangle coherence
axioms, including the two mixed pentagons relating left and right actions through the
middle interchange. -/
class Definition_2_5_4_BimoduleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D]
    (M : Type u₃) [Category.{v₃} M]
    extends BimoduleCategoryData C D M where
  leftPentagon : ∀ (X Y Z : C) (N : M),
    (lactWhiskerRight (α_ X Y Z).hom N) ≫
    (lactAssociator X (Y ⊗ Z) N).hom ≫
    (lactWhiskerLeft X (lactAssociator Y Z N).hom) =
    (lactAssociator (X ⊗ Y) Z N).hom ≫
    (lactAssociator X Y (lactObj Z N)).hom
  leftTriangle : ∀ (X : C) (N : M),
    (lactAssociator X (𝟙_ C) N).hom ≫
    (lactWhiskerLeft X (lactLeftUnitor N).hom) =
    (lactWhiskerRight (ρ_ X).hom N)
  rightPentagon : ∀ (N : M) (X Y Z : D),
    (ractWhiskerLeft (ractAssociator N X Y).hom Z) ≫
    (ractAssociator N (X ⊗ Y) Z).hom ≫
    (ractWhiskerRight N (α_ X Y Z).hom) =
    (ractAssociator (ractObj N X) Y Z).hom ≫
    (ractAssociator N X (Y ⊗ Z)).hom
  rightTriangle : ∀ (N : M) (Y : D),
    (ractAssociator N (𝟙_ D) Y).hom ≫
    (ractWhiskerRight N (λ_ Y).hom) =
    (ractWhiskerLeft (ractRightUnitor N).hom Y)
  leftMiddlePentagon : ∀ (X Y : C) (N : M) (Z : D),
    (ractWhiskerLeft (lactAssociator X Y N).hom Z) ≫
    (middleInterchange X (lactObj Y N) Z).hom ≫
    (lactWhiskerLeft X (middleInterchange Y N Z).hom) =
    (middleInterchange (X ⊗ Y) N Z).hom ≫
    (lactAssociator X Y (ractObj N Z)).hom
  rightMiddlePentagon : ∀ (X : C) (N : M) (Y Z : D),
    (ractWhiskerLeft (middleInterchange X N Y).hom Z) ≫
    (middleInterchange X (ractObj N Y) Z).hom ≫
    (lactWhiskerLeft X (ractAssociator N Y Z).hom) =
    (ractAssociator (lactObj X N) Y Z).hom ≫
    (middleInterchange X N (Y ⊗ Z)).hom

/-- Alias for `Definition_2_5_4_BimoduleCategory`: a `(C, D)`-bimodule category. -/
abbrev Definition_2_5_4 := @Definition_2_5_4_BimoduleCategory

end CategoryTheory
