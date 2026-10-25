/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_5_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Category.Basic
import Structure.v1.Atlas.TensorCategories.code.Definition_2_5_4
open CategoryTheory MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

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

end CategoryTheory
