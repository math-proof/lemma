/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_2_1_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.Category
set_option maxHeartbeats 3200000
set_option autoImplicit false

open CategoryTheory MonoidalCategory Category

universe v₁ v₂ u₁ u₂


/-- Data of a left `C`-module category structure on a category `M`: the action
bifunctor (split into object, left and right whiskerings), the associator and
left unitor isomorphisms, and the coherence axioms (pentagon and triangle). -/
structure ModuleCategoryData
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] where
  actObj : C → M → M
  actWhiskerLeft : (X : C) → {N₁ N₂ : M} → (N₁ ⟶ N₂) → (actObj X N₁ ⟶ actObj X N₂)
  actWhiskerRight : {X₁ X₂ : C} → (X₁ ⟶ X₂) → (N : M) → (actObj X₁ N ⟶ actObj X₂ N)
  actAssociator : ∀ (X Y : C) (N : M), actObj (X ⊗ Y) N ≅ actObj X (actObj Y N)
  actLeftUnitor : ∀ (N : M), actObj (𝟙_ C) N ≅ N
  actWhiskerLeft_id : ∀ (X : C) (N : M), actWhiskerLeft X (𝟙 N) = 𝟙 (actObj X N)
  actWhiskerLeft_comp : ∀ (X : C) {N₁ N₂ N₃ : M} (f : N₁ ⟶ N₂) (g : N₂ ⟶ N₃),
    actWhiskerLeft X (f ≫ g) = actWhiskerLeft X f ≫ actWhiskerLeft X g
  actWhiskerRight_id : ∀ (X : C) (N : M), actWhiskerRight (𝟙 X) N = 𝟙 (actObj X N)
  actWhiskerRight_comp : ∀ {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (N : M),
    actWhiskerRight (f ≫ g) N = actWhiskerRight f N ≫ actWhiskerRight g N
  actWhisker_comm : ∀ {X₁ X₂ : C} (f : X₁ ⟶ X₂) {N₁ N₂ : M} (g : N₁ ⟶ N₂),
    actWhiskerRight f N₁ ≫ actWhiskerLeft X₂ g = actWhiskerLeft X₁ g ≫ actWhiskerRight f N₂
  actLeftUnitor_naturality : ∀ {N₁ N₂ : M} (f : N₁ ⟶ N₂),
    actWhiskerLeft (𝟙_ C) f ≫ (actLeftUnitor N₂).hom = (actLeftUnitor N₁).hom ≫ f
  actAssociator_naturality_N : ∀ (X Y : C) {N₁ N₂ : M} (f : N₁ ⟶ N₂),
    actWhiskerLeft (X ⊗ Y) f ≫ (actAssociator X Y N₂).hom =
      (actAssociator X Y N₁).hom ≫ actWhiskerLeft X (actWhiskerLeft Y f)
  actPentagon : ∀ (X Y Z : C) (N : M),
    (actAssociator (X ⊗ Y) Z N).hom ≫ (actAssociator X Y (actObj Z N)).hom =
      actWhiskerRight (α_ X Y Z).hom N ≫ (actAssociator X (Y ⊗ Z) N).hom ≫
        actWhiskerLeft X (actAssociator Y Z N).hom
  actTriangle : ∀ (X : C) (N : M),
    (actAssociator X (𝟙_ C) N).hom ≫ actWhiskerLeft X (actLeftUnitor N).hom =
      actWhiskerRight (ρ_ X).hom N

/-- Data of a monoidal functor `C ⥤ (M ⥤ M)` into the endofunctor category of
`M`: the underlying functor, its unit and tensor coherence isomorphisms, and the
pentagon and triangle axioms. -/
structure MonoidalFunctorToEnd
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] where
  toFunctor : C ⥤ (M ⥤ M)
  unitIso : toFunctor.obj (𝟙_ C) ≅ 𝟭 M
  tensorIso : ∀ (X Y : C), toFunctor.obj (X ⊗ Y) ≅ toFunctor.obj Y ⋙ toFunctor.obj X
  pentagon : ∀ (X Y Z : C) (N : M),
    (toFunctor.map (α_ X Y Z).hom).app N ≫
      (tensorIso X (Y ⊗ Z)).hom.app N ≫
      (toFunctor.obj X).map ((tensorIso Y Z).hom.app N) =
    (tensorIso (X ⊗ Y) Z).hom.app N ≫ (tensorIso X Y).hom.app ((toFunctor.obj Z).obj N)
  triangle : ∀ (X : C) (N : M),
    (tensorIso X (𝟙_ C)).hom.app N ≫ (toFunctor.obj X).map (unitIso.hom.app N) =
      (toFunctor.map (ρ_ X).hom).app N

