/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part3
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

open LeftModCat

attribute [reassoc] LeftModuleCategory.actTensorHom_def

attribute [reassoc, simp] LeftModuleCategory.actWhiskerLeft_id

attribute [reassoc, simp] LeftModuleCategory.actId_whiskerRight

attribute [reassoc (attr := simp)] LeftModuleCategory.actTensorHom_comp

attribute [reassoc] LeftModuleCategory.actAssociator_naturality

attribute [reassoc] LeftModuleCategory.actLeftUnitor_naturality

attribute [reassoc (attr := simp)] LeftModuleCategory.actPentagon

attribute [reassoc (attr := simp)] LeftModuleCategory.actTriangle

/-- A module functor between left `C`-module categories `M₁` and `M₂`: an underlying functor
together with a natural isomorphism `F(X ⊗ N) ≅ X ⊗ F(N)` compatible with the action
associator and left unitor. -/
structure ModuleFunctor
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂] where
  toFunctor : M₁ ⥤ M₂
  strIso : ∀ (X : C) (N : M₁), toFunctor.obj (X ⊗ᵐ N) ≅ (X ⊗ᵐ toFunctor.obj N)
  strIso_natural : ∀ {X₁ X₂ : C} {N₁ N₂ : M₁} (f : X₁ ⟶ X₂) (g : N₁ ⟶ N₂),
      toFunctor.map (f ▷ᵐ N₁ ≫ X₂ ◁ᵐ g) ≫ (strIso X₂ N₂).hom =
        (strIso X₁ N₁).hom ≫ (f ▷ᵐ toFunctor.obj N₁ ≫ X₂ ◁ᵐ toFunctor.map g)
  strIso_assoc : ∀ (X Y : C) (N : M₁),
      toFunctor.map (actμ_ X Y N).hom ≫ (strIso X (Y ⊗ᵐ N)).hom ≫
        X ◁ᵐ (strIso Y N).hom =
      (strIso (X ⊗ Y) N).hom ≫ (actμ_ X Y (toFunctor.obj N)).hom
  strIso_unit : ∀ (N : M₁),
      toFunctor.map (actℓ_ N).hom = (strIso (𝟙_ C) N).hom ≫ (actℓ_ (toFunctor.obj N)).hom

attribute [reassoc] ModuleFunctor.strIso_natural

attribute [reassoc (attr := simp)] ModuleFunctor.strIso_assoc

attribute [reassoc (attr := simp)] ModuleFunctor.strIso_unit

/-- Definition 2.12.1 (EGNO): A module natural transformation between module functors `F, G`
is an underlying natural transformation `F ⟶ G` compatible with the module structure
isomorphisms, i.e. `η_{X ⊗ N} ≫ G.strIso = F.strIso ≫ X ◁ᵐ η_N`. -/
structure ModuleNatTrans
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M₁ : Type u₂} [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    {M₂ : Type u₃} [Category.{v₃} M₂] [LeftModuleCategory C M₂]
    (F G : ModuleFunctor C M₁ M₂) where
  toNatTrans : F.toFunctor ⟶ G.toFunctor
  compatibility : ∀ (X : C) (N : M₁),
    toNatTrans.app (X ⊗ᵐ N) ≫ (G.strIso X N).hom =
      (F.strIso X N).hom ≫ X ◁ᵐ (toNatTrans.app N)

end CategoryTheory
