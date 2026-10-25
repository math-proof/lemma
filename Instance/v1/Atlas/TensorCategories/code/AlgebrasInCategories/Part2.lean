/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part3
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

attribute [reassoc (attr := simp)] RightModObj.act_unit RightModObj.act_assoc

variable {A}

attribute [reassoc (attr := simp)] RightMod_.Hom.comm

namespace RightMod_

/-- The category `RightMod_ A` of right `A`-modules carries a canonical structure of a
left `C`-module category, with action `(X, M) ↦ X ⊗ M` and the natural associativity and
unit constraints. -/
instance actLeftModuleCategory :
    LeftModuleCategory C (RightMod_ (A := A)) where
  actObj X M := ⟨X ⊗ M.X, tensorModObj X M⟩
  actWhiskerLeft X {_ _} f := actWhiskerLeft X f
  actWhiskerRight {_ _} f N := actWhiskerRight f N
  actTensorHom f g := actTensorHom f g
  actAssociator X Y N := actAssociator X Y N
  actLeftUnitor N := actLeftUnitor N
  actTensorHom_def f g := by
    apply hom_ext
    simp [actTensorHom, actWhiskerRight, actWhiskerLeft]
  actWhiskerLeft_id X N := by
    apply hom_ext
    simp [actWhiskerLeft]
  actId_whiskerRight X N := by
    apply hom_ext
    simp [actWhiskerRight]
  actId_tensorHom_id X N := by
    apply hom_ext
    simp [actTensorHom]
  actTensorHom_comp f₁ g₁ f₂ g₂ := by
    apply hom_ext
    simp [actTensorHom, comp_whiskerRight, whiskerLeft_comp, whisker_exchange_assoc]
  actAssociator_naturality {X₁ X₂ Y₁ Y₂} {M₁ M₂} f g h := by
    apply hom_ext
    show ((f ⊗ₘ g) ▷ M₁.X ≫ (X₂ ⊗ Y₂) ◁ h.hom) ≫ (α_ X₂ Y₂ M₂.X).hom =
      (α_ X₁ Y₁ M₁.X).hom ≫ (f ▷ (Y₁ ⊗ M₁.X) ≫ X₂ ◁ (g ▷ M₁.X ≫ Y₂ ◁ h.hom))
    rw [← MonoidalCategory.tensorHom_def, ← MonoidalCategory.tensorHom_def,
        ← MonoidalCategory.tensorHom_def]
    exact associator_naturality f g h.hom
  actLeftUnitor_naturality f := by
    apply hom_ext
    simp [actWhiskerLeft, actLeftUnitor]
  actPentagon X Y Z N := by
    apply hom_ext
    dsimp only [comp_hom', actWhiskerRight, actAssociator, actWhiskerLeft]
    exact pentagon X Y Z N.X
  actTriangle X N := by
    apply hom_ext
    dsimp only [comp_hom', actWhiskerRight, actAssociator, actWhiskerLeft, actLeftUnitor]
    exact triangle X N.X

end RightMod_
end CategoryTheory
