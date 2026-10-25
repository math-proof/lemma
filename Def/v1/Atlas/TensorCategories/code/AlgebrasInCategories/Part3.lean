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
import Theorem.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part2
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

/-- The right regular `A`-module, namely the algebra `A` viewed as a right module over
itself via its multiplication. -/
@[simps]
def regular (A : C) [MonObj A] : RightMod_ (A := A) where
  X := A
  mod := { act := μ[A] }

/-- The forgetful functor from right `A`-modules to `C`, sending a module to its
underlying object. -/
@[simps]
def forget : RightMod_ (A := A) ⥤ C where
  obj M := M.X
  map f := f.hom

/-- For `X : C` and a right `A`-module `M`, the object `X ⊗ M.X` carries a right
`A`-module structure with action `(α_).hom ≫ X ◁ M.mod.act`. -/
def tensorModObj (X : C) (M : RightMod_ A) : RightModObj A (X ⊗ M.X) where
  act := (α_ X M.X A).hom ≫ X ◁ M.mod.act
  act_unit := by
    calc (X ⊗ M.X) ◁ η ≫ (α_ X M.X A).hom ≫ X ◁ M.mod.act
        = (α_ X M.X _).hom ≫ X ◁ (M.X ◁ η) ≫ X ◁ M.mod.act := by simp [assoc]
      _ = (α_ X M.X _).hom ≫ X ◁ ((M.X ◁ η) ≫ M.mod.act) := by rw [whiskerLeft_comp]
      _ = (α_ X M.X _).hom ≫ X ◁ (ρ_ M.X).hom := by rw [M.mod.act_unit]
      _ = (ρ_ (X ⊗ M.X)).hom := (rightUnitor_tensor_hom X M.X).symm
  act_assoc := by
    rw [comp_whiskerRight, assoc]
    slice_lhs 2 3 => simp
    slice_lhs 3 4 => rw [← whiskerLeft_comp, M.mod.act_assoc]
    simp only [whiskerLeft_comp]
    slice_lhs 1 3 => rw [pentagon]
    simp [assoc]

/-- Right whiskering of `f : X₁ ⟶ X₂` by a right `A`-module `M`, viewed as a morphism
in `RightMod_ A` between the modules `X₁ ⊗ M` and `X₂ ⊗ M`. -/
def actWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (M : RightMod_ A) :
    (⟨X₁ ⊗ M.X, tensorModObj X₁ M⟩ : RightMod_ A) ⟶
    ⟨X₂ ⊗ M.X, tensorModObj X₂ M⟩ where
  hom := f ▷ M.X
  comm := by
    simp only [tensorModObj, assoc]
    rw [whisker_exchange]
    simp

/-- Left whiskering of a right `A`-module morphism `g : M ⟶ N` by an object `X : C`,
giving a morphism `X ⊗ M ⟶ X ⊗ N` in `RightMod_ A`. -/
def actWhiskerLeft (X : C) {M N : RightMod_ A} (g : M ⟶ N) :
    (⟨X ⊗ M.X, tensorModObj X M⟩ : RightMod_ A) ⟶
    ⟨X ⊗ N.X, tensorModObj X N⟩ where
  hom := X ◁ g.hom
  comm := by
    simp only [tensorModObj, assoc]
    rw [← whiskerLeft_comp, g.comm, whiskerLeft_comp]
    simp [assoc]

/-- The associator isomorphism `(X ⊗ Y) ⊗ M ≅ X ⊗ (Y ⊗ M)` in `RightMod_ A` for the
`C`-action on right `A`-modules. -/
def actAssociator (X Y : C) (M : RightMod_ A) :
    (⟨(X ⊗ Y) ⊗ M.X, tensorModObj (X ⊗ Y) M⟩ : RightMod_ A) ≅
    ⟨X ⊗ (Y ⊗ M.X), tensorModObj X ⟨Y ⊗ M.X, tensorModObj Y M⟩⟩ where
  hom := {
    hom := (α_ X Y M.X).hom
    comm := by
      simp only [tensorModObj, assoc, whiskerLeft_comp]
      slice_lhs 2 3 => rw [associator_naturality_right]
      rw [← pentagon_assoc]
  }
  inv := {
    hom := (α_ X Y M.X).inv
    comm := by
      simp only [tensorModObj, assoc, whiskerLeft_comp]
      rw [← cancel_mono (α_ X Y M.X).hom]
      simp only [assoc, Iso.inv_hom_id, comp_id]
      rw [associator_naturality_right (f := M.mod.act)]
      rw [show (α_ X Y M.X).inv ▷ A ≫ (α_ (X ⊗ Y) M.X A).hom ≫
        (α_ X Y (M.X ⊗ A)).hom ≫ X ◁ Y ◁ M.mod.act =
        (α_ X Y M.X).inv ▷ A ≫ ((α_ X Y M.X).hom ▷ A ≫
        (α_ X (Y ⊗ M.X) A).hom ≫ X ◁ (α_ Y M.X A).hom) ≫
        X ◁ Y ◁ M.mod.act from by rw [pentagon]; simp [assoc]]
      simp [assoc]
  }

/-- The left unitor isomorphism `𝟙_ C ⊗ M ≅ M` in `RightMod_ A` for the `C`-action. -/
def actLeftUnitor (M : RightMod_ A) :
    (⟨(𝟙_ C) ⊗ M.X, tensorModObj (𝟙_ C) M⟩ : RightMod_ A) ≅
    M where
  hom := {
    hom := (λ_ M.X).hom
    comm := by
      simp only [tensorModObj, assoc]
      rw [show (λ_ M.X).hom ▷ A ≫ M.mod.act =
        (α_ (𝟙_ C) M.X A).hom ≫ (𝟙_ C) ◁ M.mod.act ≫ (λ_ M.X).hom from by simp]
  }
  inv := {
    hom := (λ_ M.X).inv
    comm := by
      rw [← cancel_mono (λ_ M.X).hom]
      simp only [tensorModObj, assoc, Iso.inv_hom_id]
      simp
  }

/-- The tensor of a morphism `f : X₁ ⟶ X₂` in `C` with a morphism `g : M₁ ⟶ M₂` of right
`A`-modules, giving a morphism `X₁ ⊗ M₁ ⟶ X₂ ⊗ M₂` in `RightMod_ A`. -/
def actTensorHom {X₁ X₂ : C} {M₁ M₂ : RightMod_ A}
    (f : X₁ ⟶ X₂) (g : M₁ ⟶ M₂) :
    (⟨X₁ ⊗ M₁.X, tensorModObj X₁ M₁⟩ : RightMod_ A) ⟶
    ⟨X₂ ⊗ M₂.X, tensorModObj X₂ M₂⟩ where
  hom := f ▷ M₁.X ≫ X₂ ◁ g.hom
  comm := by
    dsimp only [tensorModObj]
    simp only [assoc]
    rw [whisker_exchange_assoc]
    rw [← whiskerLeft_comp X₂ M₁.mod.act g.hom, g.comm, whiskerLeft_comp]
    rw [comp_whiskerRight_assoc, associator_naturality_middle_assoc,
        associator_naturality_left_assoc]

end RightMod_
end CategoryTheory
