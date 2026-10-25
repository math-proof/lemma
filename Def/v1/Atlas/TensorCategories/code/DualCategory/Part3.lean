/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Theorem.v1.Atlas.TensorCategories.code.DualCategory.Part2
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

namespace DualCatObj

variable {C M}

attribute [reassoc] Hom.comm

/-- The identity module endofunctor of `M`, which serves as the monoidal unit of the
dual category. -/
def idModuleFunctor : DualCatObj C M :=
  { toFunctor := 𝟭 M
    strIso := fun _ _ => Iso.refl _
    strIso_natural := fun f g => by
      dsimp [Iso.refl]
      simp
    strIso_assoc := fun X Y N => by
      dsimp [Iso.refl]
      simp
    strIso_unit := fun N => by
      dsimp [Iso.refl]
      simp }

/-- Composition of two module endofunctors of `M`, giving the tensor product in the
dual category `C*_M`. -/
def compModuleFunctor (F₁ F₂ : DualCatObj C M) : DualCatObj C M :=
  { toFunctor := F₁.toFunctor ⋙ F₂.toFunctor
    strIso := fun X N =>
      (F₂.toFunctor.mapIso (F₁.strIso X N)).trans (F₂.strIso X (F₁.toFunctor.obj N))
    strIso_natural := fun {X₁ X₂ N₁ N₂} f g => by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, assoc]
      rw [← F₂.toFunctor.map_comp_assoc, F₁.strIso_natural,
          F₂.toFunctor.map_comp, assoc, F₂.strIso_natural]
    strIso_assoc := fun X Y N => by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, assoc]


      have whisker_comp : X ◁ᵐ (F₂.toFunctor.map (F₁.strIso Y N).hom ≫
          (F₂.strIso Y (F₁.toFunctor.obj N)).hom) =
        X ◁ᵐ F₂.toFunctor.map (F₁.strIso Y N).hom ≫
          X ◁ᵐ (F₂.strIso Y (F₁.toFunctor.obj N)).hom := by
        have h := LeftModuleCategory.actTensorHom_comp (𝟙 X)
          (F₂.toFunctor.map (F₁.strIso Y N).hom) (𝟙 X)
          ((F₂.strIso Y (F₁.toFunctor.obj N)).hom)
        simp [LeftModuleCategory.actTensorHom_def,
              LeftModuleCategory.actId_whiskerRight] at h
        exact h.symm
      rw [whisker_comp]

      have nat_s₂ : (F₂.strIso X (F₁.toFunctor.obj (Y ⊗ᵐ N))).hom ≫
          X ◁ᵐ F₂.toFunctor.map (F₁.strIso Y N).hom =
        F₂.toFunctor.map (X ◁ᵐ (F₁.strIso Y N).hom) ≫
          (F₂.strIso X (Y ⊗ᵐ F₁.toFunctor.obj N)).hom := by
        have := F₂.strIso_natural (𝟙 X) (F₁.strIso Y N).hom
        simp [LeftModuleCategory.actId_whiskerRight] at this
        exact this.symm
      slice_lhs 3 4 => rw [nat_s₂]
      simp only [assoc]

      rw [← F₂.toFunctor.map_comp_assoc, ← F₂.toFunctor.map_comp_assoc]

      have inner : (F₁.toFunctor.map (actμ_ X Y N).hom ≫ (F₁.strIso X (Y ⊗ᵐ N)).hom) ≫
          X ◁ᵐ (F₁.strIso Y N).hom =
        (F₁.strIso (X ⊗ Y) N).hom ≫ (actμ_ X Y (F₁.toFunctor.obj N)).hom := by
        rw [assoc]; exact F₁.strIso_assoc X Y N
      rw [show F₂.toFunctor.map ((F₁.toFunctor.map (actμ_ X Y N).hom ≫
          (F₁.strIso X (Y ⊗ᵐ N)).hom) ≫ X ◁ᵐ (F₁.strIso Y N).hom) =
        F₂.toFunctor.map ((F₁.strIso (X ⊗ Y) N).hom ≫
          (actμ_ X Y (F₁.toFunctor.obj N)).hom) from congr_arg F₂.toFunctor.map inner]
      rw [F₂.toFunctor.map_comp, assoc]
      congr 1
      exact F₂.strIso_assoc X Y (F₁.toFunctor.obj N)
    strIso_unit := fun N => by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, assoc]
      rw [F₁.strIso_unit, F₂.toFunctor.map_comp]
      congr 1
      exact F₂.strIso_unit (F₁.toFunctor.obj N) }

/-- Left whiskering of a morphism `α : G₁ ⟶ G₂` by a module endofunctor `F`, giving a
morphism `F ⊗ G₁ ⟶ F ⊗ G₂` in `DualCatObj C M`. -/
def dualWhiskerLeft (F : DualCatObj C M) {G₁ G₂ : DualCatObj C M} (α : G₁ ⟶ G₂) :
    compModuleFunctor F G₁ ⟶ compModuleFunctor F G₂ where
  natTrans :=
    { app := fun N => α.natTrans.app (F.toFunctor.obj N)
      naturality := fun N₁ N₂ f => α.natTrans.naturality (F.toFunctor.map f) }
  comm X N := by
    simp only [compModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, assoc]
    rw [← α.natTrans.naturality_assoc, α.comm]

/-- Right whiskering of a morphism `α : F₁ ⟶ F₂` by a module endofunctor `G`, giving a
morphism `F₁ ⊗ G ⟶ F₂ ⊗ G` in `DualCatObj C M`. -/
def dualWhiskerRight {F₁ F₂ : DualCatObj C M} (α : F₁ ⟶ F₂) (G : DualCatObj C M) :
    compModuleFunctor F₁ G ⟶ compModuleFunctor F₂ G where
  natTrans :=
    { app := fun N => G.toFunctor.map (α.natTrans.app N)
      naturality := fun N₁ N₂ f => by
        dsimp [compModuleFunctor]
        rw [← G.toFunctor.map_comp, ← G.toFunctor.map_comp]
        congr 1; exact α.natTrans.naturality f }
  comm X N := by
    simp only [compModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, assoc]


    rw [← G.toFunctor.map_comp_assoc, α.comm, G.toFunctor.map_comp, assoc]


    congr 1

    have := G.strIso_natural (𝟙 X) (α.natTrans.app N)
    simp [LeftModuleCategory.actId_whiskerRight] at this
    exact this

/-- Reducible alias for the category structure on `DualCatObj C M`. -/
@[reducible]
def dualCategory : Category (DualCatObj C M) := categoryInstance

end DualCatObj
end CategoryTheory
