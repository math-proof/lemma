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
import Theorem.v1.Atlas.TensorCategories.code.DualCategory.Part6
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

/-- Monoidal category structure on `DualCatObj C M` packaging together the data of
`dualMonoidalCategoryStruct` with the coherence axioms (pentagon, triangle, etc.). -/
instance dualMonoidalCategory : MonoidalCategory (DualCatObj C M) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun F G => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        tensorObj_eq, id_natTrans, comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor]
      simp [Functor.map_id])
    (id_tensorHom := fun F {G₁ G₂} f => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor]
      simp)
    (tensorHom_id := fun {F₁ F₂} f G => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor]
      simp)
    (tensorHom_comp_tensorHom := fun {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor, Hom.comp]


      have nat := f₂.natTrans.naturality (g₁.natTrans.app N)

      slice_lhs 2 3 => rw [← nat]
      simp only [assoc]
      rw [← X₂.toFunctor.map_comp_assoc])
    (associator_naturality := fun {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualAssociator, dualWhiskerLeft, dualWhiskerRight, compModuleFunctor, Hom.comp]
      simp only [id_comp, comp_id]
      rw [X₃.toFunctor.map_comp, assoc])
    (leftUnitor_naturality := fun {X₁ X₂} f => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualLeftUnitor, dualWhiskerLeft, dualWhiskerRight,
             compModuleFunctor, idModuleFunctor]
      simp)
    (rightUnitor_naturality := fun {X₁ X₂} f => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualRightUnitor, dualWhiskerLeft, dualWhiskerRight,
             compModuleFunctor, idModuleFunctor]
      simp)

    (pentagon := fun W X Y Z => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualAssociator, dualWhiskerLeft, dualWhiskerRight, Hom.comp, compModuleFunctor]
      simp [Functor.map_id])
    (triangle := fun X Y => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom, comp_natTrans, NatTrans.comp_app]
      dsimp [dualAssociator, dualLeftUnitor, dualRightUnitor,
             dualWhiskerLeft, dualWhiskerRight, Hom.comp, compModuleFunctor, idModuleFunctor]
      simp [Functor.map_id])

end DualCatObj
end CategoryTheory
