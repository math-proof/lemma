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
import Theorem.v1.Atlas.TensorCategories.code.DualCategory
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

/-- Identity morphism on `F` in the dual category, given by the identity natural
transformation. -/
def Hom.id (F : DualCatObj C M) : Hom F F where
  natTrans := NatTrans.id F.toFunctor
  comm X N := by
    simp [NatTrans.id_app', LeftModuleCategory.actWhiskerLeft_id]

/-- Composition of morphisms in the dual category, given by the vertical composition of
the underlying natural transformations. -/
def Hom.comp {F G H : DualCatObj C M} (α : Hom F G) (β : Hom G H) :
    Hom F H where
  natTrans := α.natTrans ≫ β.natTrans
  comm X N := by
    simp only [NatTrans.comp_app, assoc]
    rw [β.comm, ← assoc, α.comm, assoc]
    congr 1

    have ha : X ◁ᵐ α.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 X) (α.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hb : X ◁ᵐ β.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 X) (β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hab : X ◁ᵐ (α.natTrans.app N ≫ β.natTrans.app N) =
        LeftModuleCategoryStruct.actTensorHom (𝟙 X) (α.natTrans.app N ≫ β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    rw [ha, hb, hab, LeftModuleCategory.actTensorHom_comp, comp_id]

end DualCatObj
end CategoryTheory
