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
import Theorem.v1.Atlas.TensorCategories.code.DualCategory.Part8
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

/-- Identity morphism on `F` in the double-dual category, given by the identity natural
transformation. -/
def DoubleDualHom.id [inst : LeftModuleCategory (DualCatObj C M) M]
    (F : DoubleDualObj C M) : DoubleDualHom F F where
  natTrans := NatTrans.id F.toFunctor
  comm P N := by
    simp [NatTrans.id_app', LeftModuleCategory.actWhiskerLeft_id]

/-- Composition of morphisms in the double-dual category, given by the vertical
composition of the underlying natural transformations. -/
def DoubleDualHom.comp [inst : LeftModuleCategory (DualCatObj C M) M]
    {F G H : DoubleDualObj C M}
    (α : DoubleDualHom F G) (β : DoubleDualHom G H) :
    DoubleDualHom F H where
  natTrans := α.natTrans ≫ β.natTrans
  comm P N := by
    simp only [NatTrans.comp_app, assoc]
    rw [β.comm, ← assoc, α.comm, assoc]
    congr 1
    have ha : P ◁ᵐ α.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 P) (α.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hb : P ◁ᵐ β.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 P) (β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hab : P ◁ᵐ (α.natTrans.app N ≫ β.natTrans.app N) =
        LeftModuleCategoryStruct.actTensorHom (𝟙 P) (α.natTrans.app N ≫ β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    rw [ha, hb, hab, LeftModuleCategory.actTensorHom_comp, comp_id]

end DualCatObj
end CategoryTheory
