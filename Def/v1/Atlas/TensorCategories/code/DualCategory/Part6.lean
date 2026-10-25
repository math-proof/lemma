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
import Theorem.v1.Atlas.TensorCategories.code.DualCategory.Part5
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

/-- Right unitor for the monoidal structure on `DualCatObj C M`, witnessing
`F ⊗ 𝟙 ≅ F`. -/
def dualRightUnitor (F : DualCatObj C M) :
    compModuleFunctor F idModuleFunctor ≅ F where
  hom := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [compModuleFunctor_right_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  inv := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [← compModuleFunctor_right_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  hom_inv_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)
  inv_hom_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)

end DualCatObj
end CategoryTheory
