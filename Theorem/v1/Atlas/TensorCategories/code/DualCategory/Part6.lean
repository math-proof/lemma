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
import Instance.v1.Atlas.TensorCategories.code.DualCategory.Part2
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

/-- Tensor product in `DualCatObj C M` is functor composition. -/
@[simp] lemma tensorObj_eq (F G : DualCatObj C M) : F ⊗ G = compModuleFunctor F G := rfl

/-- The monoidal unit of `DualCatObj C M` is the identity module endofunctor. -/
@[simp] lemma tensorUnit_eq : (𝟙_ (DualCatObj C M)) = idModuleFunctor := rfl

/-- Left whiskering in `DualCatObj C M` agrees with `dualWhiskerLeft`. -/
@[simp] lemma whiskerLeft_eq (F : DualCatObj C M) {G₁ G₂ : DualCatObj C M} (f : G₁ ⟶ G₂) :
    F ◁ f = dualWhiskerLeft F f := rfl

/-- Right whiskering in `DualCatObj C M` agrees with `dualWhiskerRight`. -/
@[simp] lemma whiskerRight_eq {F₁ F₂ : DualCatObj C M} (f : F₁ ⟶ F₂) (G : DualCatObj C M) :
    f ▷ G = dualWhiskerRight f G := rfl

/-- The associator in `DualCatObj C M` agrees with `dualAssociator`. -/
@[simp] lemma associator_eq (F₁ F₂ F₃ : DualCatObj C M) :
    α_ F₁ F₂ F₃ = dualAssociator F₁ F₂ F₃ := rfl

/-- The left unitor in `DualCatObj C M` agrees with `dualLeftUnitor`. -/
@[simp] lemma leftUnitor_eq (F : DualCatObj C M) : λ_ F = dualLeftUnitor F := rfl

/-- The right unitor in `DualCatObj C M` agrees with `dualRightUnitor`. -/
@[simp] lemma rightUnitor_eq (F : DualCatObj C M) : ρ_ F = dualRightUnitor F := rfl

end DualCatObj
end CategoryTheory
