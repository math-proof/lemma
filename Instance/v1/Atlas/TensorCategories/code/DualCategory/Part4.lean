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
import Theorem.v1.Atlas.TensorCategories.code.DualCategory.Part7
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

/-- Left whiskering preserves isomorphisms: if `f : A ⟶ B` is an isomorphism in `M` then
so is `X ◁ᵐ f`. -/
instance actWhiskerLeft_isIso (X : C) {A B : M} (f : A ⟶ B) [IsIso f] :
    IsIso (X ◁ᵐ f) where
  out := ⟨X ◁ᵐ inv f, by
    constructor
    · rw [← actWhiskerLeft_comp, IsIso.hom_inv_id,
          LeftModuleCategory.actWhiskerLeft_id]
    · rw [← actWhiskerLeft_comp, IsIso.inv_hom_id,
          LeftModuleCategory.actWhiskerLeft_id]⟩

end DualCatObj
end CategoryTheory
