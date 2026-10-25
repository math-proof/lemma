/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ConcreteModuleCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Theorem.v1.Atlas.TensorCategories.code.DeligneTensorProductMonoidal
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section SelfModuleCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

/-- The left-whiskering map used to view a monoidal category `C` as a left module category
over itself: takes `f : M₁ ⟶ M₂` to `X ◁ f : X ⊗ M₁ ⟶ X ⊗ M₂`. -/
abbrev selfActWhiskerLeft (X : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) : X ⊗ M₁ ⟶ X ⊗ M₂ := X ◁ f

end SelfModuleCategory
end CategoryTheory
