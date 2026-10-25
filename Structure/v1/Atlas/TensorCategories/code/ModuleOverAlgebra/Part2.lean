/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleOverAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Def.v1.Atlas.TensorCategories.code.ModuleOverAlgebra
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [reassoc (attr := simp)] Definition_2_9_5.act_assoc Definition_2_9_5.act_unit

/-- A bundled module hom between two `A`-modules `(M₁, p₁)` and `(M₂, p₂)`: a morphism
`hom : M₁ ⟶ M₂` together with the commutativity condition with the actions. -/
@[ext]
structure AModuleHom {A : C} [MonObj A] {M₁ M₂ : C}
    (p₁ : Definition_2_9_5 A M₁) (p₂ : Definition_2_9_5 A M₂) where
  hom : M₁ ⟶ M₂
  comm : p₁.act ≫ hom = (hom ▷ A) ≫ p₂.act := by aesop_cat

end CategoryTheory
