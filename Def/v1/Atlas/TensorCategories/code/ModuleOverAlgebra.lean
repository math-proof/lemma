/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleOverAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Structure.v1.Atlas.TensorCategories.code.ModuleOverAlgebra
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [reassoc (attr := simp)] Definition_2_9_5.act_assoc Definition_2_9_5.act_unit

/-- The predicate that a morphism `l : M₁ ⟶ M₂` commutes with the right `A`-module actions
on `M₁` and `M₂`, i.e. `p₁.act ≫ l = (l ▷ A) ≫ p₂.act`. -/
def IsAModuleHom {A : C} [MonObj A] {M₁ M₂ : C}
    (p₁ : Definition_2_9_5 A M₁) (p₂ : Definition_2_9_5 A M₂) (l : M₁ ⟶ M₂) : Prop :=
  p₁.act ≫ l = (l ▷ A) ≫ p₂.act

end CategoryTheory
