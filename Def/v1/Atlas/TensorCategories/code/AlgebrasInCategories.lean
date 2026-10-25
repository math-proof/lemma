/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Structure.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part2
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

attribute [reassoc (attr := simp)] RightModObj.act_unit RightModObj.act_assoc

variable {A}

/-- A morphism `l : M₁ → M₂` between right `A`-modules `(M₁, p₁)` and `(M₂, p₂)` is an
`A`-module homomorphism if it intertwines the right actions. -/
def IsRightModHom {M₁ M₂ : C} (p₁ : RightModObj A M₁) (p₂ : RightModObj A M₂)
    (l : M₁ ⟶ M₂) : Prop :=
  p₁.act ≫ l = (l ▷ A) ≫ p₂.act

end CategoryTheory
