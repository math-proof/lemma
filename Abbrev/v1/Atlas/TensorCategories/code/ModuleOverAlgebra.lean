/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleOverAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Structure.v1.Atlas.TensorCategories.code.ModuleOverAlgebra.Part2
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [reassoc (attr := simp)] Definition_2_9_5.act_assoc Definition_2_9_5.act_unit

attribute [reassoc] AModuleHom.comm

/-- Alias for `AModuleHom` matching the textbook numbering of Definition 2.9.6 (morphisms
of right `A`-modules) in EGNO. -/
abbrev Definition_2_9_6 {A : C} [MonObj A] {M₁ M₂ : C}
    (p₁ : Definition_2_9_5 A M₁) (p₂ : Definition_2_9_5 A M₂) :=
  AModuleHom p₁ p₂

end CategoryTheory
