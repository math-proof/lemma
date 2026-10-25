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
import Theorem.v1.Atlas.TensorCategories.code.AlgebrasInCategories
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

/-- The data of a right `A`-module structure on an object `M : C`: a right action
`act : M ⊗ A → M` compatible with the unit and multiplication of the algebra `A`. -/
structure RightModObj (M : C) where
  act : M ⊗ A ⟶ M
  act_unit : (M ◁ η[A]) ≫ act = (ρ_ M).hom := by aesop_cat
  act_assoc : (act ▷ A) ≫ act = (α_ M A A).hom ≫ (M ◁ μ[A]) ≫ act := by aesop_cat

end CategoryTheory
