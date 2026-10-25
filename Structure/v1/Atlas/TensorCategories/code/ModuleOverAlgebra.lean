/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleOverAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Monoidal.Mon_
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Definition 2.9.5 (EGNO): A right module structure on `M : C` over an algebra object
`A` consists of an action morphism `act : M ⊗ A ⟶ M` that is associative with respect to the
multiplication of `A` and unital with respect to the unit of `A`. -/
structure Definition_2_9_5 (A : C) [MonObj A] (M : C) where
  act : M ⊗ A ⟶ M
  act_assoc : (act ▷ A) ≫ act = (α_ M A A).hom ≫ (M ◁ μ[A]) ≫ act := by aesop_cat
  act_unit : (M ◁ η[A]) ≫ act = (ρ_ M).hom := by aesop_cat

end CategoryTheory
