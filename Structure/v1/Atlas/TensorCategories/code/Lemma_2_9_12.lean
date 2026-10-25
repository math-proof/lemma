/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_2_9_12.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mon_
set_option maxHeartbeats 400000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

/-- A right module structure on an object `M` over a monoid object `A` in a monoidal category,
consisting of an action morphism `M ⊗ A ⟶ M` compatible with the unit and multiplication of `A`. -/
structure RightModObj' (M : C) where
  act : M ⊗ A ⟶ M
  act_unit : (M ◁ η[A]) ≫ act = (ρ_ M).hom := by aesop_cat
  act_assoc : (act ▷ A) ≫ act = (α_ M A A).hom ≫ (M ◁ μ[A]) ≫ act := by aesop_cat

attribute [reassoc (attr := simp)] RightModObj'.act_unit RightModObj'.act_assoc

/-- A right `A`-module in `C`: an object `X` together with a right `A`-module structure on it. -/
structure RightMod' where
  X : C
  mod : RightModObj' A X

variable {A}

/-- A morphism of right `A`-modules: a morphism between underlying objects that intertwines
the right `A`-action. -/
@[ext]
structure RightMod'.Hom (M N : RightMod' A) where
  hom : M.X ⟶ N.X
  comm : M.mod.act ≫ hom = (hom ▷ A) ≫ N.mod.act := by aesop_cat

end CategoryTheory
