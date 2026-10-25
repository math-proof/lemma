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
import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

attribute [reassoc (attr := simp)] RightModObj.act_unit RightModObj.act_assoc

variable {A}

/-- A morphism in the category of right `A`-modules: an underlying morphism `hom` in `C`
that intertwines the right `A`-actions on the source and target. -/
@[ext]
structure RightMod_.Hom (M N : RightMod_ A) where
  hom : M.X ⟶ N.X
  comm : M.mod.act ≫ hom = (hom ▷ A) ≫ N.mod.act := by aesop_cat

end CategoryTheory
