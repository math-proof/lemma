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
import Structure.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part3
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

attribute [reassoc (attr := simp)] RightModObj.act_unit RightModObj.act_assoc

variable {A}

attribute [reassoc (attr := simp)] RightMod_.Hom.comm

namespace RightMod_

/-- The identity morphism on a right `A`-module `M`. -/
@[simps]
def id (M : RightMod_ A) : Hom M M where
  hom := 𝟙 M.X

/-- Composition of two right `A`-module morphisms. -/
@[simps]
def comp {M N K : RightMod_ A} (f : Hom M N) (g : Hom N K) : Hom M K where
  hom := f.hom ≫ g.hom
  comm := by simp [comp_whiskerRight, reassoc_of% f.comm]

end RightMod_
end CategoryTheory
