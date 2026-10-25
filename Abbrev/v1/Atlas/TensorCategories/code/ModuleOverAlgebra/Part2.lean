/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleOverAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Monoidal.Mon_
import Def.v1.Atlas.TensorCategories.code.ModuleOverAlgebra.Part2
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [reassoc (attr := simp)] Definition_2_9_5.act_assoc Definition_2_9_5.act_unit

attribute [reassoc] AModuleHom.comm

/-- Alias for `IsMod_Hom` matching the textbook numbering of Definition 2.9.6 in the
left-module setting, expressed via Mathlib's `ModObj` typeclass. -/
abbrev Definition_2_9_6_left (A : C) [MonObj A] {M N : C}
    [ModObj A M] [ModObj A N] (f : M ⟶ N) :=
  IsMod_Hom A f

#check @Definition_2_9_5
#check @AModuleHom
#check @Definition_2_9_6
#check @Definition_2_9_6_left

end CategoryTheory
