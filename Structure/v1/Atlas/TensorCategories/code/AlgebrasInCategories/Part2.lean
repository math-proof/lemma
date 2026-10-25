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
import Abbrev.v1.Atlas.TensorCategories.code.AlgebrasInCategories
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

attribute [reassoc (attr := simp)] RightModObj.act_unit RightModObj.act_assoc

/-- A right module over the algebra `A` packaged as a bundled structure: an underlying
object `X : C` together with a right action `mod : RightModObj A X`. -/
structure RightMod_ where
  X : C
  mod : RightModObj A X

end CategoryTheory
