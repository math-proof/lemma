/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Mon_
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
public import Structure.v1.Atlas.TensorCategories.code.AlgebrasInCategories
@[expose] public section

set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (A : C) [MonObj A]

attribute [reassoc (attr := simp)] RightModObj.act_unit RightModObj.act_assoc

/-- A right module over an algebra `(A, m, u)` is a pair `(M, p)` with `M : C` and
`p : M ⊗ A → M` satisfying the unit and associativity axioms. -/
abbrev Definition_2_9_5_RightModule (M : C) := RightModObj A M

end CategoryTheory
