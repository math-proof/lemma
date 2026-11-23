/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Functor
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Abbrev.v1.Atlas.TensorCategories.code.RigidMonoidalDuality.Part2
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits MonoidalOpposite Opposite

public section

universe v u


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]


section Def_1_10_11

example [RigidCategory C] (X : C) : HasRightDual X := inferInstance

example [RigidCategory C] (X : C) : HasLeftDual X := inferInstance

end Def_1_10_11
end TensorCategories
