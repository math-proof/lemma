/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Functor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Instance.v1.Atlas.TensorCategories.code.RigidMonoidalDuality
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits MonoidalOpposite Opposite

universe v u


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]


section Def_1_10_11

/-- Definition 1.10.11 (alias): a rigid monoidal category. -/
abbrev def_1_10_11 := @RigidCategory

/-- Definition 1.10.11: A monoidal category `C` is rigid if every object has both a right
dual and a left dual. -/
abbrev Definition_1_10_11_RigidCategory (C : Type*) [Category C] [MonoidalCategory C] :=
  RigidCategory C

end Def_1_10_11
end TensorCategories
