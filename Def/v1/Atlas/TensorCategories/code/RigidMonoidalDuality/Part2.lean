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
import Theorem.v1.Atlas.TensorCategories.code.RigidMonoidalDuality
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits MonoidalOpposite Opposite

universe v u


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]


section DualityFunctor

/-- The right-duality functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` on a right-rigid category, sending each object
to its right dual. -/
def dualityFunctor_right (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RightRigidCategory C] : C ⥤ (Cᵒᵖ)ᴹᵒᵖ :=
  rightDualFunctor C

/-- The left-duality functor `C ⥤ (Cᵒᵖ)ᴹᵒᵖ` on a left-rigid category, sending each object
to its left dual. -/
def dualityFunctor_left (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [LeftRigidCategory C] : C ⥤ (Cᵒᵖ)ᴹᵒᵖ :=
  leftDualFunctor C

end DualityFunctor
end TensorCategories
