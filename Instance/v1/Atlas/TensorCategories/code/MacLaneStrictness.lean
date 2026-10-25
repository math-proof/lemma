/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.Free.Basic
import Class.v1.Atlas.TensorCategories.code.MacLaneStrictness
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


namespace EGNO.MacLaneStrictness

section EndofunctorStrict

universe v u

variable (C : Type u) [Category.{v} C]

attribute [local instance] endofunctorMonoidalCategory

/-- The monoidal category of endofunctors of `C` is strict: tensor product is composition,
the unit is the identity functor, and all structure isomorphisms are identities. -/
instance endofunctorMonoidalCategory_isStrict :
    @MonoidalCategory.IsStrict (C ⥤ C) _ (endofunctorMonoidalCategory C) where
  tensorObj_assoc _ _ _ := rfl
  tensorUnit_left _ := rfl
  tensorUnit_right _ := rfl
  associator_eqToHom _ _ _ := by ext X; simp
  leftUnitor_eqToHom _ := by ext X; simp
  rightUnitor_eqToHom _ := by ext X; simp

end EndofunctorStrict
end EGNO.MacLaneStrictness
