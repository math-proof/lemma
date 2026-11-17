/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MacLaneStrictness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Free.Coherence
public import Mathlib.CategoryTheory.Monoidal.Free.Basic
public import Class.v1.Atlas.TensorCategories.code.MacLaneStrictness

@[expose] public section

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
