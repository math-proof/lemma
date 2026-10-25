/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Abelian.Basic
import Def.v1.Atlas.TensorCategories.code.TensorExact
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Opposite

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section ExactFunctors

/-- Computation: `rightAdjointMateEquiv` applied to `f` agrees with the underlying right adjoint mate. -/
theorem rightAdjointMateEquiv_apply (X Y : C) (f : X ⟶ Y) :
    rightAdjointMateEquiv X Y f = rightAdjointMate f := by
  simp only [rightAdjointMateEquiv, Equiv.trans_apply]
  dsimp [Equiv.mk]
  simp only [rightAdjointMate, tensorLeftHomEquiv, tensorRightHomEquiv]
  dsimp
  monoidal

end ExactFunctors
end CategoryTheory
