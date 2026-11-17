/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Abelian.Basic
public import Def.v1.Atlas.TensorCategories.code.TensorExact
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Opposite

public section

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
