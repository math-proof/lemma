/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FittingLemmaLocalEnd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Endomorphism
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe v u w


namespace CategoryTheory

section EndRingStructure

variable (k : Type w) [Field k] {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- The `k`-action on `End P` commutes with right-composition by an endomorphism, so
`End P` carries a scalar tower over `k` with itself as the inner ring. -/
instance endScalarTower (P : C) : IsScalarTower k (End P) (End P) where
  smul_assoc r a b := by
    show b ≫ (r • a) = r • (b ≫ a)
    exact Linear.comp_smul P P P b r a

end EndRingStructure
end CategoryTheory
