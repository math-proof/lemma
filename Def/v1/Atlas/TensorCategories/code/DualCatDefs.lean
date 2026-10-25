/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCatDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TensorCategories.code.ModuleFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Logic.UnivLE
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory ModFun

/-- Underlying type of objects of the dual category `C*_M`: module endofunctors of `M`. -/
def DualCatObj'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] :=
  ModuleFunctor' C M M

/-- The property that the module category `M` over `C` is exact: tensoring any object of
`M` with a projective object of `C` yields a projective object. -/
def IsExactModuleCategory'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] : Prop :=
  ∀ (P : C) (N : M), Projective P → Projective (P ⊗ᵐ N)

end CategoryTheory
