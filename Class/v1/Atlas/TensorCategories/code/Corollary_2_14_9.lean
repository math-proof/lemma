/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_2_14_9.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.DualCatDefs
import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Simple
set_option maxHeartbeats 400000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory ModFun Limits

/-- A left module category `M` over a monoidal category `C` is indecomposable if it is
nonzero and does not decompose as a product of two nonzero module categories. -/
class IsIndecomposableModuleCategory'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] : Prop where
  nonzero' : ¬ IsZeroCategory M
  indecomposable' : ∀ (M₁ M₂ : Type u₂) [Category.{v₂} M₁] [Category.{v₂} M₂]
    [LeftModuleCategory' C M₁] [LeftModuleCategory' C M₂]
    [LeftModuleCategory' C (M₁ × M₂)]
    (_ : ModuleEquivalence' C M (M₁ × M₂)), IsZeroCategory M₁ ∨ IsZeroCategory M₂

end CategoryTheory
