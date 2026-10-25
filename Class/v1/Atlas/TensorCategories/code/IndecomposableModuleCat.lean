/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IndecomposableModuleCat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.DirectSumModuleCategory.Part2
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Def.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
set_option maxHeartbeats 800000

open CategoryTheory

universe u₁ v₁ u₂ v₂


namespace CategoryTheory

/-- A module category `M` over a monoidal category `C` is indecomposable if whenever it is
equivalent (as a `C`-module category) to a direct sum `M₁ × M₂`, one of the summands is empty. -/
class IsIndecomposableModuleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] : Prop where
  indecomp : ∀ (M₁ M₂ : Type u₂) [Category.{v₂} M₁] [Category.{v₂} M₂]
    [LeftModuleCategory C M₁] [LeftModuleCategory C M₂]
    (_ : ModuleEquivalence C M (M₁ × M₂)), IsEmpty M₁ ∨ IsEmpty M₂

end CategoryTheory
