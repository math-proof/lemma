/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IndecomposableModuleCat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.DirectSumModuleCategory.Part2
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
set_option maxHeartbeats 800000

open CategoryTheory

universe u₁ v₁ u₂ v₂


namespace CategoryTheory

/-- A category is a zero category if every one of its objects is a zero object. -/
def IsZeroCategory (M : Type*) [Category M] : Prop :=
  ∀ X : M, Limits.IsZero X

end CategoryTheory
