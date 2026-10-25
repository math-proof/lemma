/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SubquotientRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
set_option maxHeartbeats 400000

open CategoryTheory CategoryTheory.ExactModuleCategory MonoidalCategory Limits

universe u₁ v₁ u₂ v₂


/-- The subtype of simple objects of `M`, packaging an object together with its `Simple` instance. -/
abbrev SimpleObj (M : Type u₂) [Category.{v₂} M] [HasZeroMorphisms M] :=
  { X : M // Simple X }

