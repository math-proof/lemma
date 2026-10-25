/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Class.v1.Atlas.TensorCategories.code.ModuleCategory
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

/-- Alias for `Definition_2_1_1_LeftModuleCategory` matching the textbook numbering in EGNO. -/
abbrev Definition_2_1_1 := @Definition_2_1_1_LeftModuleCategory

end CategoryTheory
