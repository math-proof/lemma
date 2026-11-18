/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Structure.v1.Atlas.TensorCategories.code.ModuleCategory
@[expose] public section

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory

open LeftModCat


/-- Alias for `ModuleNatTrans` matching the textbook numbering in EGNO. -/
abbrev Definition_2_12_1 := @ModuleNatTrans

end CategoryTheory
