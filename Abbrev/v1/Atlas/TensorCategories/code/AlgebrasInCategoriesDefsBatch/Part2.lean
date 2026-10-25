/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategoriesDefsBatch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefsBatch
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Top-level abbreviation for Definition 2.9.21: an algebra `A` in `C` is exact iff the
module category `Mod_C(A)` is exact. -/
abbrev Definition_2_9_21 := @Definition_2_9_21_ExactAlgebra C _ _

end CategoryTheory
