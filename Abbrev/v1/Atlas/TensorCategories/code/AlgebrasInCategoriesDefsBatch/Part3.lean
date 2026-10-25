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
import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefsBatch.Part2
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [Limits.HasCoequalizers C]

/-- An `A`-`B`-bimodule in a monoidal category `C` is a triple `(M, p, q)` consisting of an
object `M ∈ C`, a left `A`-action `p : A ⊗ M → M`, and a right `B`-action `q : M ⊗ B → M`
that commute appropriately. Implemented via Mathlib's `Bimod A B`. -/
abbrev Definition_2_9_24_BimoduleInMonoidalCategory (A B : Mon C) := Bimod A B

end CategoryTheory
