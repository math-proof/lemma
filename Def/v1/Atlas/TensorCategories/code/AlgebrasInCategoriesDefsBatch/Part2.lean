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
import Abbrev.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefsBatch.Part2
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [Limits.HasCoequalizers C]

/-- Tensor product over an algebra `A`: for a right `A`-module `(M, actR)` and a left
`A`-module `(N, actL)`, the object `M ⊗_A N` is the coequalizer of the two natural maps
`M ⊗ A ⊗ N ⇒ M ⊗ N` induced by the two actions. -/
noncomputable def Definition_2_9_22_TensorOverAlgebra
    {A M N : C} (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  Limits.coequalizer
    ((α_ M A N).inv ≫ (actR ▷ N))
    (M ◁ actL)

end CategoryTheory
