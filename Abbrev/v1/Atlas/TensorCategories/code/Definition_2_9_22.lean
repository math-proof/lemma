/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_9_22.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Def.v1.Atlas.TensorCategories.code.Definition_2_9_22
set_option maxHeartbeats 400000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj Limits

section TensorOverAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [HasCoequalizers C]

/-- Alias of `Definition_2_9_22_TensorOverAlgebra`: the relative tensor product
`M ⊗_A N`. -/
noncomputable abbrev Definition_2_9_22
    {A M N : C} (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  Definition_2_9_22_TensorOverAlgebra actR actL

end TensorOverAlgebra
end CategoryTheory
