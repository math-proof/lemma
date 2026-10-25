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
set_option maxHeartbeats 400000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj Limits

section TensorOverAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [HasCoequalizers C]

/-- Definition 2.9.22: the tensor product `M ⊗_A N` of a right `A`-module `M` and a
left `A`-module `N`, constructed as the coequalizer of the two natural maps
`M ⊗ A ⊗ N ⇒ M ⊗ N`. -/
noncomputable def Definition_2_9_22_TensorOverAlgebra
    {A M N : C} (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  coequalizer
    ((α_ M A N).inv ≫ (actR ▷ N))
    (M ◁ actL)

end TensorOverAlgebra
end CategoryTheory
