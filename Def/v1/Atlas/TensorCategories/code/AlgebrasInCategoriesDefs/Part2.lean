/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AlgebrasInCategoriesDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Abbrev.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefs.Part2
set_option maxHeartbeats 400000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Proposition_2_9_10

variable {A : C} [MonObj A]

/-- The category `Mod_C(A)` of right `A`-modules, equipped with the natural tensor action
of `C`, the standard associativity, and unit constraints, is a left `C`-module category. -/
def proposition_2_9_10 : LeftModuleCategory C (RightMod_ (A := A)) :=
  RightMod_.actLeftModuleCategory

end Proposition_2_9_10

variable [Limits.HasCoequalizers C]

/-- Tensor product over an algebra `A`: for a right `A`-module `(M, actR)` and a left
`A`-module `(N, actL)`, the object `M ⊗_A N` is the quotient of `M ⊗ N` by the image of
`actR ⊗ id - id ⊗ actL : M ⊗ A ⊗ N → M ⊗ N`. -/
noncomputable def Definition_2_9_22_TensorOverAlgebra
    {A M N : C} (actR : M ⊗ A ⟶ M) (actL : A ⊗ N ⟶ N) : C :=
  TensorOverAlgebra actR actL

end CategoryTheory
