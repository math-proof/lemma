/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An algebra `A` in a multitensor category `C` is exact if the category of right
`A`-modules is an exact module category over `C` (Definition 2.9.21 of EGNO). -/
def IsExactAlgebra (A : C) [MonObj A] : Prop :=
  Nonempty (ExactModuleCategory C (RightMod_ (C := C) (A := A)))

end CategoryTheory
