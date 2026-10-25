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
import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefs
set_option maxHeartbeats 400000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- An algebra `A` in the category `C` is called exact if the module category `Mod_C(A)`
is exact. -/
abbrev Definition_2_9_21_ExactAlgebra (A : C) [MonObj A]
    [LeftModuleCategory C (RightMod_ (A := A))] : Prop :=
  IsExactAlgebra A

end CategoryTheory
