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
set_option maxHeartbeats 400000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Convenient abbreviation: an algebra structure on an object `A : C` is a `MonObj A`. -/
abbrev AlgebraObj (A : C) := MonObj A

/-- Convenient abbreviation: a left module structure on `M : C` over the algebra `A` is a
`ModObj A M`. -/
abbrev LeftModObj (A : C) [MonObj A] (M : C) := ModObj A M

/-- Two algebras `A` and `B` in `C` are Morita equivalent if the module categories `Mod_C(A)`
and `Mod_C(B)` are module equivalent. -/
abbrev Definition_2_9_18_MoritaEquivalent (A B : C) [MonObj A] [MonObj B] : Prop :=
  MoritaEquivalent A B

end CategoryTheory
