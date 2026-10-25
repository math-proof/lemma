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
import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefs.Part2
set_option maxHeartbeats 400000

universe v u


namespace CategoryTheory

open Category MonoidalCategory MonObj LeftModCat

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [Limits.HasCoequalizers C]

/-- Abbreviation for an `A`-`B`-bimodule object in `C`, identified with Mathlib's `Bimod A B`. -/
abbrev BimoduleObj (A B : Mon C) := Bimod A B

/-- An `A`-`B`-bimodule in a monoidal category `C` is a triple `(M, p, q)` where `M ∈ C`,
`p : A ⊗ M → M` makes `M` a left `A`-module, `q : M ⊗ B → M` makes `M` a right `B`-module,
and the two actions commute. -/
abbrev Definition_2_9_24_Bimodule (A B : Mon C) := Bimod A B

end CategoryTheory
