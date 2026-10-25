/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Def.v1.Atlas.TensorCategories.code.MonoidalCategoryDef.Part4
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v v₂ u u₂


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [instance] Definition_1_1_2.instCat
  Definition_1_1_2.instMonoidal
  Definition_1_1_2.instFaithful

section Definition_1_1_3

open CategoryTheory MonoidalCategory MonoidalOpposite

universe v' u'

/-- EGNO Definition 1.1.3: the opposite monoidal category `C^op`, where the tensor product
is reversed. -/
abbrev Definition_1_1_3 (C : Type u') [Category.{v'} C] [MonoidalCategory C] :=
  MonoidalCategory (MonoidalOpposite C)

/-- EGNO Definition 1.1.3 (alias): the opposite monoidal category. -/
abbrev EGNO_Definition_1_1_3 (C : Type u') [Category.{v'} C] [MonoidalCategory C] :=
  MonoidalCategory (MonoidalOpposite C)

/-- EGNO Definition 1.1.3 (short alias): the opposite monoidal category. -/
abbrev def_1_1_3 (C : Type u') [Category.{v'} C] [MonoidalCategory C] :=
  MonoidalCategory (MonoidalOpposite C)

end Definition_1_1_3
end TensorCategories
