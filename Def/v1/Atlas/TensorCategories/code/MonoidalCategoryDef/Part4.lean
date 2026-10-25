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
import Structure.v1.Atlas.TensorCategories.code.MonoidalCategoryDef
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v v₂ u u₂


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [instance] Definition_1_1_2.instCat
  Definition_1_1_2.instMonoidal
  Definition_1_1_2.instFaithful

/-- Construct a monoidal subcategory in the sense of EGNO Definition 1.1.2 from any
monoidal `ObjectProperty` on `C`. -/
def Definition_1_1_2.ofFullSubcategory
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (P : ObjectProperty C) [P.IsMonoidal] :
    Definition_1_1_2.{v, v, u, u} C where
  D := P.FullSubcategory
  ι := P.ι
  instMonoidalFunctor := inferInstance

end TensorCategories
