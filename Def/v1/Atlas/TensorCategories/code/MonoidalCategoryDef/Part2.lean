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
import Abbrev.v1.Atlas.TensorCategories.code.MonoidalCategoryDef.Part2
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v v₂ u u₂


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The unit isomorphism `(𝟙_ C) ⊗ (𝟙_ C) ⟶ 𝟙_ C` of EGNO Definition 1.1.1, realised as the
right unitor of the unit. -/
def Definition_1_1_1_unitMorphism : (𝟙_ C) ⊗ (𝟙_ C) ⟶ (𝟙_ C) :=
  (ρ_ (𝟙_ C)).hom

end TensorCategories
