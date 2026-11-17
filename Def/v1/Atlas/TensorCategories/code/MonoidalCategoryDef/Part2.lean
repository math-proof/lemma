/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
public import Abbrev.v1.Atlas.TensorCategories.code.MonoidalCategoryDef.Part2

@[expose] public section

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
