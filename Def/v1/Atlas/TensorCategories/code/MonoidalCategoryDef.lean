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
import Abbrev.v1.Atlas.TensorCategories.code.MonoidalCategoryDef
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v v₂ u u₂


section Definition_1_1_1_components

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The tensor product bifunctor `⊗` of a monoidal category, viewed as a function on objects. -/
def Definition_1_1_1.tensorObj : C → C → C := fun X Y => X ⊗ Y

/-- The associativity isomorphism `a_{X,Y,Z} : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. -/
def Definition_1_1_1.associator (X Y Z : C) : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) := α_ X Y Z

/-- The unit object `1` of a monoidal category. -/
def Definition_1_1_1.unitObject : C := 𝟙_ C

/-- The unit isomorphism `ι : 𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C` realised as the left unitor of the unit. -/
def Definition_1_1_1.unitIso : (𝟙_ C) ⊗ (𝟙_ C) ≅ 𝟙_ C := λ_ (𝟙_ C)

/-- The left unitor isomorphism `l_X : 𝟙_ C ⊗ X ≅ X`. -/
def Definition_1_1_1.leftUnitor (X : C) : (𝟙_ C) ⊗ X ≅ X := λ_ X

/-- The right unitor isomorphism `r_X : X ⊗ 𝟙_ C ≅ X`. -/
def Definition_1_1_1.rightUnitor (X : C) : X ⊗ (𝟙_ C) ≅ X := ρ_ X

end Definition_1_1_1_components
