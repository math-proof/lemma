/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_15_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
open CategoryTheory MonoidalCategory

universe u v


namespace Definition_1_15_4

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Given a finite indexing `f : Fin n → C` of objects (typically the components of the unit
object), this is the object `f i ⊗ X ⊗ f j` used to define the component subcategory C_{ij}. -/
def componentObj {n : ℕ} (f : Fin n → C) (X : C) (i j : Fin n) : C :=
  f i ⊗ X ⊗ f j

/-- Predicate: X belongs to the component subcategory C_{ij} := 1_i ⊗ C ⊗ 1_j, i.e., there
exists some Y in C with X isomorphic to f i ⊗ Y ⊗ f j. -/
def IsInComponentSubcategory {n : ℕ} (f : Fin n → C) (i j : Fin n) :
    ObjectProperty C :=
  fun X => ∃ (Y : C), Nonempty (X ≅ f i ⊗ Y ⊗ f j)

end Definition_1_15_4
