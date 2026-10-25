/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_15_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Def.v1.Atlas.TensorCategories.code.Definition_1_15_4
open CategoryTheory MonoidalCategory

universe u v


namespace Definition_1_15_4

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Definition 1.15.4: The component subcategory C_{ij} := 1_i ⊗ C ⊗ 1_j of a multiring
category, realized as the full subcategory on objects satisfying `IsInComponentSubcategory f i j`. -/
abbrev ComponentSubcategory {n : ℕ} (f : Fin n → C) (i j : Fin n) :=
  (IsInComponentSubcategory f i j).FullSubcategory

end Definition_1_15_4
