/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_1_15_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Abbrev.v1.Atlas.TensorCategories.code.Definition_1_15_4
open CategoryTheory MonoidalCategory

universe u v


namespace Definition_1_15_4

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The component subcategory inherits the category structure from C via its full subcategory
structure. -/
instance componentSubcategory_category {n : ℕ} (f : Fin n → C) (i j : Fin n) :
    Category (ComponentSubcategory f i j) := inferInstance

end Definition_1_15_4
