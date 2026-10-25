/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularObject.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Def.v1.Atlas.TensorCategories.code.RegularObject.Part2
attribute [instance] FiniteTensorCategoryFPData.I_fintype
  FiniteTensorCategoryFPData.I_nonempty


namespace FiniteTensorCategoryFPData

variable (D : FiniteTensorCategoryFPData)

/-- Reference abbreviation for Definition 1.47.4 (the regular object of a finite
tensor category). -/
noncomputable abbrev Definition_1_47_4 := @FiniteTensorCategoryFPData.regularObject

end FiniteTensorCategoryFPData
