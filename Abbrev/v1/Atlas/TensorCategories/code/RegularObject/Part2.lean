/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularObject.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Def.v1.Atlas.TensorCategories.code.RegularObject.Part2
@[expose] public section

attribute [instance] FiniteTensorCategoryFPData.I_fintype
  FiniteTensorCategoryFPData.I_nonempty


namespace FiniteTensorCategoryFPData

variable (D : FiniteTensorCategoryFPData)

/-- Reference abbreviation for Definition 1.47.4 (the regular object of a finite
tensor category). -/
noncomputable abbrev Definition_1_47_4 := @FiniteTensorCategoryFPData.regularObject

end FiniteTensorCategoryFPData
