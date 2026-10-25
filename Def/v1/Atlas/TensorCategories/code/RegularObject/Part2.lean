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
import Structure.v1.Atlas.TensorCategories.code.RegularObject
attribute [instance] FiniteTensorCategoryFPData.I_fintype
  FiniteTensorCategoryFPData.I_nonempty


namespace FiniteTensorCategoryFPData

variable (D : FiniteTensorCategoryFPData)

/-- The regular object of a finite tensor category: the formal sum of the
projective covers weighted by the Frobenius–Perron dimensions of the simples. -/
noncomputable def regularObject : FormalProjectiveSum D.I :=
  ∑ i : D.I, D.fpDimSimple i • FormalProjectiveSum.basis i

/-- The Frobenius–Perron dimension of the regular object: the formal sum of
`dim(simple i) · dim(projCover i)`. -/
noncomputable def fpdimRegularObject : ℝ :=
  D.regularObject.fpdim D.fpDimProjCover

end FiniteTensorCategoryFPData
