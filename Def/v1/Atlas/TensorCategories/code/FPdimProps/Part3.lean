/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Structure.v1.Atlas.TensorCategories.code.FPdimProps
set_option maxHeartbeats 800000


namespace CategoryTheory

open CategoryTheory MonoidalCategory Limits

attribute [reducible, instance] FiniteMultitensorDecompData.instFintype
  FiniteMultitensorDecompData.instDecEq

attribute [instance] FiniteTensorCategoryFPdimData.instFintype
  FiniteTensorCategoryFPdimData.instDecEq
  FiniteTensorCategoryFPdimData.instNonempty

namespace FiniteTensorCategoryFPdimData

variable (D : FiniteTensorCategoryFPdimData)

/-- The Frobenius–Perron dimension of the finite tensor category,
defined as `FPdim(C) := Σ_i FPdim(X_i) · FPdim(P_i)` (EGNO Definition 1.47.5). -/
noncomputable def catFPdim : ℝ :=
  ∑ i : D.I, D.fpDimSimple i * D.fpDimProjCover i

end FiniteTensorCategoryFPdimData
end CategoryTheory
