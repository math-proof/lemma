/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Structure.v1.Atlas.TensorCategories.code.FPdimCategory
set_option maxHeartbeats 800000

open CategoryTheory Finset

universe u v


namespace CategoryTheory

attribute [instance] FPdimCategoryData.instFintype FPdimCategoryData.instNonempty

namespace FPdimCategoryData

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable (D : FPdimCategoryData C)

/-- The Frobenius-Perron dimension of `C`, computed from the given data as the sum of
squared FP-dimensions of the chosen simple objects (EGNO Definition 6.1.6). -/
noncomputable def fpDimCategory : ℝ :=
  ∑ i : D.I, D.fpDimFun.fpDim (D.simpleObj i) ^ 2

end FPdimCategoryData

/-- Top-level alias for the Frobenius-Perron dimension of a category, packaged from its
`FPdimCategoryData`. -/
noncomputable def fpDimCategory {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (D : FPdimCategoryData C) : ℝ :=
  D.fpDimCategory

end CategoryTheory
