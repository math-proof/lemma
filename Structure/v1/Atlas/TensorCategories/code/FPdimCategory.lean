/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FPdimCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
set_option maxHeartbeats 800000

open CategoryTheory Finset

universe u v


namespace CategoryTheory

/-- Data needed to compute the Frobenius-Perron dimension of a multitensor category `C`:
a finite nonempty index set `I`, a family of simple objects `simpleObj : I → C`, an
FP-dimension function on `C`, and the assumption that each simple has FP-dimension at
least one. -/
structure FPdimCategoryData (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  I : Type*
  [instFintype : Fintype I]
  [instNonempty : Nonempty I]
  simpleObj : I → C
  fpDimFun : FPdimFunction (C := C)
  fpDim_simpleObj_ge_one : ∀ i, fpDimFun.fpDim (simpleObj i) ≥ 1

end CategoryTheory
