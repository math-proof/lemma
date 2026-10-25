/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecCategoricalFusionData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Instance.v1.Atlas.TensorCategories.code.VecSemisimple.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.VecSemisimple
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Def.v1.Atlas.TensorCategories.code.VecCategoricalFusionData
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Module TensorProduct

universe u


noncomputable section

namespace VecCategoricalFusionData

variable (k : Type u) [Field k]

/-- The dimension of `Hom(k, k ⊗ k)` over `k` (computed inside `FGModuleCat k`) is
one, reflecting the fact that `k ⊗ k ≅ k` is simple in `Vec`. -/
theorem vec_hom_finrank :
    finrank k (FGModuleCat.of k k ⟶ (FGModuleCat.of k k ⊗ FGModuleCat.of k k)) = 1 := by
  rw [(homLinearEquiv k (FGModuleCat.of k k) (FGModuleCat.of k k ⊗ FGModuleCat.of k k)).finrank_eq]
  show finrank k (k →ₗ[k] (k ⊗[k] k)) = 1
  rw [(LinearMap.ringLmapEquivSelf k k (k ⊗[k] k)).finrank_eq]
  rw [(TensorProduct.lid k k).finrank_eq]
  exact finrank_self k

end VecCategoricalFusionData
end
