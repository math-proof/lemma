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
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Module TensorProduct

universe u


noncomputable section

namespace VecCategoricalFusionData

variable (k : Type u) [Field k]

/-- The `k`-linear equivalence between morphisms in `FGModuleCat k` and the underlying
linear maps between their carriers. -/
def homLinearEquiv (X Y : FGModuleCat.{u} k) :
    (X ⟶ Y) ≃ₗ[k] (X →ₗ[k] Y) where
  toFun f := f.hom.hom
  invFun f := FGModuleCat.ofHom f
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_add' f g := by ext; rfl
  map_smul' c f := by ext; rfl

end VecCategoricalFusionData
end
