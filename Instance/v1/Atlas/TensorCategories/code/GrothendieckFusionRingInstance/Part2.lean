/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckFusionRingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Def.v1.Atlas.TensorCategories.code.GrothendieckFusionRingInstance.Part2
open CategoryTheory MonoidalCategory Finset

universe v u


namespace CategoryTheory

section Rank1

/-- The rank-one fusion ring trivially has the Perron-Frobenius property since all
matrices and eigenvectors are one-by-one. -/
instance : FusionRing.HasPerronFrobeniusProperty (Fin 1) where
  pfEigenvec := fun M hM => by
    refine ⟨M 0 0, fun _ => 1, hM 0 0, fun _ => one_pos, ?_⟩
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, mul_one]
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp
  pfUnique := fun M _ r₁ r₂ v w hv hv_eig hw hw_eig => by
    refine ⟨w 0 / v 0, fun i => ?_⟩
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [div_mul_cancel₀]
    exact ne_of_gt (hv 0)

end Rank1
end CategoryTheory
