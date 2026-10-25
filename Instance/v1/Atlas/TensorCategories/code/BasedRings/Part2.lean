/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Def.v1.Atlas.TensorCategories.code.BasedRings.Part5
open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The inner automorphism subgroup is normal in `MulAut G`. -/
instance innerAutNormal (G : Type*) [Group G] : (InnerAutSubgroup G).Normal where
  conj_mem := by
    rintro φ ⟨g, rfl⟩ ψ
    refine ⟨ψ g, ?_⟩
    ext x
    simp only [innerAut, MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply]
    simp only [map_mul, map_inv, MulAut.apply_inv_self]

end FusionRing
