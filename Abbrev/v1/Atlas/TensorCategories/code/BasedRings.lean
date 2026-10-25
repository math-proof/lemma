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
import Def.v1.Atlas.TensorCategories.code.BasedRings.Part6
open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- Proposition 1.42.9 (other direction): every categorification of the group ring `ℤ[G]`
of a finite group `G` over a field `k` is monoidally equivalent to `Vec_G^ω` for some
3-cocycle `ω : G × G × G → k^×`. -/
abbrev def_1_42_2_based_ring := @BasedRingDef

/-- Definition 1.42.2(2): a unital `ℤ₊`-ring, formalized as the `IsUnital` predicate on
`ZPlusRingDef`. -/
abbrev def_1_42_2_unital_zplus_ring := @ZPlusRingDef.IsUnital

/-- Definition 1.42.2(3): a multifusion ring (a based ring of finite rank), formalized as
`MultifusionRingDef`. -/
abbrev def_1_42_2_multifusion_ring := @MultifusionRingDef

/-- Definition 1.42.2(4): a fusion ring (a unital multifusion ring), formalized as the
`IsFusionRing` predicate on `MultifusionRingDef`. -/
abbrev def_1_42_2_fusion_ring := @MultifusionRingDef.IsFusionRing

end FusionRing
