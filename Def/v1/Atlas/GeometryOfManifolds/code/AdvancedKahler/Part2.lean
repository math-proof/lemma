/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part5
set_option autoImplicit false

open DifferentialFormSpace


/-- The Green-corrected section family: replaces each $s_{k,p}$ by
$s_{k,p} + G(s_{k,p})$, producing a (genuinely) holomorphic family on the
same line bundle. -/
noncomputable def correctedFamily
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst))
    (gci : GreenCorrectionInput wdn l2 dol fam) :
    ApproxHolomorphicSectionFamily (inst := inst) :=
  { L := gci.same_bundle_data,
    section_ := fun k p => fam.section_ k p + gci.greenOp.greenCorrection k (fam.section_ k p) }

