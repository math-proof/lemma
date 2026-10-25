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
import Structure.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part6
set_option autoImplicit false

open DifferentialFormSpace


/-- The PDE infrastructure required to run the Green-correction construction:
a weighted derivative sup-norm, an $L^2$-norm, the Dolbeault operator, and a
recipe for producing `GreenCorrectionInput` for any section family. -/
class HasPDEInfrastructure
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF] where
  wdn : WeightedDerivSupNorm Ω (inst := inst)
  l2 : L2NormSpace Ω (inst := inst)
  dol : DolbeaultOps (inst := inst)
  greenCorrection : ∀ (fam : ApproxHolomorphicSectionFamily (inst := inst)),
    GreenCorrectionInput wdn l2 dol fam


