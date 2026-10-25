/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part8


namespace StatMech

namespace Exact3D

namespace FKMassAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassAnalyticRGToExponentTarget C) :
    FKMassAnalyticRGToExponentTarget D where
  betaδ := T.betaδ
  betaδ_pos := T.betaδ_pos
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  fkMass := T.fkMass
  realizesXAxisLength := T.realizesXAxisLength
  fkMass_pos := T.fkMass_pos
  fk_length_eq_inv_mass := T.fk_length_eq_inv_mass
  fkPrefactor := T.fkPrefactor
  fkPrefactor_pos := T.fkPrefactor_pos
  fkPrefactor_log_negligible := T.fkPrefactor_log_negligible
  fk_length_scaling := by
    intro p hp
    simpa [hpred] using T.fk_length_scaling p hp
  ising_fk_length_agree := T.ising_fk_length_agree


end FKMassAnalyticRGToExponentTarget
end Exact3D
end StatMech
