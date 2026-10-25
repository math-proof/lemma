/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part12


namespace StatMech

namespace Exact3D

namespace FKMassPowerLawToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKMassPowerLawToIsingAnalyticRGToExponentTarget D where
  betaδ := T.betaδ
  betaδ_pos := T.betaδ_pos
  pδ := T.pδ
  pδ_pos := T.pδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  fkMass := T.fkMass
  realizesXAxisLength := T.realizesXAxisLength
  fkMassPrefactor := T.fkMassPrefactor
  fkMassPrefactor_pos := T.fkMassPrefactor_pos
  fkMassPrefactor_log_negligible := T.fkMassPrefactor_log_negligible
  fk_mass_scaling := by
    intro p hp
    simpa [hpred] using T.fk_mass_scaling p hp
  fk_length_eq_inv_mass := T.fk_length_eq_inv_mass
  ising_fk_length_agree := T.ising_fk_length_agree


end FKMassPowerLawToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
