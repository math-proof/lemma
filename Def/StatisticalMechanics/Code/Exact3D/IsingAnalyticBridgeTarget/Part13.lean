/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part14


namespace StatMech

namespace Exact3D

namespace FreeMassAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassAnalyticRGToPlusExponentTarget C) :
    FreeMassAnalyticRGToPlusExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  freeMass := T.freeMass
  plus_free_agree := T.plus_free_agree
  freeMass_pos := T.freeMass_pos
  freeMass_realizes_inverse_length := T.freeMass_realizes_inverse_length
  correlationLength_eq_inv_mass := T.correlationLength_eq_inv_mass
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := by
    intro β hβ
    simpa [hpred] using T.length_scaling β hβ


end FreeMassAnalyticRGToPlusExponentTarget
end Exact3D
end StatMech
