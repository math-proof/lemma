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
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part11


namespace StatMech

namespace Exact3D

namespace FreeAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    FreeAnalyticRGToPlusExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  correlationLength := T.correlationLength
  plus_free_agree := T.plus_free_agree
  free_realizesXAxisLength := T.free_realizesXAxisLength
  prefactor := T.prefactor
  prefactor_pos := T.prefactor_pos
  prefactor_log_negligible := T.prefactor_log_negligible
  length_scaling := by
    intro β hβ
    simpa [hpred] using T.length_scaling β hβ


end FreeAnalyticRGToPlusExponentTarget
end Exact3D
end StatMech
