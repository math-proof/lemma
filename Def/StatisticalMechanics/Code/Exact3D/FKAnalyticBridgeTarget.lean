/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part2


namespace StatMech

namespace Exact3D

namespace FKToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKToIsingAnalyticRGToExponentTarget C) :
    FKToIsingAnalyticRGToExponentTarget D where
  δ := T.δ
  δ_pos := T.δ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  realizesXAxisLength := T.realizesXAxisLength
  fk_hasCriticalNu := by
    simpa [hpred] using T.fk_hasCriticalNu
  ising_fk_length_agree := T.ising_fk_length_agree


end FKToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
