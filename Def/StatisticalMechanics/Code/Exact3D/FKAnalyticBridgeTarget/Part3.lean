/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part4


namespace StatMech

namespace Exact3D

namespace FKPowerLawToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


def toFKTarget
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    FKToIsingAnalyticRGToExponentTarget C where
  δ := T.betaδ
  δ_pos := T.betaδ_pos
  isingCorrelationLength := T.isingCorrelationLength
  fkCorrelationLength := T.fkCorrelationLength
  realizesXAxisLength := T.realizesXAxisLength
  fk_hasCriticalNu := T.fk_hasCriticalNu
  ising_fk_length_agree := T.ising_fk_length_agree

end FKPowerLawToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
