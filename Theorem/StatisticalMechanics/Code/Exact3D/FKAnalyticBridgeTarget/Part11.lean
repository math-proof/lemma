/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Def.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part7


namespace StatMech

namespace Exact3D

namespace FKMassPowerLawToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


@[simp] theorem toFKMassTarget_toFKPowerLawTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    T.toFKMassTarget.toFKPowerLawTarget = T.toFKPowerLawTarget := by
  rfl


theorem fk_hasCriticalNu
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      T.fkCorrelationLength C.predictedExponent :=
  T.toFKMassTarget.fk_hasCriticalNu


end FKMassPowerLawToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
