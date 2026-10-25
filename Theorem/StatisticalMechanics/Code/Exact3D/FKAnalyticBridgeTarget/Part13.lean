/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Def.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part9


namespace StatMech

namespace Exact3D

namespace FKMassPowerLawToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge


theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu


theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.isingCorrelationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit


@[simp] theorem congr_predictedExponent_toFKMassTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFKMassTarget =
      FKMassAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toFKMassTarget := by
  rfl


@[simp] theorem congr_predictedExponent_toFKPowerLawTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFKPowerLawTarget =
      FKPowerLawToIsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toFKPowerLawTarget := by
  rfl


@[simp] theorem congr_predictedExponent_toFKTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFKTarget =
      FKToIsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toFKTarget := by
  rfl

end FKMassPowerLawToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
