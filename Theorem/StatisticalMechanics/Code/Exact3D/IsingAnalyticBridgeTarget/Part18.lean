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
import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part16


namespace StatMech

namespace Exact3D

namespace FreeMassPowerLawToPlusAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


@[simp] theorem congr_predictedExponent_toFreeMassTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFreeMassTarget =
      FreeMassAnalyticRGToPlusExponentTarget.congr_predictedExponent
        hpred T.toFreeMassTarget := by
  rfl


@[simp] theorem congr_predictedExponent_toFreeLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toFreeLengthTarget =
      FreeAnalyticRGToPlusExponentTarget.congr_predictedExponent
        hpred T.toFreeLengthTarget := by
  rfl


@[simp] theorem congr_predictedExponent_toPlusMassTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusMassTarget =
      IsingMassAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusMassTarget := by
  rfl


@[simp] theorem congr_predictedExponent_toPlusLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusLengthTarget =
      IsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusLengthTarget := by
  rfl


@[simp] theorem congr_predictedExponent_toPlusMassPowerLawTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusMassPowerLawTarget =
      IsingMassPowerLawAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusMassPowerLawTarget := by
  rfl


theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    D.RGToExponentBridge T.correlationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge


theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu


theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeMassPowerLawToPlusAnalyticRGToExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.correlationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit


end FreeMassPowerLawToPlusAnalyticRGToExponentTarget
end Exact3D
end StatMech
