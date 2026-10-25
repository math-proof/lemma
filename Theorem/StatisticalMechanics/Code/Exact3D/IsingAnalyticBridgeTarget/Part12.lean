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
import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part10


namespace StatMech

namespace Exact3D

namespace FreeAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}


@[simp] theorem congr_predictedExponent_toPlusLengthTarget
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    (T.congr_predictedExponent hpred).toPlusLengthTarget =
      IsingAnalyticRGToExponentTarget.congr_predictedExponent
        hpred T.toPlusLengthTarget := by
  rfl


theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    D.RGToExponentBridge T.correlationLength :=
  (T.congr_predictedExponent hpred).rgToExponentBridge


theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength D.predictedExponent :=
  (T.congr_predictedExponent hpred).hasCriticalNu


theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : FreeAnalyticRGToPlusExponentTarget C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.correlationLength :=
  (T.congr_predictedExponent hpred).valid_of_checks
    hfinite htail hfixed hlinear hhyperbolic horbit


end FreeAnalyticRGToPlusExponentTarget
end Exact3D
end StatMech
