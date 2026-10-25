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
import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part3


namespace StatMech

namespace Exact3D

namespace IsingMassAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


theorem rgToExponentBridge
    (T : IsingMassAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.correlationLength :=
  T.toLengthTarget.rgToExponentBridge


theorem hasCriticalNu
    (T : IsingMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent :=
  T.rgToExponentBridge


theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toLengthTarget.eventually_correlationLength_eq_liminfCorrelationLength


theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toLengthTarget.rgToExponentBridge_liminfCorrelationLength


theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toLengthTarget.hasCriticalNu_liminfCorrelationLength


theorem valid_of_checks
    (T : IsingMassAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.correlationLength :=
  T.toLengthTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic
    horbit


theorem valid_of_checks_liminfCorrelationLength
    (T : IsingMassAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toLengthTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit


end IsingMassAnalyticRGToExponentTarget
end Exact3D
end StatMech
