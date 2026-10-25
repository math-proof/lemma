/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Def.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part3


namespace StatMech

namespace Exact3D

namespace FKPowerLawToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


@[simp] theorem toFKTarget_isingCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    T.toFKTarget.isingCorrelationLength = T.isingCorrelationLength :=
  rfl


theorem hasCriticalNu
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu


theorem eventually_isingCorrelationLength_eq_liminfCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toFKTarget.eventually_isingCorrelationLength_eq_liminfCorrelationLength


theorem rgToExponentBridge
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.isingCorrelationLength :=
  T.toFKTarget.rgToExponentBridge


theorem rgToExponentBridge_liminfCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.rgToExponentBridge_liminfCorrelationLength


theorem hasCriticalNu_liminfCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu_liminfCorrelationLength


theorem valid_of_checks
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.isingCorrelationLength :=
  T.toFKTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic horbit


theorem valid_of_checks_liminfCorrelationLength
    (T : FKPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit


end FKPowerLawToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
