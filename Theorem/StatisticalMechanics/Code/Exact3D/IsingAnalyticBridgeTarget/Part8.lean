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
import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part6


namespace StatMech

namespace Exact3D

namespace IsingMassPowerLawAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


@[simp] theorem toMassTarget_toLengthTarget
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    T.toMassTarget.toLengthTarget = T.toLengthTarget :=
  rfl


theorem rgToExponentBridge
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.correlationLength := by
  refine C.rgToExponentBridge_of_exact_mass_power_variable_prefactor_on_Ioo
    T.correlationLength T.mass T.massPrefactor T.δ T.δ_pos ?_ ?_ ?_ ?_
  · intro β hβ
    exact T.massPrefactor_pos β (by simpa [Ising3DModel] using hβ)
  · simpa [Ising3DModel] using T.massPrefactor_log_negligible
  · intro β hβ
    exact T.mass_scaling β (by simpa [Ising3DModel] using hβ)
  · intro β hβ
    exact T.correlationLength_eq_inv_mass β (by simpa [Ising3DModel] using hβ)


theorem hasCriticalNu
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.correlationLength C.predictedExponent :=
  T.rgToExponentBridge


theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toLengthTarget.eventually_correlationLength_eq_liminfCorrelationLength


theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toLengthTarget.rgToExponentBridge_liminfCorrelationLength


theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toLengthTarget.hasCriticalNu_liminfCorrelationLength


theorem valid_of_checks
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.correlationLength :=
  T.toMassTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic
    horbit


theorem valid_of_checks_liminfCorrelationLength
    (T : IsingMassPowerLawAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toLengthTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit


end IsingMassPowerLawAnalyticRGToExponentTarget
end Exact3D
end StatMech
