/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Def.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part8


namespace StatMech

namespace Exact3D

namespace FKMassPowerLawToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


@[simp] theorem toFKMassTarget_toFKTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    T.toFKMassTarget.toFKTarget = T.toFKTarget := by
  rfl


@[simp] theorem toFKPowerLawTarget_toFKTarget
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    T.toFKPowerLawTarget.toFKTarget = T.toFKTarget := by
  rfl


theorem hasCriticalNu
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu


theorem eventually_isingCorrelationLength_eq_liminfCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.isingCorrelationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toFKTarget.eventually_isingCorrelationLength_eq_liminfCorrelationLength


theorem rgToExponentBridge
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.isingCorrelationLength :=
  T.toFKTarget.rgToExponentBridge


theorem rgToExponentBridge_direct
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge T.isingCorrelationLength :=
  C.rgToExponentBridge_of_fk_exact_mass_power_variable_prefactor_on_Ioo
    T.isingCorrelationLength T.fkCorrelationLength T.fkMass
    T.fkMassPrefactor T.pδ T.pδ_pos T.fkMassPrefactor_pos
    T.fkMassPrefactor_log_negligible T.fk_mass_scaling
    T.fk_length_eq_inv_mass T.ising_fk_length_agree


theorem hasCriticalNu_direct
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel T.isingCorrelationLength
      C.predictedExponent := by
  simpa [RGCertificate.RGToExponentBridge] using T.rgToExponentBridge_direct


theorem rgToExponentBridge_liminfCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.rgToExponentBridge_liminfCorrelationLength


theorem hasCriticalNu_liminfCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toFKTarget.hasCriticalNu_liminfCorrelationLength


theorem valid_of_checks
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.isingCorrelationLength :=
  T.toFKTarget.valid_of_checks hfinite htail hfixed hlinear hhyperbolic horbit


theorem valid_of_checks_direct
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.isingCorrelationLength :=
  C.valid_of_bridge T.isingCorrelationLength hfinite htail hfixed hlinear
    hhyperbolic horbit T.rgToExponentBridge_direct


theorem valid_of_checks_liminfCorrelationLength
    (T : FKMassPowerLawToIsingAnalyticRGToExponentTarget C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toFKTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit


end FKMassPowerLawToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
