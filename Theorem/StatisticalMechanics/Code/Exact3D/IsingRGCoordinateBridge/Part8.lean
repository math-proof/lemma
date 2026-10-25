/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part6


namespace StatMech

namespace Exact3D

namespace IsingMassRGCoordinateBridgeInputs

variable {C : RGCertificate Ising3DModel}


theorem toAnalyticMassBridgeInputs
    (T : IsingMassRGCoordinateBridgeInputs C) :
    RGCertificate.AnalyticMassBridgeInputs
      C T.scaffold.correlationLength T.scaffold.mass
      T.scaffold.massPrefactor
      (T.scaffold.MassCovariance ∧
        T.scaffold.CoordinateRGCovariance)
      T.stableManifoldControlStatement T.scaffold.MicroscopicOrbitEntry
      (∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        HasInverseCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay (T.scaffold.mass β)) where
  rgCovariance := ⟨T.massCovariance, T.coordinateCovariance⟩
  stableManifoldControl := T.stableManifoldControl
  microscopicOrbitEntry := T.microscopicOrbitEntry
  subcriticalMassBridge := T.eventually_hasInverseCorrelationLength
  massPrefactor_pos := by
    simpa [Ising3DModel] using T.eventually_massPrefactor_pos
  massPrefactor_log_negligible := by
    simpa [Ising3DModel] using T.massPrefactor_log_negligible
  extractsMassPowerLaw := by
    intro _ _ _ _
    simpa [Ising3DModel] using T.eventually_mass_scaling
  extractsCorrelationLengthReciprocal := by
    intro _ _ _ _
    simpa [Ising3DModel] using
      T.eventually_correlationLength_eq_inv_mass

@[simp] theorem toIsingMassPowerLawTarget_correlationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.correlationLength =
      T.scaffold.correlationLength :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_mass
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.mass = T.scaffold.mass :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_massPrefactor
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.massPrefactor =
      T.scaffold.massPrefactor :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.δ = T.scaffold.δ :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_toIsingMassTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.toMassTarget =
      T.toIsingMassTarget :=
  rfl

@[simp] theorem toIsingMassTarget_toIsingAnalyticTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassTarget.toLengthTarget =
      T.toIsingAnalyticTarget :=
  rfl

@[simp] theorem toIsingMassPowerLawTarget_toIsingAnalyticTarget
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassPowerLawTarget.toLengthTarget =
      T.toIsingAnalyticTarget :=
  rfl

@[simp] theorem toIsingMassTarget_correlationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassTarget.correlationLength =
      T.scaffold.correlationLength :=
  rfl

@[simp] theorem toIsingMassTarget_mass
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassTarget.mass = T.scaffold.mass :=
  rfl

@[simp] theorem toIsingMassTarget_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingMassTarget.δ = T.scaffold.δ :=
  rfl

@[simp] theorem toIsingAnalyticTarget_correlationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.correlationLength =
      T.scaffold.correlationLength :=
  rfl

@[simp] theorem toIsingAnalyticTarget_delta
    (T : IsingMassRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.δ = T.scaffold.δ :=
  rfl


theorem rgToExponentBridge
    (T : IsingMassRGCoordinateBridgeInputs C) :
    C.RGToExponentBridge T.scaffold.correlationLength :=
  T.toIsingMassPowerLawTarget.rgToExponentBridge


theorem hasCriticalNu
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      C.predictedExponent :=
  T.rgToExponentBridge


theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toIsingMassPowerLawTarget
    |>.eventually_correlationLength_eq_liminfCorrelationLength


theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toIsingMassPowerLawTarget.rgToExponentBridge_liminfCorrelationLength


theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toIsingMassPowerLawTarget.hasCriticalNu_liminfCorrelationLength


theorem valid_of_checks
    (T : IsingMassRGCoordinateBridgeInputs C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.scaffold.correlationLength :=
  T.toIsingMassPowerLawTarget.valid_of_checks hfinite htail hfixed hlinear
    hhyperbolic horbit


theorem valid_of_checks_liminfCorrelationLength
    (T : IsingMassRGCoordinateBridgeInputs C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toIsingMassPowerLawTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit


theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    D.RGToExponentBridge T.scaffold.correlationLength :=
  T.toIsingMassPowerLawTarget.rgToExponentBridge_congr_predictedExponent hpred


theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      D.predictedExponent :=
  T.toIsingMassPowerLawTarget.hasCriticalNu_congr_predictedExponent hpred


theorem rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    D.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (T.toIsingMassPowerLawTarget.congr_predictedExponent
    hpred).rgToExponentBridge_liminfCorrelationLength


theorem hasCriticalNu_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      D.predictedExponent :=
  (T.toIsingMassPowerLawTarget.congr_predictedExponent
    hpred).hasCriticalNu_liminfCorrelationLength


theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.scaffold.correlationLength :=
  T.toIsingMassPowerLawTarget.valid_of_checks_congr_predictedExponent hpred
    hfinite htail hfixed hlinear hhyperbolic horbit


theorem valid_of_checks_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingMassRGCoordinateBridgeInputs C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (T.toIsingMassPowerLawTarget.congr_predictedExponent
    hpred).valid_of_checks_liminfCorrelationLength
      hfinite htail hfixed hlinear hhyperbolic horbit

end IsingMassRGCoordinateBridgeInputs
end Exact3D
end StatMech
