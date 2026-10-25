/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Def.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part3


namespace StatMech

namespace Exact3D

namespace IsingRGCoordinateBridgeInputs

variable {C : RGCertificate Ising3DModel}


theorem toAnalyticPrefactorBridgeInputs
    (T : IsingRGCoordinateBridgeInputs C) :
    RGCertificate.AnalyticPrefactorBridgeInputs
      C T.scaffold.correlationLength T.scaffold.prefactor
      (T.scaffold.LengthCovariance ∧
        T.scaffold.CoordinateRGCovariance)
      T.stableManifoldControlStatement T.scaffold.MicroscopicOrbitEntry
      (∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
          (T.scaffold.correlationLength β)) where
  rgCovariance := ⟨T.lengthCovariance, T.coordinateCovariance⟩
  stableManifoldControl := T.stableManifoldControl
  microscopicOrbitEntry := T.microscopicOrbitEntry
  subcriticalMassBridge := T.eventually_hasCorrelationLength
  prefactor_pos := by
    simpa [Ising3DModel] using T.eventually_prefactor_pos
  prefactor_log_negligible := by
    simpa [Ising3DModel] using T.prefactor_log_negligible
  extractsPrefactorPowerLaw := by
    intro _ _ _ _
    simpa [Ising3DModel] using T.eventually_length_scaling

@[simp] theorem toIsingAnalyticTarget_correlationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.correlationLength =
      T.scaffold.correlationLength :=
  rfl

@[simp] theorem toIsingAnalyticTarget_prefactor
    (T : IsingRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.prefactor = T.scaffold.prefactor :=
  rfl

@[simp] theorem toIsingAnalyticTarget_delta
    (T : IsingRGCoordinateBridgeInputs C) :
    T.toIsingAnalyticTarget.δ = T.scaffold.δ :=
  rfl


theorem rgToExponentBridge
    (T : IsingRGCoordinateBridgeInputs C) :
    C.RGToExponentBridge T.scaffold.correlationLength :=
  T.toIsingAnalyticTarget.rgToExponentBridge


theorem hasCriticalNu
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      C.predictedExponent :=
  T.rgToExponentBridge


theorem eventually_correlationLength_eq_liminfCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      T.scaffold.correlationLength β =
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay :=
  T.toIsingAnalyticTarget.eventually_correlationLength_eq_liminfCorrelationLength


theorem rgToExponentBridge_liminfCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    C.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toIsingAnalyticTarget.rgToExponentBridge_liminfCorrelationLength


theorem hasCriticalNu_liminfCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      C.predictedExponent :=
  T.toIsingAnalyticTarget.hasCriticalNu_liminfCorrelationLength


theorem valid_of_checks
    (T : IsingRGCoordinateBridgeInputs C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid T.scaffold.correlationLength :=
  T.toIsingAnalyticTarget.valid_of_checks hfinite htail hfixed hlinear
    hhyperbolic horbit


theorem valid_of_checks_liminfCorrelationLength
    (T : IsingRGCoordinateBridgeInputs C)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  T.toIsingAnalyticTarget.valid_of_checks_liminfCorrelationLength
    hfinite htail hfixed hlinear hhyperbolic horbit


theorem rgToExponentBridge_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    D.RGToExponentBridge T.scaffold.correlationLength :=
  T.toIsingAnalyticTarget.rgToExponentBridge_congr_predictedExponent hpred


theorem hasCriticalNu_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel T.scaffold.correlationLength
      D.predictedExponent :=
  T.toIsingAnalyticTarget.hasCriticalNu_congr_predictedExponent hpred


theorem rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    D.RGToExponentBridge
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (T.toIsingAnalyticTarget.congr_predictedExponent
    hpred).rgToExponentBridge_liminfCorrelationLength


theorem hasCriticalNu_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C) :
    HasCriticalNu Ising3DModel
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay)
      D.predictedExponent :=
  (T.toIsingAnalyticTarget.congr_predictedExponent
    hpred).hasCriticalNu_liminfCorrelationLength


theorem valid_of_checks_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid T.scaffold.correlationLength :=
  T.toIsingAnalyticTarget.valid_of_checks_congr_predictedExponent hpred
    hfinite htail hfixed hlinear hhyperbolic horbit


theorem valid_of_checks_liminfCorrelationLength_congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    (hpred : D.predictedExponent = C.predictedExponent)
    (T : IsingRGCoordinateBridgeInputs C)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid
      (fun β : ℝ =>
        liminfCorrelationLength Ising3DModel β ising3DOrigin
          ising3DXAxisRay) :=
  (T.toIsingAnalyticTarget.congr_predictedExponent
    hpred).valid_of_checks_liminfCorrelationLength
      hfinite htail hfixed hlinear hhyperbolic horbit

end IsingRGCoordinateBridgeInputs
end Exact3D
end StatMech
