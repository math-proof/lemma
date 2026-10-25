/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Structure.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3


namespace StatMech

namespace Exact3D

namespace RGCertificate

namespace AnalyticMassBridgeInputs

variable {ι : Type*} {M : CriticalModel ι} {C : RGCertificate M}

variable {correlationLength mass massPrefactor : ℝ → ℝ}

variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}


theorem eventually_massPrefactor_pos
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
      0 < massPrefactor β :=
  h.massPrefactor_pos


theorem eventually_mass_power
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
      mass β =
        massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (M.betaC - β)) :=
  h.extractsMassPowerLaw h.rgCovariance h.stableManifoldControl
    h.microscopicOrbitEntry h.subcriticalMassBridge


theorem eventually_correlationLength_eq_inv_mass
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
      correlationLength β = (mass β)⁻¹ :=
  h.extractsCorrelationLengthReciprocal h.rgCovariance
    h.stableManifoldControl h.microscopicOrbitEntry h.subcriticalMassBridge


theorem rgToExponentBridge
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    C.RGToExponentBridge correlationLength :=
  C.rgToExponentBridge_of_eventually_exact_mass_power_variable_prefactor
    correlationLength mass massPrefactor h.massPrefactor_pos
    h.massPrefactor_log_negligible h.eventually_mass_power
    h.eventually_correlationLength_eq_inv_mass


theorem valid_of_checks
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit h.rgToExponentBridge


theorem hasCriticalNu
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    HasCriticalNu M correlationLength C.predictedExponent :=
  h.rgToExponentBridge


theorem of_eventually_mass_power_with_inputs
    (hRG : RGCovariance)
    (hstable : StableManifoldControl)
    (horbit : MicroscopicOrbitEntry)
    (hmassBridge : SubcriticalMassBridge)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        0 < massPrefactor β)
    (hlog :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hmass :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        mass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (M.betaC - β)))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β = (mass β)⁻¹) :
    AnalyticMassBridgeInputs C correlationLength mass massPrefactor
      RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge where
  rgCovariance := hRG
  stableManifoldControl := hstable
  microscopicOrbitEntry := horbit
  subcriticalMassBridge := hmassBridge
  massPrefactor_pos := hpos
  massPrefactor_log_negligible := hlog
  extractsMassPowerLaw := fun _ _ _ _ => hmass
  extractsCorrelationLengthReciprocal := fun _ _ _ _ => hξ


theorem congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    AnalyticMassBridgeInputs D correlationLength mass massPrefactor
      RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge where
  rgCovariance := h.rgCovariance
  stableManifoldControl := h.stableManifoldControl
  microscopicOrbitEntry := h.microscopicOrbitEntry
  subcriticalMassBridge := h.subcriticalMassBridge
  massPrefactor_pos := h.massPrefactor_pos
  massPrefactor_log_negligible := h.massPrefactor_log_negligible
  extractsMassPowerLaw := by
    intro hRG hstable horbit hmassBridge
    exact
      (h.extractsMassPowerLaw hRG hstable horbit hmassBridge).mono
        (fun _ hβ => by simpa [hpred] using hβ)
  extractsCorrelationLengthReciprocal := by
    intro hRG hstable horbit hmassBridge
    exact h.extractsCorrelationLengthReciprocal hRG hstable horbit hmassBridge


theorem rgToExponentBridge_congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    D.RGToExponentBridge correlationLength :=
  (h.congr_predictedExponent hpred).rgToExponentBridge


theorem valid_of_checks_congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid correlationLength :=
  (h.congr_predictedExponent hpred).valid_of_checks hfinite htail hfixed
    hlinear hhyperbolic horbit


theorem hasCriticalNu_congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticMassBridgeInputs C correlationLength mass massPrefactor
        RGCovariance StableManifoldControl MicroscopicOrbitEntry
        SubcriticalMassBridge) :
    HasCriticalNu M correlationLength D.predictedExponent :=
  (h.congr_predictedExponent hpred).hasCriticalNu

end AnalyticMassBridgeInputs
end RGCertificate
end Exact3D
end StatMech
