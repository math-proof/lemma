/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Structure.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part2


namespace StatMech

namespace Exact3D

namespace RGCertificate

namespace AnalyticPrefactorBridgeInputs

variable {ι : Type*} {M : CriticalModel ι} {C : RGCertificate M}

variable {correlationLength prefactor : ℝ → ℝ}

variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}


theorem eventually_prefactor_pos
    (h :
      AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < prefactor β :=
  h.prefactor_pos


theorem eventually_prefactor_power
    (h :
      AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
      correlationLength β =
        prefactor β *
          Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) :=
  h.extractsPrefactorPowerLaw h.rgCovariance h.stableManifoldControl
    h.microscopicOrbitEntry h.subcriticalMassBridge


theorem rgToExponentBridge
    (h :
      AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    C.RGToExponentBridge correlationLength :=
  C.rgToExponentBridge_of_eventually_exact_power_variable_prefactor
    correlationLength prefactor h.prefactor_pos h.prefactor_log_negligible
    h.eventually_prefactor_power


theorem valid_of_checks
    (h :
      AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid correlationLength :=
  C.valid_of_bridge correlationLength hfinite htail hfixed hlinear
    hhyperbolic horbit h.rgToExponentBridge


theorem hasCriticalNu
    (h :
      AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength C.predictedExponent :=
  h.rgToExponentBridge


theorem of_eventually_prefactor_power_with_inputs
    (hRG : RGCovariance)
    (hstable : StableManifoldControl)
    (horbit : MicroscopicOrbitEntry)
    (hmass : SubcriticalMassBridge)
    (hpos :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < prefactor β)
    (hlog :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) / Real.log (M.betaC - β))
        (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0))
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
      StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where
  rgCovariance := hRG
  stableManifoldControl := hstable
  microscopicOrbitEntry := horbit
  subcriticalMassBridge := hmass
  prefactor_pos := hpos
  prefactor_log_negligible := hlog
  extractsPrefactorPowerLaw := fun _ _ _ _ => hξ


theorem congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    AnalyticPrefactorBridgeInputs D correlationLength prefactor RGCovariance
      StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where
  rgCovariance := h.rgCovariance
  stableManifoldControl := h.stableManifoldControl
  microscopicOrbitEntry := h.microscopicOrbitEntry
  subcriticalMassBridge := h.subcriticalMassBridge
  prefactor_pos := h.prefactor_pos
  prefactor_log_negligible := h.prefactor_log_negligible
  extractsPrefactorPowerLaw := by
    intro hRG hstable horbit hmass
    exact
      (h.extractsPrefactorPowerLaw hRG hstable horbit hmass).mono
        (fun _ hβ => by simpa [hpred] using hβ)


theorem rgToExponentBridge_congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    D.RGToExponentBridge correlationLength :=
  (h.congr_predictedExponent hpred).rgToExponentBridge


theorem valid_of_checks_congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge)
    (hfinite : D.FiniteCaseChecks) (htail : D.TailBounds)
    (hfixed : D.FixedPointEnclosure) (hlinear : D.LinearizationEnclosure)
    (hhyperbolic : D.HyperbolicSplitting) (horbit : D.OrbitEntry) :
    D.Valid correlationLength :=
  (h.congr_predictedExponent hpred).valid_of_checks hfinite htail hfixed
    hlinear hhyperbolic horbit


theorem hasCriticalNu_congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticPrefactorBridgeInputs C correlationLength prefactor RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength D.predictedExponent :=
  (h.congr_predictedExponent hpred).hasCriticalNu

end AnalyticPrefactorBridgeInputs
end RGCertificate
end Exact3D
end StatMech
