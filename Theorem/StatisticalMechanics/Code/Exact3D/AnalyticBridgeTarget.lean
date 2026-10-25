/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Structure.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget


namespace StatMech

namespace Exact3D

namespace RGCertificate

namespace AnalyticBridgeInputs

variable {ι : Type*} {M : CriticalModel ι} {C : RGCertificate M}

variable {correlationLength : ℝ → ℝ}

variable {RGCovariance StableManifoldControl MicroscopicOrbitEntry
  SubcriticalMassBridge : Prop}


theorem eventually_exact_power
    (h :
      AnalyticBridgeInputs C correlationLength RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
      correlationLength β =
        Real.exp (-C.predictedExponent * Real.log (M.betaC - β)) :=
  h.extractsExactPowerLaw h.rgCovariance h.stableManifoldControl
    h.microscopicOrbitEntry h.subcriticalMassBridge


theorem rgToExponentBridge
    (h :
      AnalyticBridgeInputs C correlationLength RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    C.RGToExponentBridge correlationLength :=
  C.rgToExponentBridge_of_eventually_exact_power correlationLength
    (eventually_exact_power h)


theorem valid_of_checks
    (h :
      AnalyticBridgeInputs C correlationLength RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge)
    (hfinite : C.FiniteCaseChecks) (htail : C.TailBounds)
    (hfixed : C.FixedPointEnclosure) (hlinear : C.LinearizationEnclosure)
    (hhyperbolic : C.HyperbolicSplitting) (horbit : C.OrbitEntry) :
    C.Valid correlationLength where
  finiteCaseChecks := hfinite
  tailBounds := htail
  fixedPointEnclosure := hfixed
  linearizationEnclosure := hlinear
  hyperbolicSplitting := hhyperbolic
  orbitEntry := horbit
  bridge := h.rgToExponentBridge


theorem hasCriticalNu
    (h :
      AnalyticBridgeInputs C correlationLength RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength C.predictedExponent :=
  h.rgToExponentBridge


theorem of_eventually_exact_power
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    AnalyticBridgeInputs C correlationLength True True True True where
  rgCovariance := trivial
  stableManifoldControl := trivial
  microscopicOrbitEntry := trivial
  subcriticalMassBridge := trivial
  extractsExactPowerLaw := fun _ _ _ _ => hξ


theorem of_eventually_exact_power_with_inputs
    (hRG : RGCovariance)
    (hstable : StableManifoldControl)
    (horbit : MicroscopicOrbitEntry)
    (hmass : SubcriticalMassBridge)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          Real.exp (-C.predictedExponent * Real.log (M.betaC - β))) :
    AnalyticBridgeInputs C correlationLength RGCovariance
      StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where
  rgCovariance := hRG
  stableManifoldControl := hstable
  microscopicOrbitEntry := horbit
  subcriticalMassBridge := hmass
  extractsExactPowerLaw := fun _ _ _ _ => hξ


theorem congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticBridgeInputs C correlationLength RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    AnalyticBridgeInputs D correlationLength RGCovariance
      StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge where
  rgCovariance := h.rgCovariance
  stableManifoldControl := h.stableManifoldControl
  microscopicOrbitEntry := h.microscopicOrbitEntry
  subcriticalMassBridge := h.subcriticalMassBridge
  extractsExactPowerLaw := by
    intro hRG hstable horbit hmass
    exact
      (h.extractsExactPowerLaw hRG hstable horbit hmass).mono
        (fun _ hβ => by simpa [hpred] using hβ)


theorem rgToExponentBridge_congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticBridgeInputs C correlationLength RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    D.RGToExponentBridge correlationLength :=
  (h.congr_predictedExponent hpred).rgToExponentBridge


theorem valid_of_checks_congr_predictedExponent {D : RGCertificate M}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      AnalyticBridgeInputs C correlationLength RGCovariance
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
      AnalyticBridgeInputs C correlationLength RGCovariance
        StableManifoldControl MicroscopicOrbitEntry SubcriticalMassBridge) :
    HasCriticalNu M correlationLength D.predictedExponent :=
  (h.congr_predictedExponent hpred).hasCriticalNu

end AnalyticBridgeInputs
end RGCertificate
end Exact3D
end StatMech
