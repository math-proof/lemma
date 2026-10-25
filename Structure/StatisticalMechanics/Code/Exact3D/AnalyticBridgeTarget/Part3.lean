/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part2


namespace StatMech

namespace Exact3D

namespace RGCertificate

structure AnalyticMassBridgeInputs {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M)
    (correlationLength mass massPrefactor : ℝ → ℝ)
    (RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge : Prop) : Prop where
  rgCovariance : RGCovariance
  stableManifoldControl : StableManifoldControl
  microscopicOrbitEntry : MicroscopicOrbitEntry
  subcriticalMassBridge : SubcriticalMassBridge
  massPrefactor_pos :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
      0 < massPrefactor β
  massPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (massPrefactor β) / Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)
  extractsMassPowerLaw :
    RGCovariance →
      StableManifoldControl →
      MicroscopicOrbitEntry →
      SubcriticalMassBridge →
        ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
          mass β =
            massPrefactor β *
              Real.exp (C.predictedExponent * Real.log (M.betaC - β))
  extractsCorrelationLengthReciprocal :
    RGCovariance →
      StableManifoldControl →
      MicroscopicOrbitEntry →
      SubcriticalMassBridge →
        ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
          correlationLength β = (mass β)⁻¹

end RGCertificate
end Exact3D
end StatMech
