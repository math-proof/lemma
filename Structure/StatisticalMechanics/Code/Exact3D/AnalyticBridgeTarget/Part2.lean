/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget


namespace StatMech

namespace Exact3D

namespace RGCertificate

structure AnalyticPrefactorBridgeInputs {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength prefactor : ℝ → ℝ)
    (RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge : Prop) : Prop where
  rgCovariance : RGCovariance
  stableManifoldControl : StableManifoldControl
  microscopicOrbitEntry : MicroscopicOrbitEntry
  subcriticalMassBridge : SubcriticalMassBridge
  prefactor_pos :
    ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC), 0 < prefactor β
  prefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (prefactor β) / Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 0)
  extractsPrefactorPowerLaw :
    RGCovariance →
      StableManifoldControl →
      MicroscopicOrbitEntry →
      SubcriticalMassBridge →
        ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
          correlationLength β =
            prefactor β *
              Real.exp (-C.predictedExponent * Real.log (M.betaC - β))

end RGCertificate
end Exact3D
end StatMech
