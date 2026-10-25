/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/AnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge


namespace StatMech

namespace Exact3D

namespace RGCertificate

structure AnalyticBridgeInputs {ι : Type*} {M : CriticalModel ι}
    (C : RGCertificate M) (correlationLength : ℝ → ℝ)
    (RGCovariance StableManifoldControl MicroscopicOrbitEntry
      SubcriticalMassBridge : Prop) : Prop where
  rgCovariance : RGCovariance
  stableManifoldControl : StableManifoldControl
  microscopicOrbitEntry : MicroscopicOrbitEntry
  subcriticalMassBridge : SubcriticalMassBridge
  extractsExactPowerLaw :
    RGCovariance →
      StableManifoldControl →
      MicroscopicOrbitEntry →
      SubcriticalMassBridge →
        ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
          correlationLength β =
            Real.exp (-C.predictedExponent * Real.log (M.betaC - β))

end RGCertificate
end Exact3D
end StatMech
