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
import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part5


namespace StatMech

namespace Exact3D

structure IsingMassPowerLawAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  δ : ℝ
  δ_pos : 0 < δ
  correlationLength : ℝ → ℝ
  mass : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < mass β
  mass_realizes_inverse_length :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (mass β)
  correlationLength_eq_inv_mass :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β = (mass β)⁻¹
  
  massPrefactor : ℝ → ℝ
  massPrefactor_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < massPrefactor β
  massPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (massPrefactor β) /
        Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  
  mass_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      mass β =
        massPrefactor β *
          Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))

end Exact3D
end StatMech
