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
import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part11


namespace StatMech

namespace Exact3D

structure FreeMassAnalyticRGToPlusExponentTarget
    (C : RGCertificate Ising3DModel) where
  δ : ℝ
  δ_pos : 0 < δ
  correlationLength : ℝ → ℝ
  freeMass : ℝ → ℝ
  plus_free_agree : PlusFreeTwoPointAgreeBelowBetaC
  freeMass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeMass β
  freeMass_realizes_inverse_length :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (freeMass β)
  correlationLength_eq_inv_mass :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β = (freeMass β)⁻¹
  prefactor : ℝ → ℝ
  prefactor_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < prefactor β
  prefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ => Real.log (prefactor β) / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  length_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      correlationLength β =
        prefactor β *
          Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))

end Exact3D
end StatMech
