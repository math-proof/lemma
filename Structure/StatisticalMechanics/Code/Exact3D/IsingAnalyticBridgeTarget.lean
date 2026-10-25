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
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget


namespace StatMech

namespace Exact3D

structure IsingAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  

  δ : ℝ
  δ_pos : 0 < δ
  
  correlationLength : ℝ → ℝ
  

  realizesXAxisLength :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (correlationLength β)
  
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
