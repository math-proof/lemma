/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget


namespace StatMech

namespace Exact3D

structure FKToIsingAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  

  δ : ℝ
  δ_pos : 0 < δ
  
  isingCorrelationLength : ℝ → ℝ
  
  fkCorrelationLength : ℝ → ℝ
  
  realizesXAxisLength :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (isingCorrelationLength β)
  
  fk_hasCriticalNu :
    HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
      fkCorrelationLength C.predictedExponent
  

  ising_fk_length_agree :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)

end Exact3D
end StatMech
