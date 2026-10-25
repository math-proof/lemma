/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part6


namespace StatMech

namespace Exact3D

structure FKMassAnalyticRGToExponentTarget
    (C : RGCertificate Ising3DModel) where
  

  betaδ : ℝ
  betaδ_pos : 0 < betaδ
  
  pδ : ℝ
  pδ_pos : 0 < pδ
  isingCorrelationLength : ℝ → ℝ
  fkCorrelationLength : ℝ → ℝ
  fkMass : ℝ → ℝ
  realizesXAxisLength :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - betaδ) (Ising.betaC 3) →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (isingCorrelationLength β)
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      0 < fkMass p
  fk_length_eq_inv_mass :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      fkCorrelationLength p = (fkMass p)⁻¹
  fkPrefactor : ℝ → ℝ
  fkPrefactor_pos :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      0 < fkPrefactor p
  fkPrefactor_log_negligible :
    Filter.Tendsto
      (fun p : ℝ =>
        Real.log (fkPrefactor p) /
          Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
      (nhdsWithin (IsingFK.pOfBeta (Ising.betaC 3))
        (Set.Iio (IsingFK.pOfBeta (Ising.betaC 3)))) (nhds 0)
  fk_length_scaling :
    ∀ p, p ∈ Set.Ioo
        (IsingFK.pOfBeta (Ising.betaC 3) - pδ)
        (IsingFK.pOfBeta (Ising.betaC 3)) →
      fkCorrelationLength p =
        fkPrefactor p *
          Real.exp
            (-C.predictedExponent *
              Real.log (IsingFK.pOfBeta (Ising.betaC 3) - p))
  ising_fk_length_agree :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      isingCorrelationLength β = fkCorrelationLength (IsingFK.pOfBeta β)

end Exact3D
end StatMech
