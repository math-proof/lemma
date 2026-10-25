/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part5


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassLogAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  logRemainder : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  logRemainder_negligible :
    Filter.Tendsto
      (fun β : ℝ => logRemainder β / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  log_mass_scaling :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        C.predictedExponent * Real.log (Ising.betaC 3 - β) +
          logRemainder β

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassLogRatioLimitNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_ratio_tendsto :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
          Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds C.predictedExponent)

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassLogRatioSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_ratio_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        C.predictedExponent - ε <
            Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
              Real.log (Ising.betaC 3 - β) ∧
          Real.log (freeSelectedPositiveSubcriticalMass hmass β) /
              Real.log (Ising.betaC 3 - β) <
            C.predictedExponent + ε

end Exact3D
end StatMech
