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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part6


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassPowerSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  mass_power_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        Real.exp
            ((C.predictedExponent + ε) *
              Real.log (Ising.betaC 3 - β)) <
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β <
            Real.exp
              ((C.predictedExponent - ε) *
                Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ → ℝ
  upperPrefactor : ℝ → ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactor_pos :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        0 < lowerPrefactor ε β
  upperPrefactor_pos :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        0 < upperPrefactor ε β
  lowerPrefactor_log_negligible :
    ∀ ε, 0 < ε →
      Filter.Tendsto
        (fun β : ℝ =>
          Real.log (lowerPrefactor ε β) / Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  upperPrefactor_log_negligible :
    ∀ ε, 0 < ε →
      Filter.Tendsto
        (fun β : ℝ =>
          Real.log (upperPrefactor ε β) / Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_prefactor_power_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        lowerPrefactor ε β *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) <
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β <
            upperPrefactor ε β *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ → ℝ
  upperPrefactor : ℝ → ℝ → ℝ
  lowerPrefactorLo : ℝ → ℝ
  lowerPrefactorHi : ℝ → ℝ
  upperPrefactorLo : ℝ → ℝ
  upperPrefactorHi : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactorLo_pos : ∀ ε, 0 < ε → 0 < lowerPrefactorLo ε
  lowerPrefactorHi_pos : ∀ ε, 0 < ε → 0 < lowerPrefactorHi ε
  upperPrefactorLo_pos : ∀ ε, 0 < ε → 0 < upperPrefactorLo ε
  upperPrefactorHi_pos : ∀ ε, 0 < ε → 0 < upperPrefactorHi ε
  lowerPrefactor_bounds :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        lowerPrefactorLo ε ≤ lowerPrefactor ε β ∧
          lowerPrefactor ε β ≤ lowerPrefactorHi ε
  upperPrefactor_bounds :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        upperPrefactorLo ε ≤ upperPrefactor ε β ∧
          upperPrefactor ε β ≤ upperPrefactorHi ε
  mass_prefactor_power_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        lowerPrefactor ε β *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) <
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β <
            upperPrefactor ε β *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

end Exact3D
end StatMech
