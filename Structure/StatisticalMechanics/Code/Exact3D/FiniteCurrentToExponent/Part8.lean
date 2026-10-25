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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part7


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  mass_constant_prefactor_power_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakIooSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  window : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  window_pos : ∀ ε, 0 < ε → 0 < window ε
  mass_constant_prefactor_power_sandwich_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - window ε) (Ising.betaC 3) →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  lowerPrefactor : ℝ → ℝ
  lowerWindow : ℝ → ℝ
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  lowerWindow_pos : ∀ ε, 0 < ε → 0 < lowerWindow ε
  mass_lower_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - lowerWindow ε) (Ising.betaC 3) →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  upperPrefactor : ℝ → ℝ
  upperWindow : ℝ → ℝ
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  upperWindow_pos : ∀ ε, 0 < ε → 0 < upperWindow ε
  mass_upper_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - upperWindow ε) (Ising.betaC 3) →
        freeSelectedPositiveSubcriticalMass hmass β ≤
          upperPrefactor ε *
            Real.exp
              ((C.predictedExponent - ε / 2) *
                Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakIooUpperExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  mass_upper_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
          freeSelectedPositiveSubcriticalMass hmass β ≤
            p.1 *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising.betaC 3 - β))

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - p.2) (Ising.betaC 3) →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising.betaC 3 - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

end Exact3D
end StatMech
