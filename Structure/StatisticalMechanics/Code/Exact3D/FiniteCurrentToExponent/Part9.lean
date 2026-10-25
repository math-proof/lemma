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
import Abbrev.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part3


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooLowerBoundExistsNoWindowNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - p.2) Ising3DFKBetaC →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising3DFKBetaC - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β

set_option linter.style.longLine false in

structure FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooUpperExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  mass_upper_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - p.2) Ising3DFKBetaC →
          freeSelectedPositiveSubcriticalMass hmass β ≤
            p.1 *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKBetaC - β))

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  window : ℝ → ℝ
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  window_pos : ∀ ε, 0 < ε → 0 < window ε
  mass_constant_prefactor_power_sandwich_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - window ε) Ising3DFKBetaC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKBetaC - β)) ≤
            freeSelectedPositiveSubcriticalMass hmass β ∧
          freeSelectedPositiveSubcriticalMass hmass β ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKBetaC - β))

end Exact3D
end StatMech
