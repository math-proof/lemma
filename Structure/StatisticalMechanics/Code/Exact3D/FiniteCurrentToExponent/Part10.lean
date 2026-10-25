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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part8


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  fkMass : ℝ → ℝ
  lowerPrefactor : ℝ → ℝ
  upperPrefactor : ℝ → ℝ
  betaWindow : ℝ → ℝ
  pWindow : ℝ → ℝ
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  betaWindow_pos : ∀ ε, 0 < ε → 0 < betaWindow ε
  pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε
  selected_mass_eq_fkMass :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - betaWindow ε) Ising3DFKBetaC →
        freeSelectedPositiveSubcriticalMass hmass β = fkMass (IsingFK.pOfBeta β)
  beta_to_p_window :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - betaWindow ε) Ising3DFKBetaC →
        IsingFK.pOfBeta β ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC
  p_mass_constant_prefactor_power_sandwich_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKPC - p)) ≤
            fkMass p ∧
          fkMass p ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - p))
  beta_to_p_power_transfer_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - betaWindow ε) Ising3DFKBetaC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKBetaC - β)) ≤
            lowerPrefactor ε *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising3DFKPC - IsingFK.pOfBeta β)) ∧
          upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - IsingFK.pOfBeta β)) ≤
            upperPrefactor ε *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKBetaC - β))

end Exact3D
end StatMech
