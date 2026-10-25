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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part12


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  lowerPrefactor : ℝ → ℝ
  pWindow : ℝ → ℝ
  lowerPrefactor_pos : ∀ ε, 0 < ε → 0 < lowerPrefactor ε
  pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε
  p_mass_lower_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC →
        lowerPrefactor ε *
            Real.exp
              ((C.predictedExponent + ε / 2) *
                Real.log (Ising3DFKPC - p)) ≤
            fkMass p

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  upperPrefactor : ℝ → ℝ
  pWindow : ℝ → ℝ
  upperPrefactor_pos : ∀ ε, 0 < ε → 0 < upperPrefactor ε
  pWindow_pos : ∀ ε, 0 < ε → 0 < pWindow ε
  p_mass_upper_on_Ioo :
    ∀ ε, 0 < ε →
      ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pWindow ε) Ising3DFKPC →
        fkMass p ≤
          upperPrefactor ε *
            Real.exp
              ((C.predictedExponent - ε / 2) *
                Real.log (Ising3DFKPC - p))

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  p_mass_lower_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ q, q ∈ Set.Ioo (Ising3DFKPC - p.2) Ising3DFKPC →
          p.1 *
              Real.exp
                ((C.predictedExponent + ε / 2) *
                  Real.log (Ising3DFKPC - q)) ≤
            fkMass q

set_option linter.style.longLine false in

structure FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  p_mass_upper_exists :
    ∀ ε, 0 < ε →
      ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
        ∀ q, q ∈ Set.Ioo (Ising3DFKPC - p.2) Ising3DFKPC →
          fkMass q ≤
            p.1 *
              Real.exp
                ((C.predictedExponent - ε / 2) *
                  Real.log (Ising3DFKPC - q))

end Exact3D
end StatMech
