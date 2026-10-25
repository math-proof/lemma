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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part11


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical
    (hmass : FreePositiveSubcriticalMassBridge) where
  fkMass : ℝ → ℝ
  selectedWindow : ℝ → ℝ
  selectedWindow_pos : ∀ ε, 0 < ε → 0 < selectedWindow ε
  selected_mass_eq_fkMass :
    ∀ ε, 0 < ε →
      ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - selectedWindow ε) Ising3DFKBetaC →
        freeSelectedPositiveSubcriticalMass hmass β = fkMass (IsingFK.pOfBeta β)

end Exact3D
end StatMech
