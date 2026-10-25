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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part12


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
      D hmass where
  fkMass := h.fkMass
  lowerPrefactor := h.lowerPrefactor
  upperPrefactor := h.upperPrefactor
  pWindow := h.pWindow
  selectedWindow := h.selectedWindow
  lowerPrefactor_pos := h.lowerPrefactor_pos
  upperPrefactor_pos := h.upperPrefactor_pos
  pWindow_pos := h.pWindow_pos
  selectedWindow_pos := h.selectedWindow_pos
  selected_mass_eq_fkMass := h.selected_mass_eq_fkMass
  p_mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using
      h.p_mass_constant_prefactor_power_sandwich_on_Ioo ε hε p hp

end FreePositiveSubcriticalMassFKPCSelectedConstantPrefactorWeakIooSandwichNearCritical
end Exact3D
end StatMech
