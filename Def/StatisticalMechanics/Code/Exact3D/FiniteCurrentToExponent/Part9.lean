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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part10


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
      D hmass where
  fkMass := h.fkMass
  lowerPrefactor := h.lowerPrefactor
  upperPrefactor := h.upperPrefactor
  betaWindow := h.betaWindow
  pWindow := h.pWindow
  lowerPrefactor_pos := h.lowerPrefactor_pos
  upperPrefactor_pos := h.upperPrefactor_pos
  betaWindow_pos := h.betaWindow_pos
  pWindow_pos := h.pWindow_pos
  selected_mass_eq_fkMass := h.selected_mass_eq_fkMass
  beta_to_p_window := h.beta_to_p_window
  p_mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using
      h.p_mass_constant_prefactor_power_sandwich_on_Ioo ε hε p hp
  beta_to_p_power_transfer_on_Ioo := by
    intro ε hε β hβ
    simpa [hpred] using h.beta_to_p_power_transfer_on_Ioo ε hε β hβ

end FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical

set_option linter.style.longLine false in


def freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCPullback
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hpull :
      FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  lowerPrefactor := hpull.lowerPrefactor
  upperPrefactor := hpull.upperPrefactor
  window := hpull.betaWindow
  lowerPrefactor_pos := hpull.lowerPrefactor_pos
  upperPrefactor_pos := hpull.upperPrefactor_pos
  window_pos := hpull.betaWindow_pos
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    have hpwin := hpull.beta_to_p_window ε hε β hβ
    have hpsand :=
      hpull.p_mass_constant_prefactor_power_sandwich_on_Ioo
        ε hε (IsingFK.pOfBeta β) hpwin
    have htransfer := hpull.beta_to_p_power_transfer_on_Ioo ε hε β hβ
    have hsel := hpull.selected_mass_eq_fkMass ε hε β hβ
    constructor
    · rw [hsel]
      exact le_trans htransfer.1 hpsand.1
    · rw [hsel]
      exact le_trans hpsand.2 htransfer.2

end Exact3D
end StatMech
