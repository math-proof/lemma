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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part11


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
      D hmass where
  fkMass := h.fkMass
  lowerPrefactor := h.lowerPrefactor
  upperPrefactor := h.upperPrefactor
  pWindow := h.pWindow
  lowerPrefactor_pos := h.lowerPrefactor_pos
  upperPrefactor_pos := h.upperPrefactor_pos
  pWindow_pos := h.pWindow_pos
  selected_mass_eq_fkMass := h.selected_mass_eq_fkMass
  p_mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using
      h.p_mass_constant_prefactor_power_sandwich_on_Ioo ε hε p hp
  beta_to_p_power_transfer_on_Ioo := by
    intro ε hε β hβ
    simpa [hpred] using h.beta_to_p_power_transfer_on_Ioo ε hε β hβ

end FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCPullback_of_canonicalWindowPullback
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKPCPullbackConstantPrefactorWeakIooSandwichNearCritical
      C hmass where
  fkMass := hcanon.fkMass
  lowerPrefactor := hcanon.lowerPrefactor
  upperPrefactor := hcanon.upperPrefactor
  betaWindow :=
    FKReparameterization.pOfBetaLeftPullbackWindow
      Ising3DFKBetaC hcanon.pWindow hcanon.pWindow_pos
  pWindow := hcanon.pWindow
  lowerPrefactor_pos := hcanon.lowerPrefactor_pos
  upperPrefactor_pos := hcanon.upperPrefactor_pos
  betaWindow_pos := by
    intro ε hε
    exact
      FKReparameterization.pOfBetaLeftPullbackWindow_pos
        Ising3DFKBetaC hcanon.pWindow hcanon.pWindow_pos hε
  pWindow_pos := hcanon.pWindow_pos
  selected_mass_eq_fkMass := hcanon.selected_mass_eq_fkMass
  beta_to_p_window := by
    intro ε hε β hβ
    simpa [Ising3DFKPC] using
      FKReparameterization.pOfBeta_mem_Ioo_of_mem_leftPullbackWindow
        Ising3DFKBetaC hcanon.pWindow hcanon.pWindow_pos hε hβ
  p_mass_constant_prefactor_power_sandwich_on_Ioo :=
    hcanon.p_mass_constant_prefactor_power_sandwich_on_Ioo
  beta_to_p_power_transfer_on_Ioo := hcanon.beta_to_p_power_transfer_on_Ioo

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCCanonicalWindowPullback
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hcanon :
      FreePositiveSubcriticalMassFKPCCanonicalWindowPullbackConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
      C hmass :=
  freePositiveSubcriticalMassFKBetaCIooSandwich_of_fkPCPullback
    C hmass
    (freePositiveSubcriticalMassFKPCPullback_of_canonicalWindowPullback
      C hmass hcanon)

end Exact3D
end StatMech
