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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part7


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def
    freePositiveSubcriticalMassSubpowerPrefactorSandwich_of_boundedPrefactorSandwich
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (hbounded :
      FreePositiveSubcriticalMassBoundedPrefactorSandwichNearCritical C hmass) :
    FreePositiveSubcriticalMassSubpowerPrefactorSandwichNearCritical C hmass where
  δ := hbounded.δ
  δ_pos := hbounded.δ_pos
  δ_le_betaC := hbounded.δ_le_betaC
  lowerPrefactor := hbounded.lowerPrefactor
  upperPrefactor := hbounded.upperPrefactor
  mass_pos := hbounded.mass_pos
  lowerPrefactor_pos := by
    intro ε hε
    filter_upwards [hbounded.lowerPrefactor_bounds ε hε] with β hβ
    exact lt_of_lt_of_le (hbounded.lowerPrefactorLo_pos ε hε) hβ.1
  upperPrefactor_pos := by
    intro ε hε
    filter_upwards [hbounded.upperPrefactor_bounds ε hε] with β hβ
    exact lt_of_lt_of_le (hbounded.upperPrefactorLo_pos ε hε) hβ.1
  lowerPrefactor_log_negligible := by
    intro ε hε
    simpa [Ising3DModel] using
      tendsto_log_bounded_prefactor_div_log_betaC_sub Ising3DModel
        (hbounded.lowerPrefactorLo_pos ε hε)
        (hbounded.lowerPrefactorHi_pos ε hε)
        (hbounded.lowerPrefactor_bounds ε hε)
  upperPrefactor_log_negligible := by
    intro ε hε
    simpa [Ising3DModel] using
      tendsto_log_bounded_prefactor_div_log_betaC_sub Ising3DModel
        (hbounded.upperPrefactorLo_pos ε hε)
        (hbounded.upperPrefactorHi_pos ε hε)
        (hbounded.upperPrefactor_bounds ε hε)
  mass_prefactor_power_sandwich := hbounded.mass_prefactor_power_sandwich

end Exact3D
end StatMech
