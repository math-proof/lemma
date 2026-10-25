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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part9


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
        C hmass) :
    FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
      D hmass where
  lowerPrefactor := h.lowerPrefactor
  upperPrefactor := h.upperPrefactor
  window := h.window
  lowerPrefactor_pos := h.lowerPrefactor_pos
  upperPrefactor_pos := h.upperPrefactor_pos
  window_pos := h.window_pos
  mass_constant_prefactor_power_sandwich_on_Ioo := by
    intro ε hε β hβ
    simpa [hpred] using
      h.mass_constant_prefactor_power_sandwich_on_Ioo ε hε β hβ

end FreePositiveSubcriticalMassFKBetaCConstantPrefactorWeakIooSandwichNearCritical
end Exact3D
end StatMech
