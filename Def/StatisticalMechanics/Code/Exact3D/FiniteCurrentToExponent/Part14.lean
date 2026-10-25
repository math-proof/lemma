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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part15


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical C fkMass) :
    FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical D fkMass where
  pδ := h.pδ
  pδ_pos := h.pδ_pos
  massPrefactor := h.massPrefactor
  massPrefactor_pos := h.massPrefactor_pos
  massPrefactor_log_negligible := h.massPrefactor_log_negligible
  mass_scaling := by
    intro p hp
    simpa [hpred] using h.mass_scaling p hp

end FreePositiveSubcriticalMassFKPCExactPowerLawNearCritical
end Exact3D
end StatMech
