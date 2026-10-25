/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part4


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {hmass : FreePositiveSubcriticalMassBridge}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical D
        hmass where
  δ := h.δ
  δ_pos := h.δ_pos
  δ_le_betaC := h.δ_le_betaC
  scaleBase := h.scaleBase
  scaleBase_gt_one := h.scaleBase_gt_one
  relevantEigenvalue := h.relevantEigenvalue
  relevantEigenvalue_gt_one := h.relevantEigenvalue_gt_one
  predictedExponent_eq := by
    rw [hpred]
    exact h.predictedExponent_eq
  clock := h.clock
  cLo := h.cLo
  cLo_pos := h.cLo_pos
  cHi := h.cHi
  cHi_pos := h.cHi_pos
  clock_annulus := h.clock_annulus
  terminalLog := h.terminalLog
  terminalLogLimit := h.terminalLogLimit
  terminalLog_tendsto := h.terminalLog_tendsto
  accumulatedError := h.accumulatedError
  averageAccumulatedError_negligible :=
    h.averageAccumulatedError_negligible
  mass_pos := h.mass_pos
  log_mass_terminalAverageError := h.log_mass_terminalAverageError

end FreePositiveSubcriticalMassAnnulusScaleClockTerminalAverageErrorNearCritical
end Exact3D
end StatMech
