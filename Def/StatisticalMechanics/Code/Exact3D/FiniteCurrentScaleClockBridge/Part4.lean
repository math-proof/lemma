/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassAnnulusScaleClock_of_annulusScaleClockAverageError
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge)
    (havg :
      FreePositiveSubcriticalMassAnnulusScaleClockAverageErrorNearCritical C
        hmass) :
    FreePositiveSubcriticalMassAnnulusScaleClockNearCritical C hmass where
  δ := havg.δ
  δ_pos := havg.δ_pos
  δ_le_betaC := havg.δ_le_betaC
  scaleBase := havg.scaleBase
  scaleBase_gt_one := havg.scaleBase_gt_one
  relevantEigenvalue := havg.relevantEigenvalue
  relevantEigenvalue_gt_one := havg.relevantEigenvalue_gt_one
  predictedExponent_eq := havg.predictedExponent_eq
  clock := havg.clock
  cLo := havg.cLo
  cLo_pos := havg.cLo_pos
  cHi := havg.cHi
  cHi_pos := havg.cHi_pos
  clock_annulus := havg.clock_annulus
  logError := fun β => havg.terminalLog β + havg.accumulatedError β
  mass_pos := havg.mass_pos
  logError_negligible := by
    exact
      (tendsto_bounded_terminal_add_error_div_log_betaC_sub_of_annulus_clock_average
        Ising3DModel havg.clock havg.terminalLog havg.accumulatedError
        havg.terminalLogBound havg.relevantEigenvalue havg.cLo havg.cHi
        havg.relevantEigenvalue_gt_one havg.cLo_pos havg.cHi_pos
        (by simpa [Ising3DModel] using havg.clock_annulus)
        (by simpa [Ising3DModel] using havg.terminalLog_eventually_abs_le)
        (by
          simpa [Ising3DModel] using
            havg.averageAccumulatedError_negligible))
  log_mass_scaleClock := by
    intro β hβ
    calc
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
          -(Real.log havg.scaleBase) * havg.clock β +
            havg.terminalLog β + havg.accumulatedError β :=
        havg.log_mass_averageError β hβ
      _ =
          -(Real.log havg.scaleBase) * havg.clock β +
            (havg.terminalLog β + havg.accumulatedError β) := by
        ring

end Exact3D
end StatMech
