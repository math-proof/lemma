/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentScaleClockBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part16
import Theorem.StatisticalMechanics.Code.Exact3D.ScaleClockBridge.Part2
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentScaleClockBridge.Part17


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassCriticalDistanceClockComparisonTerminalAverageErrorNearCritical
    (C : RGCertificate Ising3DModel)
    (hmass : FreePositiveSubcriticalMassBridge) where
  δ : ℝ
  δ_pos : 0 < δ
  δ_le_betaC : δ ≤ Ising.betaC 3
  scaleBase : ℝ
  scaleBase_gt_one : 1 < scaleBase
  relevantEigenvalue : ℝ
  relevantEigenvalue_gt_one : 1 < relevantEigenvalue
  predictedExponent_eq :
    C.predictedExponent = Real.log scaleBase / Real.log relevantEigenvalue
  clock : ℝ → ℝ
  clockError_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        (clock β -
            criticalDistanceScaleClock Ising3DModel relevantEigenvalue β) /
          (-Real.log (Ising.betaC 3 - β)))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  terminalLog : ℝ → ℝ
  terminalLogLimit : ℝ
  terminalLog_tendsto :
    Filter.Tendsto terminalLog
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)))
      (nhds terminalLogLimit)
  accumulatedError : ℝ → ℝ
  averageAccumulatedError_negligible :
    Filter.Tendsto
      (fun β : ℝ => accumulatedError β / clock β)
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  mass_pos :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      0 < freeSelectedPositiveSubcriticalMass hmass β
  log_mass_terminalAverageError :
    ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
      Real.log (freeSelectedPositiveSubcriticalMass hmass β) =
        -(Real.log scaleBase) * clock β + terminalLog β +
          accumulatedError β

end Exact3D
end StatMech
