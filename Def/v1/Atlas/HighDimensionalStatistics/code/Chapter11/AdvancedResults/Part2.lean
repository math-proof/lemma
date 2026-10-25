/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/AdvancedResults.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.FourierMultiplier
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props.Part3
import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter11.AdvancedResults.Part2
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap FourierTransform Laplacian BigOperators Pointwise

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

namespace Chapter11

variable {n : ℕ}

/-- The fractional Laplacian `(-Δ)^{s/2}` defined as the Fourier multiplier with
symbol `(2π|ξ|)^s`. -/
def fractionalLaplacian (n : ℕ) (s : ℝ) : 𝓢'(Rn n, ℂ) →L[ℂ] 𝓢'(Rn n, ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ
    (fun ξ : Rn n => ((2 * Real.pi * ‖ξ‖) ^ s : ℝ) : Rn n → ℂ)

end Chapter11
end
