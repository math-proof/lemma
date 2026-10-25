/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/Defs_and_Props.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Structure.v1.Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Chapter11

/-- A tempered distribution `E_sol` is a fundamental solution of `P` if
`P(E_sol) = δ₀`. -/
def IsTemperedFundamentalSolution
    (P : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (E_sol : 𝓢'(E, ℂ)) : Prop :=
  P E_sol = TemperedDistribution.delta 0

end Chapter11
end
