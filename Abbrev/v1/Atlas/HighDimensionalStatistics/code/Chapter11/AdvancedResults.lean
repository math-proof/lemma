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
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap FourierTransform Laplacian BigOperators Pointwise

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

namespace Chapter11

/-- Shorthand for the Euclidean space `ℝⁿ`. -/
abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)

end Chapter11
end
