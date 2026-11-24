module
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Abbrev.v1.Atlas.HighDimensionalStatistics.code.Chapter11.Defs_and_Props.Part3
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter11.AdvancedResults.Part2
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/AdvancedResults.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped SchwartzMap FourierTransform Laplacian BigOperators Pointwise

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

namespace Chapter11

variable {n : ℕ}

/-- Textbook alias for `fractionalLaplacian`. -/
abbrev def_11_11_fractional_laplacian := @fractionalLaplacian

end Chapter11
end
