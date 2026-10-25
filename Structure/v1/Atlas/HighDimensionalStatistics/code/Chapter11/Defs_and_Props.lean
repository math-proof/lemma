/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter11/Defs_and_Props.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.RingTheory.MvPolynomial.Homogeneous
set_option maxHeartbeats 800000


noncomputable section

open scoped SchwartzMap

open MeasureTheory TemperedDistribution Filter ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Chapter11

/-- A constant-coefficient differential operator on tempered distributions: a
nonzero continuous `ℂ`-linear endomorphism of `𝓢'(E, ℂ)`. -/
structure ConstCoeffDiffOp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The underlying continuous linear map on tempered distributions. -/
  toDistribCLM : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)
  /-- The operator is nonzero. -/
  ne_zero : toDistribCLM ≠ 0

end Chapter11
end
