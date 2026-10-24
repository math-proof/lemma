/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open ProbabilityTheory hiding stdGaussian
open MeasureTheory Real Set

noncomputable section

/-- The standard Gaussian measure on `ℝ` with mean `0` and variance `1`. -/
def stdGaussianMeasure : Measure ℝ := gaussianReal 0 1

variable {n : ℕ}
