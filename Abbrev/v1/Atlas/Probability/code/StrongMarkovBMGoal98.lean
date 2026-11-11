/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovBMGoal98.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal


noncomputable section

namespace StrongMarkovBMGoal98

variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}

/-- Abbreviation for `d`-dimensional Euclidean space `ℝ^d`, represented as functions
`Fin d → ℝ`. -/
abbrev Rd (d : ℕ) := Fin d → ℝ

end StrongMarkovBMGoal98
end
