/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StrongMarkovBMGoal98.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.MeasurableIntegral
set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal


@[expose] public noncomputable section

namespace StrongMarkovBMGoal98

variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}

/-- Abbreviation for `d`-dimensional Euclidean space `ℝ^d`, represented as functions
`Fin d → ℝ`. -/
abbrev Rd (d : ℕ) := Fin d → ℝ

end StrongMarkovBMGoal98
end
