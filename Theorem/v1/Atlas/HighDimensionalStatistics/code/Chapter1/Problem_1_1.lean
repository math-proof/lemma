/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter1/Problem_1_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_11
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Normed.Group.Constructions
open MeasureTheory ProbabilityTheory

/-- **Problem 1.1 (weighted sums of sub-exponentials).** For independent
sub-exponential variables `X₁,…,Xₙ` with parameter `λ`, there is a constant
`C > 0` such that for any coefficients `a` and any `t > 0`,
`P(|∑ aᵢXᵢ| > t) ≤ 2 exp(-C · min(t² / (λ² ∑ aᵢ²), t / (λ ‖a‖)))`. -/


noncomputable section

end
