/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/SecondMoment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.Variance

set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Filter

namespace SecondMoment

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω}

/-- Shorthand for the variance $\mathrm{Var}(X) = \mathbb{E}[(X - \mathbb{E}X)^2]$
of a random variable $X$ with respect to a measure $\mu$. -/
noncomputable abbrev Var (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ProbabilityTheory.variance X μ

end SecondMoment

namespace ProbabilityTheory
