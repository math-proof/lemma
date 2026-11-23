/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovThreeSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Independence.Integration
public import Theorem.v1.Atlas.Probability.code.CenteredConvergence
public import Theorem.Measure.Atlas.v1.Probability.code.CenteredConvergence

@[expose] public section

set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory Filter


noncomputable section

namespace KolmogorovThreeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

set_option maxHeartbeats 6400000 in
/-- The truncation `Yₙ = Xₙ · 1_{|Xₙ| ≤ A}` of the random variable `Xₙ` at threshold `A`,
i.e. `Yₙ(ω) = Xₙ(ω)` when `|Xₙ(ω)| ≤ A` and `0` otherwise. This is the key construction
in the Kolmogorov three-series theorem. -/
def truncatedRV (X : ℕ → Ω → ℝ) (A : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => X n ω * Set.indicator {ω | |X n ω| ≤ A} 1 ω

end KolmogorovThreeSeries
end
