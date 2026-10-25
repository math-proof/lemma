/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovThreeSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Independence.Integration
import Theorem.v1.Atlas.TheoryOfProbability.code.CenteredConvergence
import Lemma.Measure.Atlas.v1.TheoryOfProbability.code.CenteredConvergence
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
