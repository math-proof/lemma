/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/DeMoivreLaplace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.CDF
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.MeasureTheory.Measure.LevyConvergence
open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval NNReal Topology Real


noncomputable section

namespace ProbabilityTheory

/-- **Standardized binomial distribution**.

The law of `(Sₙ − np) / √(np(1−p))` where `Sₙ ~ Binomial(n, p)`. This is the
standardized sum appearing in the DeMoivre–Laplace limit theorem. -/
def standardizedBinomial (n : ℕ) (p : I) : Measure ℝ :=
  Bin(ℝ, n, p).map (fun x : ℝ ↦ (x - ↑n * ↑p) / Real.sqrt (↑n * ↑p * (1 - ↑p)))

end ProbabilityTheory
end
