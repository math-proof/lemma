/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/DeMoivreLaplace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.CDF
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Instance.v1.Atlas.Probability.code.DeMoivreLaplace

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval NNReal Topology Real


noncomputable section

namespace ProbabilityTheory

/-- Bundled `ProbabilityMeasure` wrapper around `standardizedBinomial n p`. -/
def standardizedBinomialProb (n : ℕ) (p : I) : ProbabilityMeasure ℝ :=
  ⟨standardizedBinomial n p, isProbabilityMeasure_standardizedBinomial n p⟩

/-- The **standard normal** distribution `N(0, 1)` packaged as a `ProbabilityMeasure ℝ`. -/
def stdNormalProb : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

end ProbabilityTheory
end
