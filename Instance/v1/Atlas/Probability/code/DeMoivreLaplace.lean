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
public import Def.Probability.DeMoivreLaplace

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval NNReal Topology Real


noncomputable section

namespace ProbabilityTheory

/-- The real-valued binomial measure `Bin(ℝ, n, p)` is a probability measure. -/
instance isProbabilityMeasure_Bin_real (n : ℕ) (p : I) :
    IsProbabilityMeasure Bin(ℝ, n, p) :=
  inferInstance

/-- The standardized binomial measure is a probability measure (pushforward of a
probability measure under a measurable affine map). -/
instance isProbabilityMeasure_standardizedBinomial (n : ℕ) (p : I) :
    IsProbabilityMeasure (standardizedBinomial n p) := by
  unfold standardizedBinomial
  infer_instance

end ProbabilityTheory
end
