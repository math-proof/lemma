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

/-- The real-valued binomial measure `Bin(ℝ, n, p)` is a probability measure. -/
instance isProbabilityMeasure_Bin_real (n : ℕ) (p : I) :
    IsProbabilityMeasure Bin(ℝ, n, p) :=
  Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable

/-- The standardized binomial measure is a probability measure (pushforward of a
probability measure under a measurable affine map). -/
instance isProbabilityMeasure_standardizedBinomial (n : ℕ) (p : I) :
    IsProbabilityMeasure (standardizedBinomial n p) := by
  unfold standardizedBinomial
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Bundled `ProbabilityMeasure` wrapper around `standardizedBinomial n p`. -/
def standardizedBinomialProb (n : ℕ) (p : I) : ProbabilityMeasure ℝ :=
  ⟨standardizedBinomial n p, isProbabilityMeasure_standardizedBinomial n p⟩

/-- The **standard normal** distribution `N(0, 1)` packaged as a `ProbabilityMeasure ℝ`. -/
def stdNormalProb : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩
