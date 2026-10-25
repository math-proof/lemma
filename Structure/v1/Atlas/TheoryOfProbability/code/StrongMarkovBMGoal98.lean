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
import Abbrev.v1.Atlas.TheoryOfProbability.code.StrongMarkovBMGoal98
set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal


noncomputable section

namespace StrongMarkovBMGoal98

variable {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}

/-- Predicate bundling the defining properties of a `d`-dimensional Brownian motion
`B` with respect to a filtration `ℱ` and a family `P : Rd d → Measure Ω` of
starting-point laws. The fields encode: starting at `x` under `P x`, Gaussian
increments with the correct variance, independence of increments from the past,
adaptedness to `ℱ`, that each `P x` is a probability measure, measurability in
the starting point, and almost-sure continuity of sample paths. -/
structure IsBrownianMotion (B : ℝ≥0 → Ω → Rd d) (ℱ : Filtration ℝ≥0 m)
    (P : Rd d → Measure Ω) : Prop where
  start : ∀ x : Rd d, ∀ᵐ ω ∂(P x), B 0 ω = x
  increment_dist : ∀ (x : Rd d) (i : Fin d) (s t : ℝ≥0), s ≤ t →
    Measure.map (fun ω => B t ω i - B s ω i) (P x) = gaussianReal 0 (t - s)
  indep_increment : ∀ (x : Rd d) (i : Fin d) (s t : ℝ≥0), s ≤ t →
    Indep (ℱ s) (MeasurableSpace.comap (fun ω => B t ω i - B s ω i) inferInstance) (P x)
  adapted : ∀ (t : ℝ≥0), Measurable[ℱ t] (B t)
  isProbMeasure : ∀ x : Rd d, IsProbabilityMeasure (P x)
  measurable_P : Measurable P
  continuous_path : ∀ (x : Rd d), ∀ᵐ ω ∂(P x), ∀ i : Fin d,
    Continuous (fun t => B t ω i)

end StrongMarkovBMGoal98
end
