/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ContinuousMapping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory Filter ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction

noncomputable section

namespace ProbabilityTheory

/-- **Weak convergence** of a sequence of probability measures on `ℝ`.

`μs n ⇒ μ` iff `∫ f d(μs n) → ∫ f dμ` for every bounded continuous `f : ℝ →ᵇ ℝ`,
which is the Portmanteau characterization of weak convergence (Lecture 12). -/
def WeakConvergenceMeasures (μs : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μs n)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  ∀ f : ℝ →ᵇ ℝ,
    Tendsto (fun n ↦ ∫ x, f x ∂(μs n)) atTop (𝓝 (∫ x, f x ∂μ))
