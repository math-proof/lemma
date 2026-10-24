/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/StoppedSumSqUI.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TheoryOfProbability.code.WaldSecondEquation
import Lemma.Measure.Atlas.v1.TheoryOfProbability.code.WaldSecondEquation

open MeasureTheory ProbabilityTheory MeasureTheory.Measure Finset ENNReal Filter

/-- Let `X₁, X₂, …` be i.i.d. with `E[X₁] = 0` and `E[X₁²] < ∞`, and let `T` be a
stopping time (relative to the natural filtration) with `E[T] < ∞`. Writing
`Sₖ = X₁ + ⋯ + Xₖ`, the random variable `max_{0 ≤ k ≤ T} Sₖ²` is integrable. This
is used in conjunction with Wald's second equation to control stopped partial-sum
processes. -/
