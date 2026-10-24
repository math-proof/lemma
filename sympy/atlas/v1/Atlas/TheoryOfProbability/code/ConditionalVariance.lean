/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ConditionalVariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.CondVar
import Mathlib.Probability.Martingale.Basic

open MeasureTheory ProbabilityTheory Filter

noncomputable section

section AlternativeFormula

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}
