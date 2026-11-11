/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/OptionalStoppingExpectation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Notation
open MeasureTheory
open scoped ProbabilityTheory


namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0}
  {f : ℕ → Ω → ℝ} {τ : Ω → ℕ∞}

end MeasureTheory
