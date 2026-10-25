/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
open MeasureTheory Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology


namespace TheoryOfProbability3

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- A *decreasing filtration* on `(Ω, m0)` is a sequence of sub-σ-algebras
`ℱ n ⊆ m0` that is antitone in `n` (i.e. `ℱ 0 ⊇ ℱ 1 ⊇ ℱ 2 ⊇ ⋯`). This is the
natural index structure for backwards martingales, where conditioning
σ-algebras shrink as `n → ∞`. -/
structure DecreasingFiltration (Ω : Type*) (m0 : MeasurableSpace Ω) where
  seq : ℕ → MeasurableSpace Ω
  antitone' : Antitone seq
  le' : ∀ n, seq n ≤ m0

end TheoryOfProbability3
