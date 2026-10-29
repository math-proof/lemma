/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovPropertyBM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith.NNRealPreprocessor
import Structure.v1.Atlas.TheoryOfProbability.code.MarkovPropertyBM
open MeasureTheory ProbabilityTheory MeasurableSpace Filter
open scoped NNReal ENNReal


noncomputable section

namespace BrownianMotion

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The time-shifted path of a Brownian motion: `shiftPath B s ω` is the function
`t ↦ B (s + t) ω`, i.e. the path of `B` starting from time `s` instead of `0`. -/
def shiftPath (B : NNReal → Ω → E) (s : NNReal) : Ω → (NNReal → E) :=
  fun ω t => B (s + t) ω

/-- The law on path space of the centered shifted path `t ↦ B (s + t) ω - B s ω`. By
independence and stationarity of Brownian increments, this measure does not depend on `s`
and equals the law of standard Brownian motion. -/
def shiftedPathLaw (B : NNReal → Ω → E) (μ : Measure Ω) (s : NNReal) :
    Measure (NNReal → E) :=
  Measure.map (fun ω t => B (s + t) ω - B s ω) μ

/-- The expectation of a path functional `Y` under the law of Brownian motion started from
the point `x ∈ E`. Operationally, it integrates `Y (t ↦ x + f t)` against the law of the
centered shifted path `f`. This is the function `φ(x) = E_x Y` that appears as the
conditional expectation in the Markov property. -/
def pathExpectation (B : NNReal → Ω → E) (μ : Measure Ω) (s : NNReal)
    (Y : (NNReal → E) → ℝ) (x : E) : ℝ :=
  ∫ f, Y (fun t => x + f t) ∂(shiftedPathLaw B μ s)

end BrownianMotion
end
