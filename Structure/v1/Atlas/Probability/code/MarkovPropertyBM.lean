/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MarkovPropertyBM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Notation.v1.Atlas.Probability.code.MarkovPropertyBM
open MeasureTheory ProbabilityTheory MeasurableSpace Filter
open scoped NNReal ENNReal


public noncomputable section

namespace BrownianMotion

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `IsBrownianMotion B ℱ μ` asserts that the family `B : NNReal → Ω → E` is a `d`-dimensional
Brownian motion under `μ` adapted to the filtration `ℱ`. It packages the standard defining
properties: `B 0 = 0` almost surely, independent increments with respect to the filtration,
adaptedness, almost-sure continuous paths, and measurability of each increment. -/
structure IsBrownianMotion (B : NNReal → Ω → E) (ℱ : Filtration NNReal m) (μ : Measure Ω) : Prop where
  zero : ∀ᵐ ω ∂μ, B 0 ω = 0
  indep_increment : ∀ (s t : NNReal), s ≤ t →
    Indep (ℱ s) (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) μ
  adapted : ∀ (t : NNReal), Measurable[ℱ t] (B t)
  continuous_path : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω)
  meas_increment : ∀ (s t : NNReal), s ≤ t → Measurable (fun ω => B t ω - B s ω)

end BrownianMotion
end
