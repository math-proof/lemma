/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/LindebergFeller.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Probability.Distributions.Gaussian.CharFun

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex Finset
open scoped Topology BoundedContinuousFunction NNReal


noncomputable section

namespace ProbabilityTheory

/-- The **Lindeberg condition** for a triangular array `X n k` of random variables on `(Ω, μ)`:
for every `ε > 0`, the truncated second moment
`∑ₖ ∫ (X n k)² · 𝟙{|X n k| > ε} dμ` tends to `0` as `n → ∞`. This is the key hypothesis of the
Lindeberg–Feller central limit theorem. -/
def LindebergConditionTriangular {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ)
    atTop (𝓝 0)

end ProbabilityTheory
end
