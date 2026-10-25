/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/PoissonConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Def.v1.Atlas.TheoryOfProbability.code.PoissonRV
open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped ENNReal NNReal Topology Nat


noncomputable section

namespace ProbabilityTheory

/-- `IsBernoulliRV X μ p` says that `X : Ω → ℕ` is a Bernoulli`(p)` random variable under
the measure `μ`: the parameter `p ∈ [0,1]` satisfies `P(X = 0) = 1 - p` and `P(X = 1) = p`. -/
def IsBernoulliRV {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → ℕ) (μ : Measure Ω) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧
    μ (X ⁻¹' {0}) = ENNReal.ofReal (1 - p) ∧
    μ (X ⁻¹' {1}) = ENNReal.ofReal p

end ProbabilityTheory
end
