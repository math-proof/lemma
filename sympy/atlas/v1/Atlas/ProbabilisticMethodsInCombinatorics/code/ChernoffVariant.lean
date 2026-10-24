/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ChernoffVariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option maxHeartbeats 400000

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal ENNReal

namespace ChernoffBound

/-- `IsBernoulliRV X p μ` says that under measure `μ`, the random variable `X` is almost
surely $\{0,1\}$-valued, takes the value $1$ with probability $p$, and $p \in [0,1]$. -/
def IsBernoulliRV {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : Ω → ℝ)
    (p : ℝ) (μ : Measure Ω) : Prop :=
  (∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) ∧
  μ {ω | X ω = 1} = ENNReal.ofReal p ∧
  0 ≤ p ∧ p ≤ 1

/-- Sharp Chernoff upper-tail bound (Theorem 5.0.5). For independent Bernoullis $X_i$ with
mean $\mu = \sum_i p_i > 0$ and $\varepsilon > 0$,
$\Pr\!\left(\sum_i X_i \ge (1+\varepsilon)\mu\right) \le \exp(-((1+\varepsilon)\log(1+\varepsilon) - \varepsilon)\mu)$. -/
end ChernoffBound
