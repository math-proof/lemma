/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TheoryOfProbability.code.FiniteMarkovChain
import Def.v1.Atlas.TheoryOfProbability.code.KolmogorovCycle
open MeasureTheory ProbabilityTheory Finset BigOperators


namespace StochasticMatrix

variable {M : ℕ}

/-- A **probability distribution** on the finite state space `Fin (M + 1)`: a function
`val : Fin (M + 1) → ℝ` whose values are nonnegative and sum to `1`. -/
structure Distribution (M : ℕ) where
  val : Fin (M + 1) → ℝ
  nonneg : ∀ i, 0 ≤ val i
  sum_one : ∑ i, val i = 1

end StochasticMatrix
