/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TheoryOfProbability.code.FiniteMarkovChain
import Def.v1.Atlas.TheoryOfProbability.code.KolmogorovCycle.Part2
open MeasureTheory ProbabilityTheory Finset BigOperators


namespace StochasticMatrix

variable {M : ℕ}

/-- **Kolmogorov's cycle condition** on a stochastic matrix `P`:
(1) `symm_support`: `P(x, y) > 0` implies `P(y, x) > 0`; and
(2) `cycle_prod`: for any loop `x₀, x₁, …, xₙ = x₀` whose reverse path has positive
probability, the product of forward transition probabilities along the loop equals the
product of backward transition probabilities. This is the necessary and sufficient
condition for the existence of a reversible measure for an irreducible chain. -/
structure KolmogorovCycleCondition (P : StochasticMatrix M) : Prop where
  symm_support : ∀ x y : Fin (M + 1), P.prob x y > 0 → P.prob y x > 0
  cycle_prod : ∀ (n : ℕ) (c : Fin (n + 1) → Fin (M + 1)), c 0 = c (Fin.last n) →
    (∏ i : Fin n, P.prob (c i.succ) (c i.castSucc)) > 0 →
    (∏ i : Fin n, P.prob (c i.castSucc) (c i.succ)) =
      (∏ i : Fin n, P.prob (c i.succ) (c i.castSucc))

end StochasticMatrix
