/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TheoryOfProbability.code.FiniteMarkovChain
import Structure.v1.Atlas.TheoryOfProbability.code.KolmogorovCycle
open MeasureTheory ProbabilityTheory Finset BigOperators


namespace StochasticMatrix

variable {M : ℕ}

/-- A distribution `π` is **stationary** for the transition matrix `P` if `π P = π`, i.e.,
`∑ᵢ π(i) P(i, j) = π(j)` for every state `j`. -/
def IsStationary (P : StochasticMatrix M) (π : Distribution M) : Prop :=
  ∀ j, ∑ i, π.val i * P.prob i j = π.val j

/-- The **detailed balance** (reversibility) equations between `P` and `π`:
`π(i) P(i,j) = π(j) P(j,i)` for all states `i, j`. -/
def DetailedBalance (P : StochasticMatrix M) (π : Distribution M) : Prop :=
  ∀ i j : Fin (M + 1), π.val i * P.prob i j = π.val j * P.prob j i

/-- A transition matrix `P` is **reversible** if there exists a distribution `π` that is
both stationary and satisfies the detailed balance equations with `P`. -/
def IsReversible (P : StochasticMatrix M) : Prop :=
  ∃ π : Distribution M, P.IsStationary π ∧ P.DetailedBalance π

/-- The product of transition probabilities along a path: for a list of states
`[x₀, x₁, …, x_k]`, returns `∏ᵢ P(xᵢ, xᵢ₊₁)`. Empty and singleton lists give `1`. -/
def pathProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: rest => P.prob a b * P.pathProduct (b :: rest)

end StochasticMatrix
