/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TheoryOfProbability.code.FiniteMarkovChain
open MeasureTheory ProbabilityTheory Finset BigOperators


namespace StochasticMatrix

variable {M : ℕ}

/-- The `n`-th matrix power of a stochastic transition matrix `P`. Entry `(i,j)` represents
the probability of moving from state `i` to state `j` in exactly `n` steps. -/
def matPow (P : StochasticMatrix M) : ℕ → (Fin (M + 1) → Fin (M + 1) → ℝ)
  | 0 => fun i j => if i = j then 1 else 0
  | n + 1 => fun i j => ∑ k, P.prob i k * P.matPow n k j

/-- A stochastic matrix `P` is **irreducible** if for every pair of states `i, j` there is some
positive number of steps `n` such that `P^n i j > 0`; i.e., every state is reachable from every
other state in finitely many steps. -/
def IsIrreducible (P : StochasticMatrix M) : Prop :=
  ∀ i j : Fin (M + 1), ∃ n : ℕ, 0 < n ∧ 0 < P.matPow n i j

end StochasticMatrix
