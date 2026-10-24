/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TheoryOfProbability.code.FiniteMarkovChain

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

/-- A **probability distribution** on the finite state space `Fin (M + 1)`: a function
`val : Fin (M + 1) → ℝ` whose values are nonnegative and sum to `1`. -/
structure Distribution (M : ℕ) where
  val : Fin (M + 1) → ℝ
  nonneg : ∀ i, 0 ≤ val i
  sum_one : ∑ i, val i = 1

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

/-- `NNReal`-valued version of `pathProduct`: the product of forward transition probabilities
along the path, packaged as a nonnegative real. -/
noncomputable def listPathProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → NNReal
  | [] => 1
  | [_] => 1
  | a :: b :: rest => ⟨P.prob a b, P.nonneg a b⟩ * listPathProduct P (b :: rest)

/-- The product of ratios `P(xᵢ, xᵢ₊₁) / P(xᵢ₊₁, xᵢ)` along a path. This is the quantity
that defines the "cycle weight" used to construct a reversible measure from Kolmogorov's
cycle condition. -/
noncomputable def listRatioProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → NNReal
  | [] => 1
  | [_] => 1
  | a :: b :: rest =>
    (⟨P.prob a b, P.nonneg a b⟩ / ⟨P.prob b a, P.nonneg b a⟩) * listRatioProduct P (b :: rest)

/-- The **cycle weight** of state `j` relative to a reference state `i₀`: defined as the
`listRatioProduct` along some (classically chosen) positive-probability path from `i₀` to `j`.
For chains satisfying Kolmogorov's cycle condition this value is path-independent
(`cycleWeight_path_independent`) and yields the unique-up-to-scaling reversible measure. -/
noncomputable def cycleWeight (P : StochasticMatrix M) (hirr : P.IsIrreducible)
    (i₀ : Fin (M + 1)) (j : Fin (M + 1)) : NNReal :=
  listRatioProduct P (Classical.choose (hirr.exists_path i₀ j))
