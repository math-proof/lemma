/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics Project Contributors
Authors: AlgebraicCombinatorics Project Contributors
-/
import Mathlib
import Def.Combinatorics.Enumerative.Partition.Basics.Part8
import Theorem.Combinatorics.Enumerative.Partition.PentagonalJacobi.Part4
open scoped Nat PowerSeries

/-!
# Euler's Pentagonal Number Theorem and Jacobi's Triple Product Identity

This file formalizes Euler's pentagonal number theorem and Jacobi's triple product identity,
following the treatment in the AlgebraicCombinatorics textbook.

## Main definitions

* `pentagonalNumber` : The k-th pentagonal number w_k = (3k - 1) * k / 2
* `Level` : A "level" is a half-integer p + 1/2 for some integer p (used in the proof)
* `State` : A "state" is a set of levels containing all but finitely many negative levels
  and only finitely many positive levels
* `State.energy` : The energy of a state
* `State.parnum` : The particle number of a state

## Main results

* `pentagonalNumber_nonneg` : Pentagonal numbers are nonnegative
* `euler_pentagonal_number_theorem` : ∏_{k≥1} (1 - x^k) = ∑_{k∈ℤ} (-1)^k x^{w_k}
* `jacobi_triple_product` : Jacobi's triple product identity
* `partition_recursive` : Recursive formula for partition numbers using pentagonal numbers
* `euler_sum_divisors_recursive` : Euler's recursion for the sum of divisors function

## References

* AlgebraicCombinatorics textbook, Section on Partitions/PentagonalJacobi.tex
* [Bell, 2006] for history of Euler's pentagonal number theorem
* [Borcherds' proof via Cameron's book, §8.3]

## Tags

pentagonal number, Euler, Jacobi triple product, partitions, formal power series
-/


namespace AlgebraicCombinatorics

section Jacobi

variable {R : Type*} [CommRing R]

namespace State

/-- The intermediate state after i jumps. -/
noncomputable def intermediateState (ell : ℤ) (parts : List ℕ) (i : ℕ) (hi : i ≤ parts.length) : State where
  levels := intermediateStateLevels ell parts i hi
  finite_nonneg := intermediateStateLevels_finite_nonneg ell parts i hi
  finite_negative_missing := intermediateStateLevels_finite_neg_missing ell parts i hi

/-- The bijection Φ_ℓ : {partitions} → {states with particle number ℓ}.
Here we use Σ n, Nat.Partition n to represent all partitions. -/
noncomputable def partitionToState (ell : ℤ) : (Σ n, Nat.Partition n) → State :=
  fun ⟨_, mu⟩ => excitedState ell mu

/-- The base level of a state is the smallest level not in S.
This is well-defined because:
1. The set of levels not in S is nonempty (S can't contain all integers)
2. The set is bounded below (only finitely many negative levels are missing) -/
noncomputable def baseLevel (S : State) : ℤ :=
  sInf {p : ℤ | p ∉ S.levels}

/-- The excited levels of a state (levels in S that are ≥ baseLevel). -/
noncomputable def excitedLevelsSet (S : State) : Set ℤ :=
  S.levels ∩ {p | p ≥ baseLevel S}

end State
end Jacobi
end AlgebraicCombinatorics
