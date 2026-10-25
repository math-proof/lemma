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
import Theorem.Combinatorics.Enumerative.Partition.PentagonalJacobi.Part3
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

/-- The excited state E_{ℓ,μ} obtained from the ground state by jumping electrons
according to the partition μ.

Given a partition μ = (μ₁, μ₂, ..., μₖ) of some n, we start with the ℓ-ground state
and let the k highest electrons jump by μ₁, μ₂, ..., μₖ steps respectively. -/
noncomputable def excitedState (ell : ℤ) {n : ℕ} (mu : Nat.Partition n) : State where
  levels := excitedStateLevels ell mu
  finite_nonneg := excitedStateLevels_finite_nonneg ell mu
  finite_negative_missing := excitedStateLevels_finite_negative_missing ell mu

/-- The levels of an intermediate state after i jumps.
After i jumps, we have all levels below (ell - i), plus the i jump targets. -/
def intermediateStateLevels (ell : ℤ) (parts : List ℕ) (i : ℕ) (hi : i ≤ parts.length) : Set ℤ :=
  {p : ℤ | p < ell - i} ∪ 
  {p : ℤ | ∃ j : Fin i, p = ell - 1 - j + parts.get ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩}

end State
end Jacobi
end AlgebraicCombinatorics
