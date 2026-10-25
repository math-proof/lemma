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
import Inductive.Combinatorics.Enumerative.Partition.PentagonalJacobi
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

/-- The explicit set of levels in an excited state E_{ℓ,μ}.
E_{ℓ,μ} = {p | p < ℓ-k} ∪ {ℓ-1-i+μ_i | i ∈ {0,...,k-1}}
where k is the number of parts and μ_i are the parts (sorted in decreasing order).

We use `mu.parts.sort (· ≥ ·)` to get a canonical decreasing ordering of parts.
This ensures that the excited levels uniquely encode the partition, since with sorted
parts the function `i ↦ parts[i] - i` is strictly decreasing (hence injective). -/
def excitedStateLevels (ell : ℤ) {n : ℕ} (mu : Nat.Partition n) : Set Level :=
  let parts := mu.parts.sort (· ≥ ·)
  let k := parts.length
  {p : Level | p < ell - k} ∪
  {p : Level | ∃ i : Fin k, p = ell - 1 - i + parts.get (i.cast (by omega))}

end State
end Jacobi
end AlgebraicCombinatorics
