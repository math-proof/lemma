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
import Abbrev.Combinatorics.Enumerative.Partition.PentagonalJacobi
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

/-- The generating function for partitions as a formal power series.
  ∑_{n∈ℕ} p(n) x^n -/
noncomputable def partitionGenFun : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => partitionCount n

/-- The inverse Euler product ∏_{k≥1} 1/(1-x^k).

This is defined using Mathlib's partition generating function framework.
By `Nat.Partition.genFun_eq_tprod`, this equals:
  ∏' i, (1 + ∑' j, X ^ ((i + 1) * (j + 1)))
which is the product ∏_{k≥1} (1 + X^k + X^{2k} + ...) = ∏_{k≥1} 1/(1-X^k). -/
noncomputable def eulerProductInv : ℤ⟦X⟧ := Nat.Partition.genFun (fun _ _ => 1)

end AlgebraicCombinatorics
