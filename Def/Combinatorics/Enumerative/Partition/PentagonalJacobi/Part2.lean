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
import Instance.Combinatorics.Enumerative.Partition.PentagonalJacobi
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

section FPS

variable {R : Type*} [CommRing R]

/-- Helper: Check if n is a pentagonal number and return the corresponding k.
Returns none if n is not a pentagonal number.

This is computable for any given n by checking a finite range of k values,
since pentagonal numbers grow quadratically. -/
def pentagonalNumberInverse (n : ℕ) : Option ℤ :=
  -- For any n, we only need to check k in a bounded range
  -- since w_k grows roughly like 3k²/2
  let bound := n + 1
  -- Check positive k first, then negative k
  let posResult := (List.range bound).find? fun k => pentagonalNumber k = n
  match posResult with
  | some k => some k
  | none =>
    let negResult := (List.range bound).find? fun k => pentagonalNumber (-(k : ℤ) - 1) = n
    match negResult with
    | some k => some (-(k : ℤ) - 1)
    | none => none

/-- The coefficient of x^n in the pentagonal series.
Returns (-1)^k if n = w_k for some k, and 0 otherwise.

Note: We use `k.natAbs` to compute the sign correctly for negative k,
since (-1)^k = (-1)^|k| for integers (as (-1)^{-m} = (-1)^m). -/
def pentagonalCoeff (n : ℕ) : ℤ :=
  match pentagonalNumberInverse n with
  | some k => (-1 : ℤ) ^ k.natAbs
  | none => 0

/-- The alternating sum ∑_{k∈ℤ} (-1)^k x^{w_k} as a formal power series.
This is well-defined because the pentagonal numbers grow quadratically.

We define the coefficient at n to be (-1)^k if n = w_k for some k, and 0 otherwise.
Since pentagonal numbers are injective, this is well-defined. -/
noncomputable def pentagonalSeries : R⟦X⟧ :=
  PowerSeries.mk fun n => (pentagonalCoeff n : R)

/-- The Euler product ∏_{k≥1} (1 - x^k).

This is defined using the discrete topology on R, which ensures the infinite product
is well-defined via Mathlib's infrastructure for infinite products of power series.
The product is multipliable because the order of (1 - X^k) is k, which tends to infinity. -/
noncomputable def eulerProduct : R⟦X⟧ :=
  letI : TopologicalSpace R := ⊥
  haveI : DiscreteTopology R := ⟨rfl⟩
  letI := PowerSeries.WithPiTopology.instTopologicalSpace (R := R)
  ∏' k, (1 - PowerSeries.X ^ (k + 1) : R⟦X⟧)

end FPS
end AlgebraicCombinatorics
