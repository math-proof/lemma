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
import Def.Combinatorics.Enumerative.Partition.PentagonalJacobi.Part5
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

/-- A state S is reachable from T by a sequence of jumps. -/
inductive ReachableByJumps (T : State) : State → Prop where
  | refl : ReachableByJumps T T
  | step (S S' : State) (p : Level) (q : ℕ) (hp : p ∈ S.levels)
      (hpq : p + q ∉ S.levels) (hq : q > 0) :
      ReachableByJumps T S → S' = S.jump p q hp hpq hq → ReachableByJumps T S'

/-- A state S is reachable from T by a sequence of jumps with total jump amount m.
This is an extended version of `ReachableByJumps` that tracks the cumulative sum
of all jump sizes, which is needed to prove energy formulas. -/
inductive ReachableByJumpsWithTotal (T : State) : State → ℕ → Prop where
  | refl : ReachableByJumpsWithTotal T T 0
  | step (S S' : State) (p : Level) (q : ℕ) (m : ℕ) (hp : p ∈ S.levels)
      (hpq : p + q ∉ S.levels) (hq : q > 0) :
      ReachableByJumpsWithTotal T S m → S' = S.jump p q hp hpq hq →
      ReachableByJumpsWithTotal T S' (m + q)

end State
end Jacobi
end AlgebraicCombinatorics
