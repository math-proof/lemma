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
import Def.Combinatorics.Enumerative.Partition.PentagonalJacobi
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

/-- Key bound: w_k ≥ |k| for k ≠ 0.
This is because for k ≥ 1: (3k-1)k/2 ≥ k, and for k ≤ -1: (3|k|+1)|k|/2 ≥ |k|. -/
theorem pentagonalNumber_ge_natAbs {k : ℤ} (hk : k ≠ 0) :
    pentagonalNumber k ≥ k.natAbs := by
  unfold pentagonalNumber
  by_cases hpos : k > 0
  · have hk1 : k ≥ 1 := hpos
    have h1 : (3 * k - 1) * k / 2 ≥ k := by
      have h2 : 3 * k - 1 ≥ 2 := by omega
      have h3 : (3 * k - 1) * k ≥ 2 * k := by nlinarith
      omega
    have habs : k.natAbs = k.toNat := by omega
    rw [habs]
    exact Int.toNat_le_toNat h1
  · push Not at hpos
    have hneg : k < 0 := by omega
    let m := -k
    have hm : m ≥ 1 := by omega
    have heq : (3 * k - 1) * k = (3 * m + 1) * m := by ring
    have h1 : (3 * m + 1) * m / 2 ≥ m := by
      have h2 : 3 * m + 1 ≥ 2 := by omega
      have h3 : (3 * m + 1) * m ≥ 2 * m := by nlinarith
      omega
    have habs : k.natAbs = m.toNat := by omega
    rw [heq, habs]
    exact Int.toNat_le_toNat h1

/-- The set of k with pentagonalNumber k < n is finite, since pentagonal numbers grow quadratically. -/
theorem pentagonal_below_finite (n : ℕ) : Set.Finite {k : ℤ | pentagonalNumber k < n} := by
  have h : {k : ℤ | pentagonalNumber k < n} ⊆ Set.Icc (-(n : ℤ)) n := by
    intro k hk
    simp only [Set.mem_ofPred_eq] at hk
    simp only [Set.mem_Icc]
    by_cases hk0 : k = 0
    · subst hk0; omega
    · have hge := pentagonalNumber_ge_natAbs hk0
      have hlt : k.natAbs < n := Nat.lt_of_le_of_lt hge hk
      constructor
      · have h1 : -(k.natAbs : ℤ) ≤ k := by
          have := Int.neg_le_neg_iff.mpr (Int.le_natAbs (a := -k))
          simp at this
          convert this using 1
          simp
        omega
      · have h2 : k ≤ k.natAbs := Int.le_natAbs
        omega
  exact Set.Finite.subset (Set.finite_Icc _ _) h

end AlgebraicCombinatorics
