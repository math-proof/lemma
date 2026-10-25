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
import Def.Combinatorics.Enumerative.Partition.PentagonalJacobi.Part7
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

/-- The intermediate state levels have finitely many nonnegative elements. -/
theorem intermediateStateLevels_finite_nonneg (ell : ℤ) (parts : List ℕ) (i : ℕ) (hi : i ≤ parts.length) :
    Set.Finite {p : ℤ | p ≥ 0 ∧ p ∈ intermediateStateLevels ell parts i hi} := by
  unfold intermediateStateLevels
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  have h1 : Set.Finite {p : ℤ | p ≥ 0 ∧ p < ell - i} := Set.finite_Ico 0 (ell - i)
  have h2 : Set.Finite {p : ℤ | ∃ j : Fin i, p = ell - 1 - j + parts.get ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩} := by
    apply Set.Finite.subset (Set.finite_range (fun j : Fin i => ell - 1 - j + parts.get ⟨j.val, Nat.lt_of_lt_of_le j.isLt hi⟩))
    intro p ⟨j, hj⟩
    exact ⟨j, hj.symm⟩
  apply Set.Finite.subset (h1.union h2)
  intro p ⟨hp_nonneg, hp_mem⟩
  cases hp_mem with
  | inl hp => left; exact ⟨hp_nonneg, hp⟩
  | inr hp => right; exact hp

/-- The intermediate state levels have finitely many negative missing elements. -/
theorem intermediateStateLevels_finite_neg_missing (ell : ℤ) (parts : List ℕ) (i : ℕ) (hi : i ≤ parts.length) :
    Set.Finite {p : ℤ | p < 0 ∧ p ∉ intermediateStateLevels ell parts i hi} := by
  unfold intermediateStateLevels
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt]
  apply Set.Finite.subset (Set.finite_Ico (ell - i) 0)
  intro p ⟨hp_neg, hp_ge, _⟩
  exact ⟨hp_ge, hp_neg⟩

end State
end Jacobi
end AlgebraicCombinatorics
