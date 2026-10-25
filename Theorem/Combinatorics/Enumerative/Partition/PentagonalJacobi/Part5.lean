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
import Def.Combinatorics.Enumerative.Partition.PentagonalJacobi.Part8
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

/-- The excited levels form a finite set. -/
theorem excitedLevelsSet_finite (S : State) : Set.Finite (excitedLevelsSet S) := by
  unfold excitedLevelsSet
  by_cases h : baseLevel S ≥ 0
  · have hsub : S.levels ∩ {p | p ≥ baseLevel S} ⊆ {p | p ≥ 0 ∧ p ∈ S.levels} := by
      intro p ⟨hp_mem, hp_ge⟩; exact ⟨le_trans h hp_ge, hp_mem⟩
    exact Set.Finite.subset S.finite_nonneg hsub
  · push Not at h
    have h1 : S.levels ∩ {p | p ≥ baseLevel S} ⊆
              {p | p ≥ 0 ∧ p ∈ S.levels} ∪ Set.Ico (baseLevel S) 0 := by
      intro p ⟨hp_mem, hp_ge⟩
      by_cases hp_nonneg : p ≥ 0
      · left; exact ⟨hp_nonneg, hp_mem⟩
      · push Not at hp_nonneg; right; simp only [Set.mem_Ico]; exact ⟨hp_ge, hp_nonneg⟩
    apply Set.Finite.subset _ h1
    exact Set.Finite.union S.finite_nonneg (Set.finite_Ico (baseLevel S) 0)

end State
end Jacobi
end AlgebraicCombinatorics
