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
import Def.Combinatorics.Enumerative.Partition.PentagonalJacobi.Part6
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

/-- The excited state has finitely many nonnegative levels. -/
theorem excitedStateLevels_finite_nonneg (ell : ℤ) {n : ℕ} (mu : Nat.Partition n) :
    Set.Finite {p : Level | p ≥ 0 ∧ p ∈ excitedStateLevels ell mu} := by
  unfold excitedStateLevels
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  let parts := mu.parts.sort (· ≥ ·)
  let k := parts.length
  -- The first set {p | p ≥ 0 ∧ p < ell - k} is finite
  have h1 : Set.Finite {p : Level | p ≥ 0 ∧ p < ell - k} :=
    Set.finite_Ico 0 (ell - k)
  -- The second set {p | ∃ i, p = ...} is finite (range of finite type)
  have h2 : Set.Finite {p : Level | ∃ i : Fin k, p = ell - 1 - i + parts.get (i.cast (by omega))} := by
    have : {p : Level | ∃ i : Fin k, p = ell - 1 - i + parts.get (i.cast (by omega))} ⊆
           Set.range (fun i : Fin k => ell - 1 - i + parts.get (i.cast (by omega))) := by
      intro p hp
      obtain ⟨i, hi⟩ := hp
      exact ⟨i, hi.symm⟩
    exact Set.Finite.subset (Set.finite_range _) this
  -- The target set is a subset of the union
  apply Set.Finite.subset (h1.union h2)
  intro p ⟨hp_nonneg, hp_mem⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  cases hp_mem with
  | inl h => left; exact ⟨hp_nonneg, h⟩
  | inr h => right; exact h

/-- The excited state has finitely many missing negative levels. -/
theorem excitedStateLevels_finite_negative_missing (ell : ℤ) {n : ℕ} (mu : Nat.Partition n) :
    Set.Finite {p : Level | p < 0 ∧ p ∉ excitedStateLevels ell mu} := by
  -- A negative level p is missing if:
  -- 1. p ≥ ell - k (not in the unbounded part)
  -- 2. p is not one of the finitely many jumped levels
  -- The missing negative levels are a subset of {p | ell - k ≤ p < 0}
  apply Set.Finite.subset
  · exact Set.finite_Icc (ell - ↑((mu.parts.sort (· ≥ ·)).length)) (-1) |>.image (fun x => x)
  · intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    obtain ⟨hp_neg, hp_nmem⟩ := hp
    unfold excitedStateLevels at hp_nmem
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hp_nmem
    simp only [Set.mem_image, Set.mem_Icc]
    use p
    constructor
    · constructor
      · exact hp_nmem.1
      · linarith
    · rfl

end State
end Jacobi
end AlgebraicCombinatorics
