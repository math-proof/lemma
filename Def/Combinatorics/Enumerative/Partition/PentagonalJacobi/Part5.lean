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
import Structure.Combinatorics.Enumerative.Partition.PentagonalJacobi
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

/-- The energy of a state S is:
  energy(S) = ∑_{p≥0, p∈S} (2p+1) - ∑_{p<0, p∉S} (2p+1)

In the tex source, levels are half-integers `q = p + 1/2`, and the formula is:
  energy(S) = ∑_{q>0, q∈S} 2q - ∑_{q<0, q∉S} 2q

Substituting q = p + 1/2:
- q > 0 ⟺ p ≥ 0
- 2q = 2(p + 1/2) = 2p + 1

For p ≥ 0: 2p + 1 = 2*p.natAbs + 1 (since p.natAbs = p for p ≥ 0)
For p < 0: -(2p + 1) = -2p - 1 = 2*|p| - 1 = 2*p.natAbs - 1 (since p.natAbs = -p for p < 0)

Thus energy is always a natural number. -/
noncomputable def energy (S : State) : ℕ :=
  (S.finite_nonneg.toFinset.sum fun p => 2 * p.natAbs + 1) +
  (S.finite_negative_missing.toFinset.sum fun p => 2 * p.natAbs - 1)

/-- The particle number of a state S is:
  parnum(S) = #{p ≥ 0 : p ∈ S} - #{p < 0 : p ∉ S}

In the tex source, this counts the number of positive half-integer levels in S
minus the number of negative half-integer levels not in S. -/
noncomputable def parnum (S : State) : ℤ :=
  S.finite_nonneg.toFinset.card - S.finite_negative_missing.toFinset.card

/-- The ℓ-ground state G_ℓ = {all levels < ℓ}.

In the half-integer convention, G_ℓ contains all half-integer levels q < ℓ.
In our integer representation (where level q = p + 1/2), this is {p : p < ℓ}.

For ℓ ≥ 0:
- Nonnegative integers in G_ℓ: {0, 1, ..., ℓ-1}
- No negative integers are missing from G_ℓ

For ℓ < 0:
- No nonnegative integers are in G_ℓ
- Negative integers missing from G_ℓ: {ℓ, ℓ+1, ..., -1} -/
def groundState (ell : ℤ) : State where
  levels := {p : Level | p < ell}
  finite_nonneg := by
    by_cases h : ell ≤ 0
    · convert Set.finite_empty
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hp
      linarith
    · push Not at h
      apply Set.Finite.subset (Set.finite_Ico 0 ell)
      intro p ⟨hp_nonneg, hp_lt⟩
      simp only [Set.mem_Ico]
      exact ⟨hp_nonneg, hp_lt⟩
  finite_negative_missing := by
    by_cases h : ell ≥ 0
    · convert Set.finite_empty
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hp
      push Not
      linarith
    · push Not at h
      apply Set.Finite.subset (Set.finite_Ico ell 0)
      intro p ⟨hp_neg, hp_ge⟩
      simp only [Set.mem_Ico, Set.mem_ofPred_eq] at hp_ge ⊢
      push Not at hp_ge
      exact ⟨hp_ge, hp_neg⟩

/-- Jump operation: if p ∈ S and p + q ∉ S, then jump_{p,q}(S) = (S \ {p}) ∪ {p + q}. -/
def jump (S : State) (p : Level) (q : ℕ) (_hp : p ∈ S.levels)
    (_hpq : p + q ∉ S.levels) (_hq : q > 0) : State where
  levels := (S.levels \ {p}) ∪ {p + q}
  finite_nonneg := by
    apply Set.Finite.subset
    · exact S.finite_nonneg.union (Set.finite_singleton (p + q))
    · intro x ⟨hx_nonneg, hx_mem⟩
      simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx_mem ⊢
      cases hx_mem with
      | inl h => left; exact ⟨hx_nonneg, h.1⟩
      | inr h => right; exact h
  finite_negative_missing := by
    apply Set.Finite.subset
    · exact S.finite_negative_missing.union (Set.finite_singleton p)
    · intro x ⟨hx_neg, hx_nmem⟩
      simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff] at hx_nmem ⊢
      by_cases hxp : x = p
      · right; exact hxp
      · left
        constructor
        · exact hx_neg
        · intro hx_in_S
          apply hx_nmem
          left
          exact ⟨hx_in_S, hxp⟩

end State
end Jacobi
end AlgebraicCombinatorics
